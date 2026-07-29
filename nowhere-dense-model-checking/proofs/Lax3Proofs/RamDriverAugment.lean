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

/-- A walk that contributes less at every slot accumulates less. -/
theorem rowAcc_mono {off tgt : ℕ → ℕ} {fs gs : ℕ → Finset ℕ} (h : ∀ z, fs z ⊆ gs z)
    (v : ℕ) : rowAcc off tgt fs v ⊆ rowAcc off tgt gs v := by
  intro y hy
  obtain ⟨s, h₁, h₂, h₃⟩ := mem_rowAcc.1 hy
  exact mem_rowAcc.2 ⟨s, h₁, h₂, h _ h₃⟩

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

/-- The relation is about one array, so it transports along any state
that agrees on it. -/
theorem Marks.of_eq {s : String} {n b : ℕ} {S : Finset ℕ} {g : ℕ → ℕ} {τ τ' : Env}
    (h : Marks s n b S g τ) (he : τ'.arrs s = τ.arrs s) : Marks s n b S g τ' := by
  obtain ⟨g', hg', hk⟩ := h
  exact ⟨g', he.trans hg', hk⟩

theorem Marks.setVar {s : String} {n b : ℕ} {S : Finset ℕ} {g : ℕ → ℕ} {τ : Env}
    (h : Marks s n b S g τ) (y : String) (x : ℕ) : Marks s n b S g (τ.setVar y x) :=
  h.of_eq (by rw [arrs_setVar])

theorem Marks.setArr_of_ne {s a : String} {n b : ℕ} {S : Finset ℕ} {g : ℕ → ℕ} {τ : Env}
    (h : Marks s n b S g τ) (ha : a ≠ s) (p x : ℕ) : Marks s n b S g (τ.setArr a p x) :=
  h.of_eq (by rw [arrs_setArr, if_neg (Ne.symm ha)])

/-- A stamp array that is zero everywhere holds no marks at all — the
state every stamped walk of the round starts and ends in. -/
theorem Marks.zero {s : String} {n b : ℕ} {g : ℕ → ℕ} {τ : Env}
    (h : ∃ g', τ.arrs s = arrOf n g' ∧ ∀ k < n, g' k = g k) :
    Marks s n b (∅ : Finset ℕ) g τ := by
  obtain ⟨g', hg', hk⟩ := h
  exact ⟨g', hg', fun k hkn => by rw [hk k hkn]; simp⟩

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
    {Acc : Finset ℕ → Env → Prop} {S M Cap : Finset ℕ} {τ : Env} {z : ℕ}
    (ha₁ : a₁ ≠ sd) (ha₂ : a₂ ≠ sd) (hB1 : 1 < B) (hnB : n < B)
    (hAccSt : ∀ S τ p x, Acc S τ → Acc S (τ.setArr sd p x))
    (hAcc : Emits B n Ka a₁ a₂ act Cap Acc)
    (hm : Marks sd n 1 M (fun _ => 0) τ) (hA : Acc S τ)
    (hu : τ.vars "u" = z) (hzn : z < n) (hz : z ∉ S) (hzc : z ∈ Cap) :
    ∃ τ' K, Run B (.seq (.store sd (.var "u") (.lit 1)) act) τ τ' K ∧ K ≤ Ka + 3 ∧
      Marks sd n 1 (insert z M) (fun _ => 0) τ' ∧ Acc (insert z S) τ' ∧
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
  have hm₁ : Marks sd n 1 (insert z M) (fun _ => 0) (τ.setArr sd z 1) := by
    refine ⟨fun k => if k = z then 1 else g k, by rw [arrs_setArr, if_pos rfl, hg, set_arrOf],
      fun k hk => ?_⟩
    simp only []
    by_cases hkz : k = z
    · rw [if_pos hkz, if_pos (by simp [hkz])]
    · rw [if_neg hkz, hgk k hk]
      by_cases hkb : k ∈ M
      · rw [if_pos hkb, if_pos (Finset.mem_insert_of_mem hkb)]
      · rw [if_neg hkb, if_neg (by
          intro hc
          rcases Finset.mem_insert.1 hc with h | h
          · exact hkz h
          · exact hkb h)]
  obtain ⟨g₁, hg₁, hgk₁⟩ := hm₁
  obtain ⟨τ', K, hr, hK, hA', hj', hfa⟩ :=
    hAcc S (τ.setArr sd z 1) z (hAccSt S τ z 1 hA) (by rw [vars_setArr]; exact hu) hzn
      hz hzc
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
      emitBranch_run (sd := "stf") (M := ({i} : Finset ℕ) ∪ S) ha₁ ha₂ hB1 hnB hAccSt hAcc
        ⟨g, hg, hgk⟩ hA hu hzn (fun hc => hin (Finset.mem_union_right _ hc))
        (hfe (by simp only [if_neg hzi]; exact Finset.mem_singleton_self z))
    have hset : S ∪ (if z = i then (∅ : Finset ℕ) else {z}) = insert z S := by
      rw [if_neg hzi, Finset.union_singleton]
    refine ⟨τ', _, Run.ite_true (by rw [econd, hgz0]; rfl) hr, ?_, ?_, hfv⟩
    · simp only [size_condEq, size_get, size_var, size_lit]; omega
    · simp only [hset]
      exact ⟨hm'.congr (Finset.union_insert _ _ _).symm, hA'⟩

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
first clause of `RamAugment.NewArc` — or it has been emitted.

The accounting is carried at `Base ∪ S`, `Base` being what an earlier
list of the same turn already emitted and the stamp `ste` never saw:
the assembly's first list is the old in-block, which the stamp `sta`
excludes on its own, so `Base ⊆ A` is exactly what says the guard
cannot meet it twice. -/
theorem guardAsmIn_of_emits {B n Ka : ℕ} {a₁ a₂ : String} {act : Com}
    {Acc : Finset ℕ → Env → Prop} {A Base Cap : Finset ℕ}
    (ha₁ : a₁ ≠ "ste") (ha₂ : a₂ ≠ "ste") (hb₁ : a₁ ≠ "sta") (hb₂ : a₂ ≠ "sta")
    (hB1 : 1 < B) (hnB : n < B) (hBA : Base ⊆ A)
    (hAccSt : ∀ S τ p x, Acc S τ → Acc S (τ.setArr "ste" p x))
    (hAcc : Emits B n Ka a₁ a₂ act Cap Acc) :
    Guarded B n (Ka + 13)
      (.ite (.eq (.get "sta" (.var "u")) (.lit 0))
        (.ite (.eq (.get "ste" (.var "u")) (.lit 0))
          (.seq (.store "ste" (.var "u") (.lit 1)) act) .skip)
        .skip)
      (fun z => if z ∈ A then ∅ else {z}) Cap
      (fun S τ => Marks "ste" n 1 S (fun _ => 0) τ ∧
        Marks "sta" n 1 A (fun _ => 0) τ ∧ Acc (Base ∪ S) τ) := by
  classical
  rintro S τ z ⟨hme, hma, hA⟩ hu hzn hfe
  have ea := stampCond hma hu hzn hB1 hnB
  have ee := stampCond hme hu hzn hB1 hnB
  by_cases hzA : z ∈ A
  · refine ⟨τ, _, Run.ite_false (by rw [ea]; simp [hzA]) Run.skip, ?_, ?_, fun y _ => rfl⟩
    · simp only [size_condEq, size_get, size_var, size_lit]; omega
    · simp only [if_pos hzA, Finset.union_empty]
      exact ⟨hme, hma, hA⟩
  · have hzB : z ∉ Base := fun hc => hzA (hBA hc)
    by_cases hzS : z ∈ S
    · refine ⟨τ, _, Run.ite_true (by rw [ea]; simp [hzA])
        (Run.ite_false (by rw [ee]; simp [hzS]) Run.skip), ?_, ?_, fun y _ => rfl⟩
      · simp only [size_condEq, size_get, size_var, size_lit]; omega
      · simp only [if_neg hzA, Finset.union_singleton, Finset.insert_eq_self.2 hzS]
        exact ⟨hme, hma, hA⟩
    · obtain ⟨τ', K, hr, hK, hm', hA', hfv, hfr⟩ :=
        emitBranch_run (sd := "ste") (M := S) ha₁ ha₂ hB1 hnB hAccSt hAcc hme hA hu hzn
          (by rintro hc; rcases Finset.mem_union.1 hc with h | h; exacts [hzB h, hzS h])
          (hfe (by simp only [if_neg hzA]; exact Finset.mem_singleton_self z))
      refine ⟨τ', _, Run.ite_true (by rw [ea]; simp [hzA])
        (Run.ite_true (by rw [ee]; simp [hzS]) hr), ?_, ?_, hfv⟩
      · simp only [size_condEq, size_get, size_var, size_lit]; omega
      · simp only [if_neg hzA, Finset.union_singleton]
        obtain ⟨ga, hga, hgak⟩ := hma
        exact ⟨hm', ⟨ga, by
          rw [hfr "sta" (Ne.symm hb₁) (Ne.symm hb₂) (by decide)]; exact hga, hgak⟩,
          by rw [Finset.union_insert]; exact hA'⟩

/-- **The transitive candidates' guard.** The pair must not be one `D`
already carries, the candidate must not have been emitted, and if the
current vertex is demanded an arc *back* — which is what the stamp
`std` holds — the ranking decides. That is
`RamAugment.NewArc` read off three array cells and one comparison. -/
theorem guardAsmTrans_of_emits {B n Ka i : ℕ} {a₁ a₂ : String} {act : Com}
    {Acc : Finset ℕ → Env → Prop} {A Dm Base Cap : Finset ℕ} {R : ℕ → ℕ}
    (ha₁ : a₁ ≠ "ste") (ha₂ : a₂ ≠ "ste") (hb₁ : a₁ ≠ "sta") (hb₂ : a₂ ≠ "sta")
    (hc₁ : a₁ ≠ "std") (hc₂ : a₂ ≠ "std") (hd₁ : a₁ ≠ "rnk") (hd₂ : a₂ ≠ "rnk")
    (hB1 : 1 < B) (hnB : n < B) (hin : i < n) (hR : ∀ v, v < n → R v < n) (hBA : Base ⊆ A)
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
        Marks "std" n 1 Dm (fun _ => 0) τ ∧ τ.arrs "rnk" = arrOf n R ∧
        Acc (Base ∪ S) τ) := by
  classical
  rintro S τ z ⟨hme, hma, hmd, hrnk, hA⟩ hu hzn hfe
  have ea := stampCond hma hu hzn hB1 hnB
  have ee := stampCond hme hu hzn hB1 hnB
  have ed := stampCond hmd hu hzn hB1 hnB
  have eu : (Expr.var "u").evalB B τ = some z := by
    have h := evalB_var (B := B) (x := "u") (σ := τ) (by rw [hu]; omega)
    rwa [hu] at h
  have hiv : τ.vars "i" = i := hAccI _ τ hA
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
  · have hzB : z ∉ Base := fun hc => hzA (hBA hc)
    by_cases hzS : z ∈ S
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
            Marks "ste" n 1 (insert z S) (fun _ => 0) τ' ∧ Acc (Base ∪ insert z S) τ' ∧
            (∀ y, y ≠ "c" → τ'.vars y = τ.vars y) ∧
            Marks "sta" n 1 A (fun _ => 0) τ' ∧ Marks "std" n 1 Dm (fun _ => 0) τ' ∧
            τ'.arrs "rnk" = arrOf n R := by
        intro hzc
        obtain ⟨τ', K, hr, hK, hm', hA', hfv, hfr⟩ :=
          emitBranch_run (sd := "ste") (M := S) ha₁ ha₂ hB1 hnB hAccSt hAcc hme hA hu hzn
            (by rintro hc; rcases Finset.mem_union.1 hc with h | h; exacts [hzB h, hzS h]) hzc
        obtain ⟨hma', hmd', hrnk'⟩ := hkeep τ' hfr
        exact ⟨τ', K, hr, hK, hm', by rw [Finset.union_insert]; exact hA', hfv,
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
    (htn2 : ∀ z, z < nv2 → ∀ q, q < off2 (z + 1) → tgt2 q < n)
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
            (hB2 _ hznv) (by simp) ht2 (htn2 _ hznv)
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
def FillAcc (ta fa : String) (n len i base : ℕ) (T F : ℕ → ℕ) (Cap : Finset ℕ)
    (S : Finset ℕ) (τ : Env) : Prop :=
  τ.vars "i" = i ∧ S ⊆ Cap ∧
  (∃ f, τ.arrs fa = arrOf n f ∧ f i = base + S.card ∧ ∀ k, k ≠ i → f k = F k) ∧
  (∃ g, τ.arrs ta = arrOf len g ∧
    (∀ q, base ≤ q → q < base + S.card → g q ∈ S) ∧
    (∀ z, z ∈ S → ∃ q, base ≤ q ∧ q < base + S.card ∧ g q = z) ∧
    (∀ q, (q < base ∨ base + S.card ≤ q) → g q = T q))

theorem FillAcc.setArr {ta fa : String} {n len i base : ℕ} {T F : ℕ → ℕ}
    {Cap S : Finset ℕ} {τ : Env} (h : FillAcc ta fa n len i base T F Cap S τ) {a : String}
    (hta : a ≠ ta) (hfa : a ≠ fa) (p x : ℕ) :
    FillAcc ta fa n len i base T F Cap S (τ.setArr a p x) := by
  obtain ⟨hi, hsub, ⟨f, hf, hfi, hfk⟩, ⟨g, hg, h₁, h₂, h₃⟩⟩ := h
  exact ⟨by rw [vars_setArr]; exact hi, hsub,
    ⟨f, by rw [arrs_setArr, if_neg (Ne.symm hfa)]; exact hf, hfi, hfk⟩,
    ⟨g, by rw [arrs_setArr, if_neg (Ne.symm hta)]; exact hg, h₁, h₂, h₃⟩⟩

theorem FillAcc.setVar {ta fa : String} {n len i base : ℕ} {T F : ℕ → ℕ}
    {Cap S : Finset ℕ} {τ : Env} (h : FillAcc ta fa n len i base T F Cap S τ) {y : String}
    (hy : y ≠ "i") (x : ℕ) : FillAcc ta fa n len i base T F Cap S (τ.setVar y x) := by
  obtain ⟨hi, hsub, ⟨f, hf, hfi, hfk⟩, ⟨g, hg, h₁, h₂, h₃⟩⟩ := h
  exact ⟨by rw [vars_setVar, if_neg (Ne.symm hy)]; exact hi, hsub,
    ⟨f, by rw [arrs_setVar]; exact hf, hfi, hfk⟩,
    ⟨g, by rw [arrs_setVar]; exact hg, h₁, h₂, h₃⟩⟩

/-- **The fill action.** -/
theorem fillAcc_emits {B n len i base : ℕ} {ta fa : String} {T F : ℕ → ℕ}
    {Cap : Finset ℕ} (htf : ta ≠ fa) (hin : i < n) (hnB : n < B) (hlenB : len < B)
    (hcap : base + Cap.card ≤ len) :
    Emits B n 10 ta fa
      (.seq (.store ta (.get fa (.var "i")) (.var "u"))
        (.store fa (.var "i") (.add (.get fa (.var "i")) (.lit 1))))
      Cap (FillAcc ta fa n len i base T F Cap) := by
  classical
  rintro S τ z ⟨hi, hsub, ⟨f, hf, hfi, hfk⟩, ⟨g, hg, h₁, h₂, h₃⟩⟩ hu hzn hzS hzc
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
      by simp only []; rw [if_true, hcards]; omega,
      fun k hk => by simp only []; rw [if_neg hk]; exact hfk k hk⟩,
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

/-! ### The out-blocks, read as sets

The assembly's two stamps are unions of in- and out-blocks, so what the
counting sort left has to be read back at the set level once more: the
row of `i` in the out-block structure is the vertices `i` points at,
and the nested row is the vertices `i` demands an arc to. -/

theorem adjSet_eq {n : ℕ} (D : Orientation n) (v : Fin n) :
    RamAugment.adjSet D v = D.inN v ∪ RamAugment.outSet D v := rfl

theorem demandOut_eq {n : ℕ} (D : Orientation n) (v : Fin n) :
    RamAugment.demandOut D v = (RamAugment.outSet D v).biUnion (fun w => D.inN w) ∪
      (RamAugment.outSet D v).biUnion (fun w => RamAugment.outSet D w) := rfl

section OutBlocks

variable {n W m : ℕ} {D : Orientation n} {DO DT OO OT : ℕ → ℕ} {σ : Env}

/-- **A row of the out-blocks names the vertices the row's owner points
at.** -/
theorem rowTgt_out_eq (hcsr : InCsr D m DO DT) (hbl : Blocks "ooff" "otg" n W m OO OT σ)
    (hsnd : ∀ u < n, ∀ q, OO u ≤ q → q < OO (u + 1) → Pts DO DT (OT q) u)
    (hcmp : ∀ u < n, ∀ z < n, Pts DO DT z u → ∃ q, OO u ≤ q ∧ q < OO (u + 1) ∧ OT q = z)
    {i : ℕ} (hi : i < n) : rowTgt OO OT i = valSet (RamAugment.outSet D ⟨i, hi⟩) := by
  ext y
  rw [mem_rowTgt, mem_valSet]
  constructor
  · rintro ⟨q, h₁, h₂, h₃⟩
    have hqm : q < m := lt_of_lt_of_le h₂ (hbl.off_le (by omega))
    have hyn : y < n := h₃ ▸ hbl.target_lt q hqm
    refine ⟨hyn, ?_⟩
    have hp : Pts DO DT y i := h₃ ▸ hsnd i hi q h₁ h₂
    exact (pts_iff_mem_outSet hcsr hyn hi).1 hp
  · rintro ⟨hyn, hmem⟩
    exact hcmp i hi y hyn ((pts_iff_mem_outSet hcsr hyn hi).2 hmem)

/-- **The stamp `sta`**: the in-block and the out-block of `i` are the
vertices `D` makes `i` adjacent to, which is `RamAugment.mem_adjSet`. -/
theorem adjRow_eq (hcsr : InCsr D m DO DT) (hbl : Blocks "ooff" "otg" n W m OO OT σ)
    (hsnd : ∀ u < n, ∀ q, OO u ≤ q → q < OO (u + 1) → Pts DO DT (OT q) u)
    (hcmp : ∀ u < n, ∀ z < n, Pts DO DT z u → ∃ q, OO u ≤ q ∧ q < OO (u + 1) ∧ OT q = z)
    {i : ℕ} (hi : i < n) :
    rowTgt DO DT i ∪ rowTgt OO OT i = valSet (RamAugment.adjSet D ⟨i, hi⟩) := by
  rw [rowTgt_eq_inN hcsr hi, rowTgt_out_eq hcsr hbl hsnd hcmp hi, adjSet_eq, valSet_union]

/-- **The stamp `std`**: the in-blocks and the out-blocks of the
vertices `i` points at are the vertices `i` demands an arc to, which is
`RamAugment.mem_demandOut`. -/
theorem demandRow_eq (hcsr : InCsr D m DO DT) (hbl : Blocks "ooff" "otg" n W m OO OT σ)
    (hsnd : ∀ u < n, ∀ q, OO u ≤ q → q < OO (u + 1) → Pts DO DT (OT q) u)
    (hcmp : ∀ u < n, ∀ z < n, Pts DO DT z u → ∃ q, OO u ≤ q ∧ q < OO (u + 1) ∧ OT q = z)
    {i : ℕ} (hi : i < n) :
    rowAcc OO OT (fun w => rowTgt DO DT w ∪ rowTgt OO OT w) i
      = valSet (RamAugment.demandOut D ⟨i, hi⟩) := by
  classical
  ext y
  rw [mem_rowAcc, mem_valSet, demandOut_eq]
  constructor
  · rintro ⟨p, h₁, h₂, hy⟩
    have hpm : p < m := lt_of_lt_of_le h₂ (hbl.off_le (by omega))
    have hwn : OT p < n := hbl.target_lt p hpm
    have hw : (⟨OT p, hwn⟩ : Fin n) ∈ RamAugment.outSet D ⟨i, hi⟩ :=
      (pts_iff_mem_outSet hcsr hwn hi).1 (hsnd i hi p h₁ h₂)
    rcases Finset.mem_union.1 hy with hy | hy
    · rw [rowTgt_eq_inN hcsr hwn, mem_valSet] at hy
      obtain ⟨hyn, hym⟩ := hy
      exact ⟨hyn, Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨⟨OT p, hwn⟩, hw, hym⟩)⟩
    · rw [rowTgt_out_eq hcsr hbl hsnd hcmp hwn, mem_valSet] at hy
      obtain ⟨hyn, hym⟩ := hy
      exact ⟨hyn, Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨⟨OT p, hwn⟩, hw, hym⟩)⟩
  · rintro ⟨hyn, hmem⟩
    rcases Finset.mem_union.1 hmem with hm | hm
    · obtain ⟨w, hw, hyw⟩ := Finset.mem_biUnion.1 hm
      obtain ⟨p, h₁, h₂, h₃⟩ :=
        hcmp i hi (w : ℕ) w.isLt ((pts_iff_mem_outSet hcsr w.isLt hi).2 hw)
      refine ⟨p, h₁, h₂, Finset.mem_union_left _ ?_⟩
      rw [h₃, rowTgt_eq_inN hcsr w.isLt]
      exact mem_valSet.2 ⟨hyn, by simpa using hyw⟩
    · obtain ⟨w, hw, hyw⟩ := Finset.mem_biUnion.1 hm
      obtain ⟨p, h₁, h₂, h₃⟩ :=
        hcmp i hi (w : ℕ) w.isLt ((pts_iff_mem_outSet hcsr w.isLt hi).2 hw)
      refine ⟨p, h₁, h₂, Finset.mem_union_right _ ?_⟩
      rw [h₃, rowTgt_out_eq hcsr hbl hsnd hcmp w.isLt]
      exact mem_valSet.2 ⟨hyn, by simpa using hyw⟩

/-- **A row of an `InCsr` names each in-neighbour once.** The slots of
the block map onto the in-neighbours, and the block is exactly as long
as there are of them, so the map is injective. This is what the
fraternity build's `CsrSimple` output needs of the assembly's input,
and what makes the assembly's first list — the old in-block — carry no
duplicate. -/
theorem incsr_nodup (h : InCsr D m DO DT) {w : ℕ} (hw : w < n) {j₁ j₂ : ℕ}
    (h₁ : DO w ≤ j₁) (h₂ : j₁ < DO (w + 1)) (h₃ : DO w ≤ j₂) (h₄ : j₂ < DO (w + 1))
    (he : DT j₁ = DT j₂) : j₁ = j₂ := by
  classical
  set S := Finset.Ico (DO w) (DO (w + 1)) with hS
  have hslot : ∀ j ∈ S, DT j < n := by
    intro j hj
    rw [hS, Finset.mem_Ico] at hj
    exact h.target_lt j (lt_of_lt_of_le hj.2 (incsr_le h (by omega)))
  have himg : S.image DT = valSet (D.inN ⟨w, hw⟩) := by
    ext y
    rw [Finset.mem_image, mem_valSet]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [hS, Finset.mem_Ico] at hj
      exact ⟨hslot j (by rw [hS, Finset.mem_Ico]; exact hj),
        (h.mem_iff ⟨w, hw⟩ ⟨DT j, hslot j (by rw [hS, Finset.mem_Ico]; exact hj)⟩).2
          ⟨j, hj.1, hj.2, rfl⟩⟩
    · rintro ⟨hyn, hym⟩
      obtain ⟨j, hj₁, hj₂, hj₃⟩ := (h.mem_iff ⟨w, hw⟩ ⟨y, hyn⟩).1 hym
      exact ⟨j, by rw [hS, Finset.mem_Ico]; exact ⟨hj₁, hj₂⟩, hj₃⟩
  have hcard : (S.image DT).card = S.card := by
    rw [himg, card_valSet, hS, Nat.card_Ico, h.len ⟨w, hw⟩]
  have := Finset.injOn_of_card_image_eq hcard
  exact this (by simp only [hS, Finset.coe_Ico, Set.mem_Ico]; exact ⟨h₁, h₂⟩)
    (by simp only [hS, Finset.coe_Ico, Set.mem_Ico]; exact ⟨h₃, h₄⟩) he

/-- The arcs are as many as the in-degrees allow. This is what puts the
nested walks' cost — a per-slot charge times an in-block — inside the
width. -/
theorem arcs_le (h : InCsr D m DO DT) {d : ℕ} (hd : D.InDegLE d) : m ≤ n * d := by
  rw [← sum_card_inN h]
  calc ∑ v : Fin n, (D.inN v).card ≤ ∑ _v : Fin n, d := Finset.sum_le_sum fun v _ => hd v
    _ = n * d := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end OutBlocks

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

-- **the stamp `sta`**: the in-block and the out-block of `i`, which is what
-- `D` makes `i` adjacent to — `1 2 | 0 2 | 0 1 3 | 2`
#guard (List.range 4).map (fun i =>
    (rowTgt demoDO demoDT i ∪ rowTgt demoOO demoOT i).sort (· ≤ ·))
  = [[1, 2], [0, 2], [0, 1, 3], [2]]

/-- The vertices `i` demands an arc to: the in-blocks and the
out-blocks of the vertices `i` points at. -/
def demoDem (i : ℕ) : Finset ℕ :=
  rowAcc demoOO demoOT (fun w => rowTgt demoDO demoDT w ∪ rowTgt demoOO demoOT w) i

-- **the stamp `std`** — vertex `0` demands everything, `3` demands nothing
#guard (List.range 4).map (fun i => (demoDem i).sort (· ≤ ·))
  = [[0, 1, 2, 3], [0, 1, 3], [2], []]

-- the *raw* fraternity enumeration, the stamp erased: the guarded walk's set
-- `1 | 0 | | ` sits inside it, which is what makes the clearing walk clear
-- every cell the counting walk set
#guard (List.range 4).map (fun i =>
    (rowAcc demoOO demoOT (fun w => rowTgt demoDO demoDT w) i).sort (· ≤ ·))
  = [[0, 1], [0, 1], [2], []]

-- **the transitive enumeration, guarded** by the two stamps and the ranking
-- `0, 1, 2, 3` the round reports: `0 → 2` is discarded because `D` carries it,
-- and what is left is the two arcs `0 → 3`, `1 → 3` the round's example names
#guard (List.range 4).map (fun i =>
    (rowAcc demoDO demoDT (fun w => rowAcc demoDO demoDT
      (fun y => if y ∈ rowTgt demoDO demoDT i ∪ rowTgt demoOO demoOT i then ∅
        else if y ∈ demoDem i ∧ ¬ y < i then ∅ else {y}) w) i).sort (· ≤ ·))
  = [[], [], [], [0, 1]]

end Demo

/-! ### The fraternity build

`RamAugment.fratCount` and `RamAugment.fratFill` are the same walk
twice over: the stamp of `i` is set, the nested enumeration runs under
the guard, the same enumeration runs again clearing every stamp it set,
and the stamp of `i` is cleared. What differs is only what the guard
fires — a counter or a fill pointer — so the two lemmas below serve
both passes, at two `Emits`. -/

/-- The eleven arrays the round's walks read. An accounting whose
action writes neither of its own two among them crosses a walk
untouched, which is what `Emits.and` asks of it. -/
def ReadArrs (a : String) : Prop :=
  a ≠ "doff" ∧ a ≠ "dtg" ∧ a ≠ "ooff" ∧ a ≠ "otg" ∧ a ≠ "stf" ∧ a ≠ "sta" ∧
    a ≠ "std" ∧ a ≠ "ste" ∧ a ≠ "rnk" ∧ a ≠ "ioff" ∧ a ≠ "itg"

/-- The five names the round's own actions write, none of them read by
a walk. `"@"` is the counting action's placeholder: it writes no array
at all. -/
theorem readArrs_at : ReadArrs "@" :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem readArrs_tgt : ReadArrs "tgt" :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem readArrs_ffl : ReadArrs "ffl" :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem readArrs_ntg : ReadArrs "ntg" :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem readArrs_nfl : ReadArrs "nfl" :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-- The four arrays and the one scalar a nested walk of the round
reads, which every accounting has to carry across it. -/
def NestArr (n W : ℕ) (DO DT OO OT : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "n" = n ∧ τ.arrs "doff" = arrOf (n + 1) DO ∧ τ.arrs "dtg" = arrOf W DT ∧
    τ.arrs "ooff" = arrOf (n + 1) OO ∧ τ.arrs "otg" = arrOf W OT

namespace NestArr

variable {n W : ℕ} {DO DT OO OT : ℕ → ℕ} {τ τ' : Env}

theorem setVar (h : NestArr n W DO DT OO OT τ) (y : String) (hy : y ≠ "n") (x : ℕ) :
    NestArr n W DO DT OO OT (τ.setVar y x) :=
  ⟨by rw [vars_setVar, if_neg (Ne.symm hy)]; exact h.1, by simpa using h.2.1,
    by simpa using h.2.2.1, by simpa using h.2.2.2.1, by simpa using h.2.2.2.2⟩

theorem setArr (h : NestArr n W DO DT OO OT τ) {a : String} (h1 : a ≠ "doff")
    (h2 : a ≠ "dtg") (h3 : a ≠ "ooff") (h4 : a ≠ "otg") (p x : ℕ) :
    NestArr n W DO DT OO OT (τ.setArr a p x) :=
  ⟨by rw [vars_setArr]; exact h.1,
    by rw [arrs_setArr, if_neg (Ne.symm h1)]; exact h.2.1,
    by rw [arrs_setArr, if_neg (Ne.symm h2)]; exact h.2.2.1,
    by rw [arrs_setArr, if_neg (Ne.symm h3)]; exact h.2.2.2.1,
    by rw [arrs_setArr, if_neg (Ne.symm h4)]; exact h.2.2.2.2⟩

/-- The relation crosses any command that leaves the four arrays and
the scalar `"n"` alone — which every accounting's action does. -/
theorem of_frame {a₁ a₂ : String} (h : NestArr n W DO DT OO OT τ)
    (ha₁ : ReadArrs a₁) (ha₂ : ReadArrs a₂)
    (hv : ∀ y, y ≠ "c" → τ'.vars y = τ.vars y)
    (hfa : ∀ a, a ≠ a₁ → a ≠ a₂ → τ'.arrs a = τ.arrs a) : NestArr n W DO DT OO OT τ' :=
  ⟨by rw [hv "n" (by decide)]; exact h.1,
    by rw [hfa "doff" (Ne.symm ha₁.1) (Ne.symm ha₂.1)]; exact h.2.1,
    by rw [hfa "dtg" (Ne.symm ha₁.2.1) (Ne.symm ha₂.2.1)]; exact h.2.2.1,
    by rw [hfa "ooff" (Ne.symm ha₁.2.2.1) (Ne.symm ha₂.2.2.1)]; exact h.2.2.2.1,
    by rw [hfa "otg" (Ne.symm ha₁.2.2.2.1) (Ne.symm ha₂.2.2.2.1)]; exact h.2.2.2.2⟩

end NestArr

/-- The guard the fraternity build runs at every candidate: emit unless
the stamp is set. -/
def fratGuard (act : Com) : Com :=
  .ite (.eq (.get "stf" (.var "u")) (.lit 0))
    (.seq (.store "stf" (.var "u") (.lit 1)) act) .skip

section FratPass

variable {B n d W m Ka : ℕ} {a₁ a₂ : String} {act : Com} {D : Orientation n}
variable {DO DT OO OT : ℕ → ℕ} {Acc : Finset ℕ → Env → Prop} {Cap : Finset ℕ}
variable {i : ℕ} {σ : Env}

/-- **The fraternity walk, guarded.** The out-block of `i` is scanned,
the in-block of every vertex it names inside it, and every candidate
whose stamp is clear is stamped and handed to the action — so what
reaches the action is `RamAugment.fratNbrs D i`, once each, by
`fratRow_eq`. -/
theorem fratEmit_run
    (ha₁ : ReadArrs a₁) (ha₂ : ReadArrs a₂)
    (hB1 : 1 < B) (hnB : n < B) (hmB : m < B) (hi : i < n)
    (hcsr : InCsr D m DO DT) (hdeg : D.InDegLE d) (hmW : m ≤ W)
    (hbo : Blocks "ooff" "otg" n W m OO OT σ)
    (hsnd : ∀ u < n, ∀ q, OO u ≤ q → q < OO (u + 1) → Pts DO DT (OT q) u)
    (hcmp : ∀ u < n, ∀ z < n, Pts DO DT z u → ∃ q, OO u ≤ q ∧ q < OO (u + 1) ∧ OT q = z)
    (hiv : σ.vars "i" = i) (harr : NestArr n W DO DT OO OT σ)
    (hstf : Marks "stf" n 1 ({i} : Finset ℕ) (fun _ => 0) σ)
    (hAccSt : ∀ S τ p x, Acc S τ → Acc S (τ.setArr "stf" p x))
    (hAccV : ∀ S τ (y : String) (z : ℕ),
      (y = "j" ∨ y = "jend" ∨ y = "w" ∨ y = "q" ∨ y = "qe" ∨ y = "u") → Acc S τ →
      Acc S (τ.setVar y z))
    (hAcc : Emits B n Ka a₁ a₂ act Cap Acc)
    (hCap : valSet (RamAugment.fratNbrs D ⟨i, hi⟩) ⊆ Cap) (hA0 : Acc ∅ σ) :
    ∃ σ' K, Run B (RamAugment.fratScan (fratGuard act)) σ σ' K ∧
      K ≤ ((Ka + 19) * d + 23) * (OO (i + 1) - OO i) + 12 ∧
      Marks "stf" n 1 ({i} ∪ valSet (RamAugment.fratNbrs D ⟨i, hi⟩)) (fun _ => 0) σ' ∧
      Acc (valSet (RamAugment.fratNbrs D ⟨i, hi⟩)) σ' ∧ NestArr n W DO DT OO OT σ' ∧
      (∀ y, y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" → y ≠ "u" → y ≠ "c" →
        σ'.vars y = σ.vars y) := by
  classical
  have hDle : ∀ z, z < n → DO (z + 1) ≤ m := fun z hz => incsr_le hcsr (by omega)
  have hOle : ∀ z, z < n → OO (z + 1) ≤ m := fun z hz => hbo.off_le (by omega)
  have hrow : rowAcc OO OT (fun w => rowAcc DO DT (fun y => if y = i then ∅ else {y}) w) i
      = valSet (RamAugment.fratNbrs D ⟨i, hi⟩) :=
    fratRow_eq hcsr hOle (fun q hq => hbo.target_lt q hq) hi (hsnd i hi)
      (fun z hz hp => hcmp i hi z hz hp)
  have hsub : rowAcc OO OT (fun w => rowAcc DO DT (fun y => if y = i then ∅ else {y}) w) i
      ⊆ Cap := by rw [hrow]; exact hCap
  have hAccP : Emits B n Ka a₁ a₂ act Cap
      (fun S τ => Acc S τ ∧ NestArr n W DO DT OO OT τ) :=
    hAcc.and (fun _ _ hP hv hfa => hP.of_frame ha₁ ha₂ hv hfa)
  have hg := guardFrat_of_emits (B := B) (n := n) (Ka := Ka) (i := i) (act := act)
      (Cap := Cap) (Acc := fun S τ => Acc S τ ∧ NestArr n W DO DT OO OT τ)
      ha₁.2.2.2.2.1 ha₂.2.2.2.2.1 hB1 hnB
      (fun S τ p x h => ⟨hAccSt S τ p x h.1,
        h.2.setArr (by decide) (by decide) (by decide) (by decide) p x⟩)
      hAccP
  obtain ⟨σ', K, hrun, hK, hJ, hfv⟩ :=
    emitNest_run (B := B) (o := "ooff") (t := "otg") (o2 := "doff") (t2 := "dtg")
      (grd := fratGuard act) (n := n) (nv := n) (len := W) (nv2 := n) (len2 := W)
      (v := i) (Kg := Ka + 8) (dd := d) (off := OO) (tgt := OT) (off2 := DO) (tgt2 := DT)
      (fe := fun y => if y = i then ∅ else {y})
      (J := fun S τ => Marks "stf" n 1 ({i} ∪ S) (fun _ => 0) τ ∧
        (Acc S τ ∧ NestArr n W DO DT OO OT τ))
      (E₀ := ∅) (Cap := Cap) (σ := σ)
      hB1 hnB hi (by omega) harr.2.2.2.1 (hbo.mono i hi)
      (le_trans (hOle i hi) hmW) (by have := hOle i hi; omega) hiv
      (fun _ _ h => h.2.2.2.2.2.2)
      (fun p hp => hbo.target_lt p (by have := hOle i hi; omega))
      le_rfl (fun _ _ h => h.2.2.2.1) (fun _ _ h => h.2.2.2.2.1)
      (fun z hz => hcsr.mono z hz) (fun z hz => le_trans (hDle z hz) hmW)
      (fun z hz => by have := hDle z hz; omega)
      (fun z hz q hq => hcsr.target_lt q (lt_of_lt_of_le hq (hDle z hz)))
      (fun z hz => by
        have h : DO (z + 1) - DO z = (D.inN ⟨z, hz⟩).card := hcsr.len ⟨z, hz⟩
        rw [h]; exact hdeg ⟨z, hz⟩)
      (fun S τ y z hy h => ⟨h.1.setVar y z, hAccV S τ y z hy h.2.1,
        h.2.2.setVar y (by rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) z⟩)
      (fun p h₁ h₂ => Finset.Subset.trans (subset_rowAcc h₁ h₂) hsub)
      hg ⟨hstf.congr (Finset.union_empty _).symm, hA0, harr⟩
  rw [Finset.empty_union, hrow] at hJ
  exact ⟨σ', K, hrun, le_trans hK (le_of_eq (by ring)), hJ.1, hJ.2.1, hJ.2.2, hfv⟩

/-- **The fraternity walk, clearing.** The very same enumeration, with
the store of the literal one replaced by the store of a zero: what it
leaves is the stamp cleared on every cell the guarded walk could have
set, since the guarded walk's set is this one's by `rowAcc_mono`. -/
theorem fratClear_run {g : ℕ → ℕ}
    (hB1 : 1 < B) (hnB : n < B) (hmB : m < B) (hi : i < n)
    (hcsr : InCsr D m DO DT) (hdeg : D.InDegLE d) (hmW : m ≤ W)
    (hbo : Blocks "ooff" "otg" n W m OO OT σ)
    (hiv : σ.vars "i" = i) (harr : NestArr n W DO DT OO OT σ)
    (hsa : σ.arrs "stf" = arrOf n g) :
    ∃ σ' K, Run B (RamAugment.fratScan (.store "stf" (.var "u") (.lit 0))) σ σ' K ∧
      K ≤ (14 * d + 23) * (OO (i + 1) - OO i) + 12 ∧
      Marks "stf" n 0 (rowAcc OO OT (fun w => rowTgt DO DT w) i) g σ' ∧
      (∀ a, a ≠ "stf" → σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" → y ≠ "u" →
        σ'.vars y = σ.vars y) := by
  classical
  have hDle : ∀ z, z < n → DO (z + 1) ≤ m := fun z hz => incsr_le hcsr (by omega)
  have hOle : ∀ z, z < n → OO (z + 1) ≤ m := fun z hz => hbo.off_le (by omega)
  obtain ⟨σ', K, hrun, hK, hm, hfa, hfv⟩ :=
    stampNest_run (B := B) (o := "ooff") (t := "otg") (x := "i") (j := "j") (jend := "jend")
      (w := "w") (s := "stf")
      (inner := RamAugment.blockScan "doff" "dtg" "w" "q" "qe" "u"
        (.store "stf" (.var "u") (.lit 0)))
      (n := n) (nv := n) (len := W) (v := i) (b := 0) (off := OO) (tgt := OT) (g := g)
      (ic := fun _ => 14 * d + 12) (fs := fun w => rowTgt DO DT w) (σ := σ)
      (by decide) (by decide) (by decide) (by decide) (by decide) hB1 hi (by omega) hnB
      harr.2.2.2.1 (hbo.mono i hi) (le_trans (hOle i hi) hmW)
      (by have := hOle i hi; omega) hiv harr.2.2.2.2
      (fun p hp => hbo.target_lt p (by have := hOle i hi; omega)) hsa
      (by
        intro τ z h hfrτ hwz hzn hst
        obtain ⟨τ', K', hr, hK', hm', hfa', hfv'⟩ :=
          stampRow_run (B := B) (o := "doff") (t := "dtg") (x := "w") (j := "q")
            (jend := "qe") (u := "u") (s := "stf") (n := n) (nv := n) (len := W) (v := z)
            (b := 0) (off := DO) (tgt := DT) (g := h) (σ := τ)
            (by decide) (by decide) (by decide) (by decide) (by decide) hB1 hzn
            (by omega) (by omega) hnB
            (by rw [hfrτ "doff" (by decide)]; exact harr.2.1) (hcsr.mono z hzn)
            (le_trans (hDle z hzn) hmW) (by have := hDle z hzn; omega) hwz
            (by rw [hfrτ "dtg" (by decide)]; exact harr.2.2.1)
            (fun p hp => hcsr.target_lt p (lt_of_lt_of_le hp (hDle z hzn))) hst
        have hd' : DO (z + 1) - DO z ≤ d := by
          have h : DO (z + 1) - DO z = (D.inN ⟨z, hzn⟩).card := hcsr.len ⟨z, hzn⟩
          rw [h]; exact hdeg ⟨z, hzn⟩
        refine ⟨τ', K', hr, ?_, hm', hfa',
          hfv' "j" (by decide) (by decide) (by decide),
          hfv' "jend" (by decide) (by decide) (by decide)⟩
        show K' ≤ 14 * d + 12
        omega)
  refine ⟨σ', K, hrun, le_trans hK ?_, hm, hfa, fun y h1 h2 h3 h4 h5 h6 => hfv y ?_⟩
  · rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
    exact le_of_eq (by ring)
  · simp [RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.wvars, h1, h2, h3, h4, h5, h6]

/-- The out-block structure is a statement about two arrays, so a
nested walk's own record of them carries it. -/
theorem Blocks.of_nestArr {τ : Env} (hbo : Blocks "ooff" "otg" n W m OO OT σ)
    (h : NestArr n W DO DT OO OT τ) : Blocks "ooff" "otg" n W m OO OT τ :=
  hbo.of_eq (by rw [h.2.2.2.1, hbo.offArr]) (by rw [h.2.2.2.2, hbo.tgtArr])

end FratPass

/-- The fraternal degree of a vertex, at the number level. -/
noncomputable def fratDeg {n : ℕ} (D : Orientation n) (u : ℕ) : ℕ :=
  if h : u < n then (RamAugment.fratNbrs D ⟨u, h⟩).card else 0

theorem sum_fratDeg {n : ℕ} (D : Orientation n) :
    ∑ u ∈ Finset.range n, fratDeg D u = RamAugment.fratSlots D := by
  rw [← Fin.sum_univ_eq_sum_range (fun u => fratDeg D u) n]
  exact Finset.sum_congr rfl fun v _ => by simp [fratDeg, v.isLt]

/-- The fraternal partners of a vertex, at the number level. -/
noncomputable def fratSet {n : ℕ} (D : Orientation n) (u : ℕ) : Finset ℕ :=
  if h : u < n then valSet (RamAugment.fratNbrs D ⟨u, h⟩) else ∅

theorem fratSet_eq {n : ℕ} {D : Orientation n} {u : ℕ} (h : u < n) :
    fratSet D u = valSet (RamAugment.fratNbrs D ⟨u, h⟩) := dif_pos h

theorem card_fratSet {n : ℕ} (D : Orientation n) (u : ℕ) :
    (fratSet D u).card = fratDeg D u := by
  by_cases h : u < n
  · rw [fratSet_eq h, card_valSet, fratDeg, dif_pos h]
  · rw [fratSet, dif_neg h, fratDeg, dif_neg h]; simp

section FratPasses

variable {B n d W m : ℕ} {D : Orientation n} {DO DT OO OT : ℕ → ℕ} {σ : Env}

/-- **The fraternal degrees, counted.** One turn stamps the current
vertex, runs the guarded enumeration with the counter as its action,
clears every stamp the enumeration could have set, clears the current
vertex's, and writes the count one place up in the offsets. -/
theorem fratCount_run
    (hnB : n + 1 < B) (hmB : m < B) (hcsr : InCsr D m DO DT) (hdeg : D.InDegLE d)
    (hmW : m ≤ W) (hbo : Blocks "ooff" "otg" n W m OO OT σ)
    (hsnd : ∀ u < n, ∀ q, OO u ≤ q → q < OO (u + 1) → Pts DO DT (OT q) u)
    (hcmp : ∀ u < n, ∀ z < n, Pts DO DT z u → ∃ q, OO u ≤ q ∧ q < OO (u + 1) ∧ OT q = z)
    (harr : NestArr n W DO DT OO OT σ)
    (hstf0 : ∃ g, σ.arrs "stf" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hoff0 : ∃ g, σ.arrs "off" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0) :
    ∃ σ' K, Run B RamAugment.fratCount σ σ' K ∧
      K ≤ (37 * d + 46) * m + 45 * n + 8 ∧ NestArr n W DO DT OO OT σ' ∧
      (∃ g, σ'.arrs "stf" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
      (∃ g, σ'.arrs "off" = arrOf (n + 1) g ∧ g 0 = 0 ∧
        ∀ u < n, g (u + 1) = fratDeg D u) ∧
      (∀ a, a ≠ "stf" → a ≠ "off" → σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "i" → y ≠ "c" → y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" →
        y ≠ "u" → σ'.vars y = σ.vars y) := by
  classical
  obtain ⟨gs₀, hgs₀, hgz₀⟩ := hstf0
  obtain ⟨go₀, hgo₀, hgoz₀⟩ := hoff0
  set I : ℕ → Env → Prop := fun i τ => τ.vars "i" = i ∧ i ≤ n ∧
    NestArr n W DO DT OO OT τ ∧
    (∃ g, τ.arrs "stf" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
    (∃ g, τ.arrs "off" = arrOf (n + 1) g ∧ g 0 = 0 ∧ ∀ u < i, g (u + 1) = fratDeg D u)
    with hI
  have hstep : ∀ i, i < n → ∀ τ, I i τ →
      ∃ τ' K, Run B (.seq (.assign "c" (.lit 0))
          (.seq (.store "stf" (.var "i") (.lit 1))
            (.seq (RamAugment.fratScan (fratGuard (.assign "c" (.add (.var "c") (.lit 1)))))
              (.seq (RamAugment.fratScan (.store "stf" (.var "u") (.lit 0)))
                (.seq (.store "stf" (.var "i") (.lit 0))
                  (.store "off" (.add (.var "i") (.lit 1)) (.var "c"))))))) τ τ' K ∧
        K ≤ (37 * d + 46) * (OO (i + 1) - OO i) + 37 ∧ τ'.vars "i" = i ∧
        I (i + 1) (τ'.setVar "i" (i + 1)) := by
    intro i hi τ hτ
    obtain ⟨hiv, -, harrτ, ⟨gs, hgs, hgz⟩, ⟨go, hgo, hgo0, hgoI⟩⟩ := hτ
    set E : Finset ℕ := valSet (RamAugment.fratNbrs D ⟨i, hi⟩) with hE
    have hEcard : E.card = fratDeg D i := by rw [hE, card_valSet, fratDeg, dif_pos hi]
    have hEn : E ⊆ Finset.range n := fun y hy => Finset.mem_range.2 (valSet_lt hy)
    have hEle : E.card ≤ n := by
      have := Finset.card_le_card hEn; rwa [Finset.card_range] at this
    -- `c := 0`
    set τ₁ := τ.setVar "c" 0 with hτ₁
    have hr₁ : Run B (.assign "c" (.lit 0)) τ τ₁ 2 :=
      (Run.assign (evalB_lit (by omega))).mono (by simp)
    have hiv₁ : τ₁.vars "i" = i := by rw [hτ₁, vars_setVar, if_neg (by decide), hiv]
    -- `stf[i] := 1`
    have ei₁ : (Expr.var "i").evalB B τ₁ = some i := by
      have h := evalB_var (B := B) (x := "i") (σ := τ₁) (by rw [hiv₁]; omega)
      rwa [hiv₁] at h
    have hgs₁ : τ₁.arrs "stf" = arrOf n gs := by rw [hτ₁, arrs_setVar]; exact hgs
    have hl₁ : i < (τ₁.arrs "stf").length := by rw [hgs₁, length_arrOf]; exact hi
    set τ₂ := τ₁.setArr "stf" i 1 with hτ₂
    have hr₂ : Run B (.store "stf" (.var "i") (.lit 1)) τ₁ τ₂ 3 :=
      (Run.store ei₁ (evalB_lit (by omega)) hl₁).mono (by simp)
    have harr₂ : NestArr n W DO DT OO OT τ₂ :=
      (harrτ.setVar "c" (by decide) 0).setArr (by decide) (by decide) (by decide)
        (by decide) i 1
    have hm₂ : Marks "stf" n 1 ({i} : Finset ℕ) (fun _ => 0) τ₂ := by
      refine ⟨fun k => if k = i then 1 else gs k, by
        rw [hτ₂, arrs_setArr, if_pos rfl, hgs₁, set_arrOf], fun k hk => ?_⟩
      simp only []
      by_cases hkz : k = i
      · rw [if_pos hkz, if_pos (Finset.mem_singleton.2 hkz)]
      · rw [if_neg hkz, if_neg (fun hc => hkz (Finset.mem_singleton.1 hc)), hgz k hk]
    have hiv₂ : τ₂.vars "i" = i := by rw [hτ₂, vars_setArr]; exact hiv₁
    have hA0 : CntAcc n i (∅ : Finset ℕ) τ₂ :=
      ⟨by rw [hτ₂, vars_setArr, hτ₁, vars_setVar, if_pos rfl]; simp, hiv₂, by simp⟩
    -- the guarded enumeration
    obtain ⟨τ₃, K₃, hr₃, hK₃, hm₃, hA₃, harr₃, hfv₃⟩ :=
      fratEmit_run (B := B) (n := n) (d := d) (W := W) (m := m) (Ka := 4) (a₁ := "@")
        (a₂ := "@") (act := .assign "c" (.add (.var "c") (.lit 1))) (D := D) (DO := DO)
        (DT := DT) (OO := OO) (OT := OT) (Acc := CntAcc n i) (Cap := E) (i := i) (σ := τ₂)
        readArrs_at readArrs_at (by omega) (by omega) hmB hi hcsr hdeg hmW
        (hbo.of_nestArr harr₂) hsnd hcmp hiv₂ harr₂ hm₂
        (fun S τ p x h => h.setArr "stf" p x)
        (fun S τ y z hy h => h.setVar
          (by rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          (by rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) z)
        (cntAcc_emits (by omega)) (Finset.Subset.refl _) hA0
    have hoff₃ : τ₃.arrs "off" = τ₂.arrs "off" :=
      hr₃.frame_arr "off" (by
        simp [RamAugment.fratScan, RamAugment.blockScan, fratGuard, Csr.loadRow, Csr.scan,
          Com.warrs])
    obtain ⟨g₃, hg₃, hg₃k⟩ := hm₃
    -- the clearing enumeration
    obtain ⟨τ₄, K₄, hr₄, hK₄, hm₄, hfa₄, hfv₄⟩ :=
      fratClear_run (B := B) (n := n) (d := d) (W := W) (m := m) (D := D) (DO := DO)
        (DT := DT) (OO := OO) (OT := OT) (i := i) (σ := τ₃) (g := g₃)
        (by omega) (by omega) hmB hi hcsr hdeg hmW (hbo.of_nestArr harr₃)
        (by rw [hfv₃ "i" (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide)]; exact hiv₂)
        harr₃ hg₃
    obtain ⟨g₄, hg₄, hg₄k⟩ := hm₄
    have hsub : E ⊆ rowAcc OO OT (fun w => rowTgt DO DT w) i := by
      rw [hE, ← fratRow_eq hcsr (fun z hz => hbo.off_le (by omega))
        (fun q hq => hbo.target_lt q hq) hi (hsnd i hi) (fun z hz hp => hcmp i hi z hz hp)]
      exact rowAcc_mono (fun w => rowAcc_mono (fun y => by
        by_cases h : y = i
        · rw [if_pos h]; exact Finset.empty_subset _
        · rw [if_neg h]) w) i
    have hg₄z : ∀ k < n, k ≠ i → g₄ k = 0 := by
      intro k hk hki
      rw [hg₄k k hk]
      by_cases hkr : k ∈ rowAcc OO OT (fun w => rowTgt DO DT w) i
      · rw [if_pos hkr]
      · rw [if_neg hkr, hg₃k k hk, if_neg]
        rintro hc
        rcases Finset.mem_union.1 hc with h | h
        · exact hki (Finset.mem_singleton.1 h)
        · exact hkr (hsub h)
    -- `stf[i] := 0`
    have hiv₄ : τ₄.vars "i" = i := by
      rw [hfv₄ "i" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfv₃ "i" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
      exact hiv₂
    have ei₄ : (Expr.var "i").evalB B τ₄ = some i := by
      have h := evalB_var (B := B) (x := "i") (σ := τ₄) (by rw [hiv₄]; omega)
      rwa [hiv₄] at h
    have hl₄ : i < (τ₄.arrs "stf").length := by rw [hg₄, length_arrOf]; exact hi
    set τ₅ := τ₄.setArr "stf" i 0 with hτ₅
    have hr₅ : Run B (.store "stf" (.var "i") (.lit 0)) τ₄ τ₅ 3 :=
      (Run.store ei₄ (evalB_lit (by omega)) hl₄).mono (by simp)
    have hstf₅ : ∃ g, τ₅.arrs "stf" = arrOf n g ∧ ∀ k < n, g k = 0 := by
      refine ⟨fun k => if k = i then 0 else g₄ k, by
        rw [hτ₅, arrs_setArr, if_pos rfl, hg₄, set_arrOf], fun k hk => ?_⟩
      simp only []
      by_cases hkz : k = i
      · rw [if_pos hkz]
      · rw [if_neg hkz]; exact hg₄z k hk hkz
    -- `off[i+1] := c`
    have hiv₅ : τ₅.vars "i" = i := by rw [hτ₅, vars_setArr]; exact hiv₄
    have hcv₅ : τ₅.vars "c" = E.card := by
      rw [hτ₅, vars_setArr,
        hfv₄ "c" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hA₃.1
    have eidx : (Expr.add (.var "i") (.lit 1)).evalB B τ₅ = some (i + 1) := by
      have h := evalB_bin (B := B) (op := .add) (σ := τ₅) (m := τ₅.vars "i") (n := 1)
        (evalB_var (by rw [hiv₅]; omega)) (evalB_lit (by omega))
        (by rw [hiv₅]; simpa [Bop.apply] using (by omega : i + 1 < B))
      rw [hiv₅] at h
      simpa [Bop.apply] using h
    have ecv : (Expr.var "c").evalB B τ₅ = some E.card := by
      have h := evalB_var (B := B) (x := "c") (σ := τ₅) (by rw [hcv₅]; omega)
      rwa [hcv₅] at h
    have hgo₅ : τ₅.arrs "off" = arrOf (n + 1) go := by
      rw [hτ₅, arrs_setArr, if_neg (by decide), hfa₄ "off" (by decide), hoff₃, hτ₂,
        arrs_setArr, if_neg (by decide), hτ₁, arrs_setVar]
      exact hgo
    have hl₆ : i + 1 < (τ₅.arrs "off").length := by rw [hgo₅, length_arrOf]; omega
    have hn₄ : τ₄.vars "n" = n := by
      rw [hfv₄ "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact harr₃.1
    have harr₄ : NestArr n W DO DT OO OT τ₄ :=
      ⟨hn₄,
        by rw [hfa₄ "doff" (by decide)]; exact harr₃.2.1,
        by rw [hfa₄ "dtg" (by decide)]; exact harr₃.2.2.1,
        by rw [hfa₄ "ooff" (by decide)]; exact harr₃.2.2.2.1,
        by rw [hfa₄ "otg" (by decide)]; exact harr₃.2.2.2.2⟩
    obtain ⟨gs₅, hgs₅, hgs₅z⟩ := hstf₅
    have hcost : 2 + (3 + (K₃ + (K₄ + (3 + 5))))
        ≤ (37 * d + 46) * (OO (i + 1) - OO i) + 37 := by
      have h₃ : K₃ ≤ (23 * d + 23) * (OO (i + 1) - OO i) + 12 :=
        le_trans hK₃ (le_of_eq (by ring))
      have hsum : (23 * d + 23) * (OO (i + 1) - OO i) + (14 * d + 23) * (OO (i + 1) - OO i)
          = (37 * d + 46) * (OO (i + 1) - OO i) := by ring
      omega
    refine ⟨τ₅.setArr "off" (i + 1) E.card, 2 + (3 + (K₃ + (K₄ + (3 + 5)))),
      hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq
        ((Run.store eidx ecv hl₆).mono
          (by simp only [size_add, size_var, size_lit]; omega)))))), hcost,
      by rw [vars_setArr]; exact hiv₅, ?_⟩
    refine ⟨by simp, by omega,
      ((((harr₄.setArr (a := "stf") (by decide) (by decide) (by decide) (by decide) i 0)).setArr
        (a := "off") (by decide) (by decide) (by decide) (by decide) (i + 1) E.card).setVar
        "i" (by decide) (i + 1)),
      ⟨gs₅, by rw [arrs_setVar, arrs_setArr, if_neg (by decide)]; exact hgs₅, hgs₅z⟩,
      ⟨fun k => if k = i + 1 then E.card else go k, ?_, ?_, ?_⟩⟩
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, hgo₅, set_arrOf]
    · simp only []; rw [if_neg (by omega)]; exact hgo0
    · intro u hu
      simp only []
      rcases Nat.lt_or_ge u i with h | h
      · rw [if_neg (by omega)]; exact hgoI u h
      · rw [if_pos (show u + 1 = i + 1 by omega), show u = i from by omega]
        exact hEcard
  obtain ⟨σ', K, hrun, hK, hIn⟩ :=
    forVerts_run (B := B) (n := n)
      (costs := fun i => (37 * d + 46) * (OO (i + 1) - OO i) + 37) (I := I) (σ := σ) hnB
      (fun _ _ h => h.2.2.1.1) (fun _ _ h => h.1) (fun _ _ h => h.2.1) hstep
      ⟨by simp, by omega, harr.setVar "i" (by decide) 0,
        ⟨gs₀, by simpa using hgs₀, hgz₀⟩,
        ⟨go₀, by simpa using hgo₀, hgoz₀ 0 (by omega), fun u hu => absurd hu (by omega)⟩⟩
  obtain ⟨-, -, harr', hstf', hoff'⟩ := hIn
  refine ⟨σ', K, hrun, le_trans hK ?_, harr', hstf', hoff',
    fun a h1 h2 => hrun.frame_arr a ?_, fun y h1 h2 h3 h4 h5 h6 h7 h8 => hrun.frame_var y ?_⟩
  · have hsum : ∑ i ∈ Finset.range n, ((37 * d + 46) * (OO (i + 1) - OO i) + 37 + 8)
        = (37 * d + 46) * m + 45 * n := by
      have hpt : ∀ i ∈ Finset.range n, (37 * d + 46) * (OO (i + 1) - OO i) + 37 + 8
          = (37 * d + 46) * (OO (i + 1) - OO i) + 45 := fun i _ => by omega
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.mul_sum, hbo.sum_rowLen,
        Finset.sum_const, Finset.card_range, smul_eq_mul]
      ring
    omega
  · simp [RamAugment.forVerts, RamAugment.fratScan, RamAugment.blockScan, fratGuard,
      Csr.loadRow, Csr.scan, Com.warrs, h1, h2]
  · simp [RamAugment.forVerts, RamAugment.fratScan, RamAugment.blockScan, fratGuard,
      Csr.loadRow, Csr.scan, Com.wvars, h1, h2, h3, h4, h5, h6, h7, h8]

/-- **The partners, written out once each.** The same turn as the
count, with the fill pointer of the current vertex for its action: the
block the turn opens ends up naming `RamAugment.fratNbrs D i`, once
each, since `FillAcc`'s window is as long as the emitted set. -/
theorem fratFill_run {nf : ℕ} {FT₀ : ℕ → ℕ}
    (hnB : n + 1 < B) (hmB : m < B) (hnfB : nf < B)
    (hcsr : InCsr D m DO DT) (hdeg : D.InDegLE d) (hmW : m ≤ W)
    (hbo : Blocks "ooff" "otg" n W m OO OT σ)
    (hsnd : ∀ u < n, ∀ q, OO u ≤ q → q < OO (u + 1) → Pts DO DT (OT q) u)
    (hcmp : ∀ u < n, ∀ z < n, Pts DO DT z u → ∃ q, OO u ≤ q ∧ q < OO (u + 1) ∧ OT q = z)
    (hnf : RamElim.psum (fratDeg D) n = nf)
    (harr : NestArr n W DO DT OO OT σ)
    (hstf0 : ∃ g, σ.arrs "stf" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hffl : σ.arrs "ffl" = arrOf n (RamElim.psum (fratDeg D)))
    (htgt : σ.arrs "tgt" = arrOf nf FT₀) :
    ∃ σ' K, Run B RamAugment.fratFill σ σ' K ∧
      K ≤ (43 * d + 46) * m + 38 * n + 8 ∧ NestArr n W DO DT OO OT σ' ∧
      (∃ g, σ'.arrs "stf" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
      (∃ FT, σ'.arrs "tgt" = arrOf nf FT ∧ ∀ u < n,
        (∀ q, RamElim.psum (fratDeg D) u ≤ q → q < RamElim.psum (fratDeg D) (u + 1) →
          FT q ∈ fratSet D u) ∧
        (∀ z ∈ fratSet D u, ∃ q, RamElim.psum (fratDeg D) u ≤ q ∧
          q < RamElim.psum (fratDeg D) (u + 1) ∧ FT q = z)) ∧
      (∀ a, a ≠ "stf" → a ≠ "tgt" → a ≠ "ffl" → σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "i" → y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" → y ≠ "u" →
        σ'.vars y = σ.vars y) := by
  classical
  obtain ⟨gs₀, hgs₀, hgz₀⟩ := hstf0
  set FO : ℕ → ℕ := RamElim.psum (fratDeg D) with hFO
  have hFOsucc : ∀ u, FO (u + 1) = FO u + fratDeg D u := fun u => RamElim.psum_succ _ u
  have hFOle : ∀ u ≤ n, FO u ≤ nf := fun u hu => by
    rw [← hnf]; exact RamElim.psum_mono _ hu
  set I : ℕ → Env → Prop := fun i τ => τ.vars "i" = i ∧ i ≤ n ∧
    NestArr n W DO DT OO OT τ ∧
    (∃ g, τ.arrs "stf" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
    (∃ f, τ.arrs "ffl" = arrOf n f ∧ ∀ k, i ≤ k → f k = FO k) ∧
    (∃ FT, τ.arrs "tgt" = arrOf nf FT ∧ ∀ u < i,
      (∀ q, FO u ≤ q → q < FO (u + 1) → FT q ∈ fratSet D u) ∧
      (∀ z ∈ fratSet D u, ∃ q, FO u ≤ q ∧ q < FO (u + 1) ∧ FT q = z)) with hI
  have hstep : ∀ i, i < n → ∀ τ, I i τ →
      ∃ τ' K, Run B (.seq (.store "stf" (.var "i") (.lit 1))
          (.seq (RamAugment.fratScan (fratGuard
              (.seq (.store "tgt" (.get "ffl" (.var "i")) (.var "u"))
                (.store "ffl" (.var "i") (.add (.get "ffl" (.var "i")) (.lit 1))))))
            (.seq (RamAugment.fratScan (.store "stf" (.var "u") (.lit 0)))
              (.store "stf" (.var "i") (.lit 0))))) τ τ' K ∧
        K ≤ (43 * d + 46) * (OO (i + 1) - OO i) + 30 ∧ τ'.vars "i" = i ∧
        I (i + 1) (τ'.setVar "i" (i + 1)) := by
    intro i hi τ hτ
    obtain ⟨hiv, -, harrτ, ⟨gs, hgs, hgz⟩, ⟨f, hf, hfk⟩, ⟨FT, hFT, hFTI⟩⟩ := hτ
    have hEs : fratSet D i = valSet (RamAugment.fratNbrs D ⟨i, hi⟩) := fratSet_eq hi
    have hEcard : FO i + (fratSet D i).card = FO (i + 1) := by
      rw [card_fratSet, hFOsucc]
    have hEcard' : FO i + (valSet (RamAugment.fratNbrs D ⟨i, hi⟩)).card = FO (i + 1) := by
      rw [← hEs]; exact hEcard
    -- `stf[i] := 1`
    have ei : (Expr.var "i").evalB B τ = some i := by
      have h := evalB_var (B := B) (x := "i") (σ := τ) (by rw [hiv]; omega)
      rwa [hiv] at h
    have hl₁ : i < (τ.arrs "stf").length := by rw [hgs, length_arrOf]; exact hi
    set τ₁ := τ.setArr "stf" i 1 with hτ₁
    have hr₁ : Run B (.store "stf" (.var "i") (.lit 1)) τ τ₁ 3 :=
      (Run.store ei (evalB_lit (by omega)) hl₁).mono (by simp)
    have harr₁ : NestArr n W DO DT OO OT τ₁ :=
      harrτ.setArr (by decide) (by decide) (by decide) (by decide) i 1
    have hiv₁ : τ₁.vars "i" = i := by rw [hτ₁, vars_setArr]; exact hiv
    have hm₁ : Marks "stf" n 1 ({i} : Finset ℕ) (fun _ => 0) τ₁ := by
      refine ⟨fun k => if k = i then 1 else gs k, by
        rw [hτ₁, arrs_setArr, if_pos rfl, hgs, set_arrOf], fun k hk => ?_⟩
      simp only []
      by_cases hkz : k = i
      · rw [if_pos hkz, if_pos (Finset.mem_singleton.2 hkz)]
      · rw [if_neg hkz, if_neg (fun hc => hkz (Finset.mem_singleton.1 hc)), hgz k hk]
    have hA0 : FillAcc "tgt" "ffl" n nf i (FO i) FT f (fratSet D i) ∅ τ₁ :=
      ⟨hiv₁, by simp,
        ⟨f, by rw [hτ₁, arrs_setArr, if_neg (by decide)]; exact hf,
          by rw [hfk i le_rfl]; simp, fun k _ => rfl⟩,
        ⟨FT, by rw [hτ₁, arrs_setArr, if_neg (by decide)]; exact hFT,
          fun q h₁ h₂ => by simp at h₂; omega, fun z hz => absurd hz (by simp),
          fun q _ => rfl⟩⟩
    -- the guarded enumeration
    obtain ⟨τ₃, K₃, hr₃, hK₃, hm₃, hA₃, harr₃, hfv₃⟩ :=
      fratEmit_run (B := B) (n := n) (d := d) (W := W) (m := m) (Ka := 10) (a₁ := "tgt")
        (a₂ := "ffl")
        (act := .seq (.store "tgt" (.get "ffl" (.var "i")) (.var "u"))
          (.store "ffl" (.var "i") (.add (.get "ffl" (.var "i")) (.lit 1))))
        (D := D) (DO := DO) (DT := DT) (OO := OO) (OT := OT)
        (Acc := FillAcc "tgt" "ffl" n nf i (FO i) FT f (fratSet D i))
        (Cap := fratSet D i) (i := i) (σ := τ₁)
        readArrs_tgt readArrs_ffl (by omega) (by omega) hmB hi hcsr hdeg hmW
        (hbo.of_nestArr harr₁) hsnd hcmp hiv₁ harr₁ hm₁
        (fun S τ p x h => h.setArr (by decide) (by decide) p x)
        (fun S τ y z hy h => h.setVar
          (by rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) z)
        (fillAcc_emits (by decide) hi (by omega) (by omega)
          (by rw [hEcard]; exact hFOle (i + 1) (by omega)))
        (by rw [hEs]) hA0
    obtain ⟨g₃, hg₃, hg₃k⟩ := hm₃
    -- the clearing enumeration
    obtain ⟨τ₄, K₄, hr₄, hK₄, hm₄, hfa₄, hfv₄⟩ :=
      fratClear_run (B := B) (n := n) (d := d) (W := W) (m := m) (D := D) (DO := DO)
        (DT := DT) (OO := OO) (OT := OT) (i := i) (σ := τ₃) (g := g₃)
        (by omega) (by omega) hmB hi hcsr hdeg hmW (hbo.of_nestArr harr₃) hA₃.1 harr₃ hg₃
    obtain ⟨g₄, hg₄, hg₄k⟩ := hm₄
    have hsub : valSet (RamAugment.fratNbrs D ⟨i, hi⟩)
        ⊆ rowAcc OO OT (fun w => rowTgt DO DT w) i := by
      rw [← fratRow_eq hcsr (fun z hz => hbo.off_le (by omega))
        (fun q hq => hbo.target_lt q hq) hi (hsnd i hi) (fun z hz hp => hcmp i hi z hz hp)]
      exact rowAcc_mono (fun w => rowAcc_mono (fun y => by
        by_cases h : y = i
        · rw [if_pos h]; exact Finset.empty_subset _
        · rw [if_neg h]) w) i
    have hg₄z : ∀ k < n, k ≠ i → g₄ k = 0 := by
      intro k hk hki
      rw [hg₄k k hk]
      by_cases hkr : k ∈ rowAcc OO OT (fun w => rowTgt DO DT w) i
      · rw [if_pos hkr]
      · rw [if_neg hkr, hg₃k k hk, if_neg]
        rintro hc
        rcases Finset.mem_union.1 hc with h | h
        · exact hki (Finset.mem_singleton.1 h)
        · exact hkr (hsub h)
    -- `stf[i] := 0`
    have hiv₄ : τ₄.vars "i" = i := by
      rw [hfv₄ "i" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hA₃.1
    have ei₄ : (Expr.var "i").evalB B τ₄ = some i := by
      have h := evalB_var (B := B) (x := "i") (σ := τ₄) (by rw [hiv₄]; omega)
      rwa [hiv₄] at h
    have hl₄ : i < (τ₄.arrs "stf").length := by rw [hg₄, length_arrOf]; exact hi
    set τ₅ := τ₄.setArr "stf" i 0 with hτ₅
    have hr₅ : Run B (.store "stf" (.var "i") (.lit 0)) τ₄ τ₅ 3 :=
      (Run.store ei₄ (evalB_lit (by omega)) hl₄).mono (by simp)
    have hn₄ : τ₄.vars "n" = n := by
      rw [hfv₄ "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact harr₃.1
    have harr₄ : NestArr n W DO DT OO OT τ₄ :=
      ⟨hn₄, by rw [hfa₄ "doff" (by decide)]; exact harr₃.2.1,
        by rw [hfa₄ "dtg" (by decide)]; exact harr₃.2.2.1,
        by rw [hfa₄ "ooff" (by decide)]; exact harr₃.2.2.2.1,
        by rw [hfa₄ "otg" (by decide)]; exact harr₃.2.2.2.2⟩
    obtain ⟨-, -, ⟨f', hf'a, hf'i, hf'k⟩, ⟨G, hGa, hG₁, hG₂, hG₃⟩⟩ := hA₃
    have hcost : 3 + (K₃ + (K₄ + 3)) ≤ (43 * d + 46) * (OO (i + 1) - OO i) + 30 := by
      have h₃ : K₃ ≤ (29 * d + 23) * (OO (i + 1) - OO i) + 12 :=
        le_trans hK₃ (le_of_eq (by ring))
      have hsum : (29 * d + 23) * (OO (i + 1) - OO i) + (14 * d + 23) * (OO (i + 1) - OO i)
          = (43 * d + 46) * (OO (i + 1) - OO i) := by ring
      omega
    refine ⟨τ₅, 3 + (K₃ + (K₄ + 3)), hr₁.seq (hr₃.seq (hr₄.seq hr₅)), hcost,
      by rw [hτ₅, vars_setArr]; exact hiv₄, ?_⟩
    refine ⟨by simp, by omega,
      (harr₄.setArr (a := "stf") (by decide) (by decide) (by decide) (by decide) i 0).setVar
        "i" (by decide) (i + 1),
      ⟨fun k => if k = i then 0 else g₄ k, by
        rw [arrs_setVar, hτ₅, arrs_setArr, if_pos rfl, hg₄, set_arrOf], fun k hk => by
        simp only []
        by_cases hkz : k = i
        · rw [if_pos hkz]
        · rw [if_neg hkz]; exact hg₄z k hk hkz⟩,
      ⟨f', ?_, ?_⟩, ⟨G, ?_, ?_⟩⟩
    · rw [arrs_setVar, hτ₅, arrs_setArr, if_neg (by decide), hfa₄ "ffl" (by decide)]
      exact hf'a
    · intro k hk
      rw [hf'k k (by omega)]
      exact hfk k (by omega)
    · rw [arrs_setVar, hτ₅, arrs_setArr, if_neg (by decide), hfa₄ "tgt" (by decide)]
      exact hGa
    · intro u hu
      rcases Nat.lt_or_ge u i with h | h
      · have hlo : FO (u + 1) ≤ FO i := RamElim.psum_mono _ (by omega)
        constructor
        · intro q h₁ h₂
          rw [hG₃ q (Or.inl (by omega))]
          exact (hFTI u h).1 q h₁ h₂
        · intro z hz
          obtain ⟨q, hq₁, hq₂, hq₃⟩ := (hFTI u h).2 z hz
          exact ⟨q, hq₁, hq₂, by rw [hG₃ q (Or.inl (by omega))]; exact hq₃⟩
      · have hui : u = i := by omega
        subst hui
        rw [hEs]
        refine ⟨fun q h₁ h₂ => hG₁ q h₁ (by rw [hEcard']; exact h₂), fun z hz => ?_⟩
        obtain ⟨q, hq₁, hq₂, hq₃⟩ := hG₂ z hz
        exact ⟨q, hq₁, by rw [← hEcard']; exact hq₂, hq₃⟩
  obtain ⟨σ', K, hrun, hK, hIn⟩ :=
    forVerts_run (B := B) (n := n)
      (costs := fun i => (43 * d + 46) * (OO (i + 1) - OO i) + 30) (I := I) (σ := σ) hnB
      (fun _ _ h => h.2.2.1.1) (fun _ _ h => h.1) (fun _ _ h => h.2.1) hstep
      ⟨by simp, by omega, harr.setVar "i" (by decide) 0,
        ⟨gs₀, by simpa using hgs₀, hgz₀⟩,
        ⟨FO, by simpa using hffl, fun k _ => rfl⟩,
        ⟨FT₀, by simpa using htgt, fun u hu => absurd hu (by omega)⟩⟩
  obtain ⟨-, -, harr', hstf', -, htgt'⟩ := hIn
  refine ⟨σ', K, hrun, le_trans hK ?_, harr', hstf', htgt',
    fun a h1 h2 h3 => hrun.frame_arr a ?_,
    fun y h1 h2 h3 h4 h5 h6 h7 => hrun.frame_var y ?_⟩
  · have hsum : ∑ i ∈ Finset.range n, ((43 * d + 46) * (OO (i + 1) - OO i) + 30 + 8)
        = (43 * d + 46) * m + 38 * n := by
      have hpt : ∀ i ∈ Finset.range n, (43 * d + 46) * (OO (i + 1) - OO i) + 30 + 8
          = (43 * d + 46) * (OO (i + 1) - OO i) + 38 := fun i _ => by omega
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.mul_sum, hbo.sum_rowLen,
        Finset.sum_const, Finset.card_range, smul_eq_mul]
      ring
    omega
  · simp [RamAugment.forVerts, RamAugment.fratScan, RamAugment.blockScan, fratGuard,
      Csr.loadRow, Csr.scan, Com.warrs, h1, h2, h3]
  · simp [RamAugment.forVerts, RamAugment.fratScan, RamAugment.blockScan, fratGuard,
      Csr.loadRow, Csr.scan, Com.wvars, h1, h2, h3, h4, h5, h6, h7]

/-- **A block that names a set of its own size names it once.** The
slots map onto the set, and the block is exactly as long as the set, so
the map is injective — which is `RamElim.CsrSimple`'s `nodup` for
every block structure a fill pass writes. -/
theorem block_nodup {O T : ℕ → ℕ} {S : Finset ℕ} {u : ℕ}
    (hcard : O (u + 1) - O u = S.card) (_hle : O u ≤ O (u + 1))
    (h₁ : ∀ q, O u ≤ q → q < O (u + 1) → T q ∈ S)
    (h₂ : ∀ z ∈ S, ∃ q, O u ≤ q ∧ q < O (u + 1) ∧ T q = z)
    {j₁ j₂ : ℕ} (a₁ : O u ≤ j₁) (a₂ : j₁ < O (u + 1)) (a₃ : O u ≤ j₂)
    (a₄ : j₂ < O (u + 1)) (he : T j₁ = T j₂) : j₁ = j₂ := by
  classical
  have himg : (Finset.Ico (O u) (O (u + 1))).image T = S := by
    ext y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [Finset.mem_Ico] at hq
      exact h₁ q hq.1 hq.2
    · intro hy
      obtain ⟨q, hq₁, hq₂, hq₃⟩ := h₂ y hy
      exact ⟨q, Finset.mem_Ico.2 ⟨hq₁, hq₂⟩, hq₃⟩
  have hc : ((Finset.Ico (O u) (O (u + 1))).image T).card
      = (Finset.Ico (O u) (O (u + 1))).card := by rw [himg, Nat.card_Ico, hcard]
  exact Finset.injOn_of_card_image_eq hc
    (by simp only [Finset.coe_Ico, Set.mem_Ico]; exact ⟨a₁, a₂⟩)
    (by simp only [Finset.coe_Ico, Set.mem_Ico]; exact ⟨a₃, a₄⟩) he

/-- **The fraternity graph, materialized.** The three passes and the
report, sequenced: what they leave in `off`/`tgt` is
`RamElim.CsrSimple` of `RamAugment.fratGraph D` at
`RamAugment.fratSlots D` slots, which is the engine's input surface, and
what they leave in `mf` is that slot count. -/
theorem fratPass_run {nf : ℕ}
    (hnB : n + 1 < B) (hmB : m < B) (hnfB : nf < B)
    (hcsr : InCsr D m DO DT) (hdeg : D.InDegLE d) (hmW : m ≤ W)
    (hbo : Blocks "ooff" "otg" n W m OO OT σ)
    (hsnd : ∀ u < n, ∀ q, OO u ≤ q → q < OO (u + 1) → Pts DO DT (OT q) u)
    (hcmp : ∀ u < n, ∀ z < n, Pts DO DT z u → ∃ q, OO u ≤ q ∧ q < OO (u + 1) ∧ OT q = z)
    (hnf : RamAugment.fratSlots D = nf)
    (harr : NestArr n W DO DT OO OT σ)
    (hstf0 : ∃ g, σ.arrs "stf" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hoff0 : ∃ g, σ.arrs "off" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0)
    (hffl0 : ∃ g, σ.arrs "ffl" = arrOf n g) (htgt0 : ∃ g, σ.arrs "tgt" = arrOf nf g) :
    ∃ σ' K, Run B RamAugment.fratPass σ σ' K ∧
      K ≤ (80 * d + 92) * m + 106 * n + 40 ∧ NestArr n W DO DT OO OT σ' ∧
      (∃ g, σ'.arrs "stf" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
      σ'.arrs "off" = arrOf (n + 1) (RamElim.psum (fratDeg D)) ∧
      (∃ FT, σ'.arrs "tgt" = arrOf nf FT ∧
        CsrSimple (fratGraph D) nf (RamElim.psum (fratDeg D)) FT) ∧
      σ'.vars "mf" = nf ∧
      (∀ a, a ≠ "stf" → a ≠ "off" → a ≠ "tgt" → a ≠ "ffl" → σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "i" → y ≠ "c" → y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" →
        y ≠ "u" → y ≠ "mf" → σ'.vars y = σ.vars y) := by
  classical
  have hFOn : RamElim.psum (fratDeg D) n = nf := by
    show ∑ u ∈ Finset.range n, fratDeg D u = nf
    rw [sum_fratDeg]; exact hnf
  obtain ⟨σ₁, K₁, hr₁, hK₁, harr₁, hstf₁, hoff₁, hfa₁, hfv₁⟩ :=
    fratCount_run hnB hmB hcsr hdeg hmW hbo hsnd hcmp harr hstf0 hoff0
  obtain ⟨σ₂, K₂, hr₂, hK₂, hn₂, hoffa₂, hffl₂⟩ :=
    prefixPass_run (B := B) (a := "off") (b := "ffl") (n := n) (d := fratDeg D) (σ := σ₁)
      (by decide) hnB (by rw [hFOn]; exact hnfB) harr₁.1 hoff₁
      (by obtain ⟨g, hg⟩ := hffl0
          exact ⟨g, by rw [hfa₁ "ffl" (by decide) (by decide)]; exact hg⟩)
  have hfa₂ : ∀ a, a ≠ "off" → a ≠ "ffl" → σ₂.arrs a = σ₁.arrs a :=
    fun a ha hb => hr₂.frame_arr a (by
      simp [prefixCom, RamAugment.forVerts, Com.warrs, ha, hb])
  have hfv₂ : ∀ y, y ≠ "i" → σ₂.vars y = σ₁.vars y :=
    fun y hy => hr₂.frame_var y (by simp [prefixCom, RamAugment.forVerts, Com.wvars, hy])
  have harr₂ : NestArr n W DO DT OO OT σ₂ :=
    ⟨hn₂, by rw [hfa₂ "doff" (by decide) (by decide)]; exact harr₁.2.1,
      by rw [hfa₂ "dtg" (by decide) (by decide)]; exact harr₁.2.2.1,
      by rw [hfa₂ "ooff" (by decide) (by decide)]; exact harr₁.2.2.2.1,
      by rw [hfa₂ "otg" (by decide) (by decide)]; exact harr₁.2.2.2.2⟩
  obtain ⟨g₂, hg₂, hg₂z⟩ := hstf₁
  obtain ⟨FT₀, hFT₀⟩ := htgt0
  obtain ⟨σ₃, K₃, hr₃, hK₃, harr₃, hstf₃, htgt₃, hfa₃, hfv₃⟩ :=
    fratFill_run (B := B) (n := n) (d := d) (W := W) (m := m) (D := D) (DO := DO) (DT := DT)
      (OO := OO) (OT := OT) (σ := σ₂) (nf := nf) (FT₀ := FT₀) hnB hmB hnfB hcsr hdeg hmW
      (hbo.of_nestArr harr₂) hsnd hcmp hFOn harr₂
      ⟨g₂, by rw [hfa₂ "stf" (by decide) (by decide)]; exact hg₂, hg₂z⟩ hffl₂
      (by rw [hfa₂ "tgt" (by decide) (by decide), hfa₁ "tgt" (by decide) (by decide)];
          exact hFT₀)
  have hoff₃ : σ₃.arrs "off" = arrOf (n + 1) (RamElim.psum (fratDeg D)) := by
    rw [hfa₃ "off" (by decide) (by decide) (by decide)]; exact hoffa₂
  -- the report
  have hnv₃ : σ₃.vars "n" = n := harr₃.1
  have en : (Expr.var "n").evalB B σ₃ = some n := by
    have h := evalB_var (B := B) (x := "n") (σ := σ₃) (by rw [hnv₃]; omega)
    rwa [hnv₃] at h
  have eget : (Expr.get "off" (.var "n")).evalB B σ₃ = some nf :=
    evalB_get en (by rw [hoff₃, getElem?_arrOf (RamElim.psum (fratDeg D)) (by omega), hFOn])
      (by omega)
  have hcost : K₁ + (K₂ + (K₃ + 3)) ≤ (80 * d + 92) * m + 106 * n + 40 := by
    have hsum : (37 * d + 46) * m + (43 * d + 46) * m = (80 * d + 92) * m := by ring
    omega
  refine ⟨σ₃.setVar "mf" nf, K₁ + (K₂ + (K₃ + 3)),
    hr₁.seq (hr₂.seq (hr₃.seq ((Run.assign eget).mono (by simp)))), hcost,
    harr₃.setVar "mf" (by decide) nf, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · obtain ⟨g, hg, hz⟩ := hstf₃
    exact ⟨g, by rw [arrs_setVar]; exact hg, hz⟩
  · rw [arrs_setVar]; exact hoff₃
  · obtain ⟨FT, hFTa, hFTb⟩ := htgt₃
    refine ⟨FT, by rw [arrs_setVar]; exact hFTa, ⟨⟨RamElim.psum_zero _, hFOn,
      fun i _ => RamElim.psum_mono _ (by omega), ?_, ?_⟩, ?_⟩⟩
    · intro j hj
      obtain ⟨w, hw, ha, hb⟩ :=
        RamElim.exists_block (ID := fratDeg D) (m := n) (t := j) (by rw [hFOn]; exact hj)
      exact valSet_lt (by
        have := (hFTb w hw).1 j ha hb
        rwa [fratSet_eq hw] at this)
    · intro u v
      constructor
      · intro hadj
        have hv : (v : ℕ) ∈ fratSet D (u : ℕ) := by
          rw [fratSet_eq u.isLt]
          exact mem_valSet_of (RamAugment.mem_fratNbrs.2 (by simpa using hadj.symm))
        obtain ⟨q, hq₁, hq₂, hq₃⟩ := (hFTb (u : ℕ) u.isLt).2 (v : ℕ) hv
        exact ⟨q, hq₁, hq₂, hq₃⟩
      · rintro ⟨q, hq₁, hq₂, hq₃⟩
        have h := (hFTb (u : ℕ) u.isLt).1 q hq₁ hq₂
        rw [fratSet_eq u.isLt] at h
        obtain ⟨hlt, hmem⟩ := mem_valSet.1 h
        have hadj := RamAugment.mem_fratNbrs.1 hmem
        have : (⟨FT q, hlt⟩ : Fin n) = v := Fin.ext hq₃
        rw [this] at hadj
        exact hadj.symm
    · intro u hu j₁ j₂ b₁ b₂ b₃ b₄ he
      refine block_nodup (S := fratSet D u) ?_ (RamElim.psum_mono _ (by omega))
        ((hFTb u hu).1) ((hFTb u hu).2) b₁ b₂ b₃ b₄ he
      rw [card_fratSet, RamElim.psum_succ]
      omega
  · intro a h1 h2 h3 h4
    rw [arrs_setVar, hfa₃ a h1 h3 h4, hfa₂ a h2 h4, hfa₁ a h1 h2]
  · intro y h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [vars_setVar, if_neg h9, hfv₃ y h1 h3 h4 h5 h6 h7 h8, hfv₂ y h1,
      hfv₁ y h1 h2 h3 h4 h5 h6 h7 h8]

end FratPasses

/-! ### The assembly's stamps

`RamAugment.asmStamp b` is three walks over two block structures, and
the same command at `b = 1` and at `b = 0` — a set on the way in and its
erasure on the way out. What it leaves is `sta` on the vertices `D`
makes `i` adjacent to and `std` on the vertices `i` demands an arc to,
which are `adjRow_eq` and `demandRow_eq`. -/

section AsmStamp

variable {B n d W m i : ℕ} {D : Orientation n} {DO DT OO OT : ℕ → ℕ} {σ : Env}

/-- **One vertex's turn's two stamps.** -/
theorem asmStamp_run {b : ℕ} {gsta gstd : ℕ → ℕ}
    (hB1 : 1 < B) (hnB : n < B) (hbB : b < B) (hmB : m < B) (hi : i < n)
    (hcsr : InCsr D m DO DT) (hdeg : D.InDegLE d) (hmW : m ≤ W)
    (hbo : Blocks "ooff" "otg" n W m OO OT σ)
    (hiv : σ.vars "i" = i) (harr : NestArr n W DO DT OO OT σ)
    (hsta : σ.arrs "sta" = arrOf n gsta) (hstd : σ.arrs "std" = arrOf n gstd) :
    ∃ σ' K, Run B (RamAugment.asmStamp b) σ σ' K ∧
      K ≤ 14 * (DO (i + 1) - DO i) + 14 * (OO (i + 1) - OO i) +
        (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)),
          (14 * (OO (OT p + 1) - OO (OT p)) + 14 * d + 35)) + 36 ∧
      Marks "sta" n b (rowTgt DO DT i ∪ rowTgt OO OT i) gsta σ' ∧
      Marks "std" n b (rowAcc OO OT (fun w => rowTgt DO DT w ∪ rowTgt OO OT w) i) gstd σ' ∧
      (∀ a, a ≠ "sta" → a ≠ "std" → σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" → y ≠ "u" →
        σ'.vars y = σ.vars y) := by
  classical
  have hDle : ∀ z, z < n → DO (z + 1) ≤ m := fun z hz => incsr_le hcsr (by omega)
  have hOle : ∀ z, z < n → OO (z + 1) ≤ m := fun z hz => hbo.off_le (by omega)
  have hDd : ∀ z, z < n → DO (z + 1) - DO z ≤ d := fun z hz => by
    have h : DO (z + 1) - DO z = (D.inN ⟨z, hz⟩).card := hcsr.len ⟨z, hz⟩
    rw [h]; exact hdeg ⟨z, hz⟩
  -- the in-block of `i`, stamped into `sta`
  obtain ⟨σ₁, K₁, hr₁, hK₁, hm₁, hfa₁, hfv₁⟩ :=
    stampRow_run (B := B) (o := "doff") (t := "dtg") (x := "i") (j := "j") (jend := "jend")
      (u := "u") (s := "sta") (n := n) (nv := n) (len := W) (v := i) (b := b) (off := DO)
      (tgt := DT) (g := gsta) (σ := σ)
      (by decide) (by decide) (by decide) (by decide) (by decide) hB1 hi (by omega) hbB
      hnB harr.2.1 (hcsr.mono i hi) (le_trans (hDle i hi) hmW)
      (by have := hDle i hi; omega) hiv harr.2.2.1
      (fun p hp => hcsr.target_lt p (lt_of_lt_of_le hp (hDle i hi))) hsta
  obtain ⟨g₁, hg₁, hg₁k⟩ := hm₁
  -- the out-block of `i`, stamped into the same array
  obtain ⟨σ₂, K₂, hr₂, hK₂, hm₂, hfa₂, hfv₂⟩ :=
    stampRow_run (B := B) (o := "ooff") (t := "otg") (x := "i") (j := "j") (jend := "jend")
      (u := "u") (s := "sta") (n := n) (nv := n) (len := W) (v := i) (b := b) (off := OO)
      (tgt := OT) (g := g₁) (σ := σ₁)
      (by decide) (by decide) (by decide) (by decide) (by decide) hB1 hi (by omega) hbB hnB
      (by rw [hfa₁ "ooff" (by decide)]; exact harr.2.2.2.1) (hbo.mono i hi)
      (le_trans (hOle i hi) hmW) (by have := hOle i hi; omega)
      (by rw [hfv₁ "i" (by decide) (by decide) (by decide)]; exact hiv)
      (by rw [hfa₁ "otg" (by decide)]; exact harr.2.2.2.2)
      (fun p hp => hbo.target_lt p (by have := hOle i hi; omega)) hg₁
  have hmsta : Marks "sta" n b (rowTgt DO DT i ∪ rowTgt OO OT i) gsta σ₂ :=
    Marks.trans hg₁k hm₂
  -- the nested walk into `std`
  obtain ⟨σ₃, K₃, hr₃, hK₃, hm₃, hfa₃, hfv₃⟩ :=
    stampNest_run (B := B) (o := "ooff") (t := "otg") (x := "i") (j := "j") (jend := "jend")
      (w := "w") (s := "std")
      (inner := .seq (RamAugment.blockScan "doff" "dtg" "w" "q" "qe" "u"
          (.store "std" (.var "u") (.lit b)))
        (RamAugment.blockScan "ooff" "otg" "w" "q" "qe" "u"
          (.store "std" (.var "u") (.lit b))))
      (n := n) (nv := n) (len := W) (v := i) (b := b) (off := OO) (tgt := OT) (g := gstd)
      (ic := fun z => 14 * (DO (z + 1) - DO z) + 14 * (OO (z + 1) - OO z) + 24)
      (fs := fun w => rowTgt DO DT w ∪ rowTgt OO OT w) (σ := σ₂)
      (by decide) (by decide) (by decide) (by decide) (by decide) hB1 hi (by omega) hnB
      (by rw [hfa₂ "ooff" (by decide), hfa₁ "ooff" (by decide)]; exact harr.2.2.2.1)
      (hbo.mono i hi) (le_trans (hOle i hi) hmW) (by have := hOle i hi; omega)
      (by rw [hfv₂ "i" (by decide) (by decide) (by decide),
            hfv₁ "i" (by decide) (by decide) (by decide)]; exact hiv)
      (by rw [hfa₂ "otg" (by decide), hfa₁ "otg" (by decide)]; exact harr.2.2.2.2)
      (fun p hp => hbo.target_lt p (by have := hOle i hi; omega))
      (by rw [hfa₂ "std" (by decide), hfa₁ "std" (by decide)]; exact hstd)
      (by
        intro τ z h hfrτ hwz hzn hst
        obtain ⟨τ₁, L₁, hs₁, hL₁, hn₁, hna₁, hnv₁⟩ :=
          stampRow_run (B := B) (o := "doff") (t := "dtg") (x := "w") (j := "q")
            (jend := "qe") (u := "u") (s := "std") (n := n) (nv := n) (len := W) (v := z)
            (b := b) (off := DO) (tgt := DT) (g := h) (σ := τ)
            (by decide) (by decide) (by decide) (by decide) (by decide) hB1 hzn (by omega)
            hbB hnB
            (by rw [hfrτ "doff" (by decide), hfa₂ "doff" (by decide),
                  hfa₁ "doff" (by decide)]; exact harr.2.1)
            (hcsr.mono z hzn) (le_trans (hDle z hzn) hmW) (by have := hDle z hzn; omega) hwz
            (by rw [hfrτ "dtg" (by decide), hfa₂ "dtg" (by decide),
                  hfa₁ "dtg" (by decide)]; exact harr.2.2.1)
            (fun p hp => hcsr.target_lt p (lt_of_lt_of_le hp (hDle z hzn))) hst
        obtain ⟨h₁, hh₁, hh₁k⟩ := hn₁
        obtain ⟨τ₂, L₂, hs₂, hL₂, hn₂, hna₂, hnv₂⟩ :=
          stampRow_run (B := B) (o := "ooff") (t := "otg") (x := "w") (j := "q")
            (jend := "qe") (u := "u") (s := "std") (n := n) (nv := n) (len := W) (v := z)
            (b := b) (off := OO) (tgt := OT) (g := h₁) (σ := τ₁)
            (by decide) (by decide) (by decide) (by decide) (by decide) hB1 hzn (by omega)
            hbB hnB
            (by rw [hna₁ "ooff" (by decide), hfrτ "ooff" (by decide),
                  hfa₂ "ooff" (by decide), hfa₁ "ooff" (by decide)]; exact harr.2.2.2.1)
            (hbo.mono z hzn) (le_trans (hOle z hzn) hmW) (by have := hOle z hzn; omega)
            (by rw [hnv₁ "w" (by decide) (by decide) (by decide)]; exact hwz)
            (by rw [hna₁ "otg" (by decide), hfrτ "otg" (by decide),
                  hfa₂ "otg" (by decide), hfa₁ "otg" (by decide)]; exact harr.2.2.2.2)
            (fun p hp => hbo.target_lt p (by have := hOle z hzn; omega)) hh₁
        refine ⟨τ₂, L₁ + L₂, hs₁.seq hs₂,
          (by show L₁ + L₂ ≤ 14 * (DO (z + 1) - DO z) + 14 * (OO (z + 1) - OO z) + 24
              omega), Marks.trans hh₁k hn₂,
          fun a ha => by rw [hna₂ a ha, hna₁ a ha], ?_, ?_⟩
        · rw [hnv₂ "j" (by decide) (by decide) (by decide),
            hnv₁ "j" (by decide) (by decide) (by decide)]
        · rw [hnv₂ "jend" (by decide) (by decide) (by decide),
            hnv₁ "jend" (by decide) (by decide) (by decide)])
  have hcost : K₁ + (K₂ + K₃) ≤ 14 * (DO (i + 1) - DO i) + 14 * (OO (i + 1) - OO i) +
      (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)),
        (14 * (OO (OT p + 1) - OO (OT p)) + 14 * d + 35)) + 36 := by
    have hK₃' : K₃ ≤ (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)),
        (14 * (OO (OT p + 1) - OO (OT p)) + 14 * d + 35)) + 12 := by
      refine le_trans hK₃ (Nat.add_le_add_right (Finset.sum_le_sum fun p hp => ?_) 12)
      rw [Finset.mem_Ico] at hp
      have hpm : p < m := lt_of_lt_of_le hp.2 (hOle i hi)
      have := hDd (OT p) (hbo.target_lt p hpm)
      omega
    omega
  exact ⟨σ₃, K₁ + (K₂ + K₃), hr₁.seq (hr₂.seq hr₃), hcost,
    hmsta.of_eq (hfa₃ "sta" (by decide)), hm₃,
    fun a h1 h2 => by rw [hfa₃ a h2, hfa₂ a h1, hfa₁ a h1],
    fun y h1 h2 h3 h4 h5 h6 => by
      rw [hfv₃ y (by
          simp [RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.wvars, h1, h2, h3, h4, h5,
            h6]),
        hfv₂ y h1 h2 h6, hfv₁ y h1 h2 h6]⟩

/-- **The assembly's duplicate stamps, cleared.** The two lists the
guard stamps — the transitive candidates, walked as the in-block of the
in-block, and the engine's own in-block — walked again at the literal
zero. -/
theorem asmClearE_run {me : ℕ} {Eo : Orientation n} {IO IT gste : ℕ → ℕ}
    (hB1 : 1 < B) (hnB : n < B) (hmB : m < B) (hmeB : me < B) (hi : i < n)
    (hcsr : InCsr D m DO DT) (hdeg : D.InDegLE d) (hmW : m ≤ W)
    (hE : InCsr Eo me IO IT) (hmeW : me ≤ W)
    (hiv : σ.vars "i" = i) (harr : NestArr n W DO DT OO OT σ)
    (hioff : σ.arrs "ioff" = arrOf (n + 1) IO) (hitg : σ.arrs "itg" = arrOf W IT)
    (hste : σ.arrs "ste" = arrOf n gste) :
    ∃ σ' K, Run B RamAugment.asmClearE σ σ' K ∧
      K ≤ (14 * d + 23) * (DO (i + 1) - DO i) + 14 * (IO (i + 1) - IO i) + 24 ∧
      Marks "ste" n 0
        (rowAcc DO DT (fun w => rowTgt DO DT w) i ∪ rowTgt IO IT i) gste σ' ∧
      (∀ a, a ≠ "ste" → σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" → y ≠ "u" →
        σ'.vars y = σ.vars y) := by
  classical
  have hDle : ∀ z, z < n → DO (z + 1) ≤ m := fun z hz => incsr_le hcsr (by omega)
  have hIle : ∀ z, z < n → IO (z + 1) ≤ me := fun z hz => incsr_le hE (by omega)
  obtain ⟨σ₁, K₁, hr₁, hK₁, hm₁, hfa₁, hfv₁⟩ :=
    stampNest_run (B := B) (o := "doff") (t := "dtg") (x := "i") (j := "j") (jend := "jend")
      (w := "w") (s := "ste")
      (inner := RamAugment.blockScan "doff" "dtg" "w" "q" "qe" "u"
        (.store "ste" (.var "u") (.lit 0)))
      (n := n) (nv := n) (len := W) (v := i) (b := 0) (off := DO) (tgt := DT) (g := gste)
      (ic := fun _ => 14 * d + 12) (fs := fun w => rowTgt DO DT w) (σ := σ)
      (by decide) (by decide) (by decide) (by decide) (by decide) hB1 hi (by omega) hnB
      harr.2.1 (hcsr.mono i hi) (le_trans (hDle i hi) hmW) (by have := hDle i hi; omega)
      hiv harr.2.2.1 (fun p hp => hcsr.target_lt p (lt_of_lt_of_le hp (hDle i hi))) hste
      (by
        intro τ z h hfrτ hwz hzn hst
        obtain ⟨τ', K', hr, hK', hm', hfa', hfv'⟩ :=
          stampRow_run (B := B) (o := "doff") (t := "dtg") (x := "w") (j := "q")
            (jend := "qe") (u := "u") (s := "ste") (n := n) (nv := n) (len := W) (v := z)
            (b := 0) (off := DO) (tgt := DT) (g := h) (σ := τ)
            (by decide) (by decide) (by decide) (by decide) (by decide) hB1 hzn
            (by omega) (by omega) hnB
            (by rw [hfrτ "doff" (by decide)]; exact harr.2.1) (hcsr.mono z hzn)
            (le_trans (hDle z hzn) hmW) (by have := hDle z hzn; omega) hwz
            (by rw [hfrτ "dtg" (by decide)]; exact harr.2.2.1)
            (fun p hp => hcsr.target_lt p (lt_of_lt_of_le hp (hDle z hzn))) hst
        have hd' : DO (z + 1) - DO z ≤ d := by
          have hc : DO (z + 1) - DO z = (D.inN ⟨z, hzn⟩).card := hcsr.len ⟨z, hzn⟩
          rw [hc]; exact hdeg ⟨z, hzn⟩
        refine ⟨τ', K', hr, ?_, hm', hfa',
          hfv' "j" (by decide) (by decide) (by decide),
          hfv' "jend" (by decide) (by decide) (by decide)⟩
        show K' ≤ 14 * d + 12
        omega)
  obtain ⟨g₁, hg₁, hg₁k⟩ := hm₁
  obtain ⟨σ₂, K₂, hr₂, hK₂, hm₂, hfa₂, hfv₂⟩ :=
    stampRow_run (B := B) (o := "ioff") (t := "itg") (x := "i") (j := "j") (jend := "jend")
      (u := "u") (s := "ste") (n := n) (nv := n) (len := W) (v := i) (b := 0) (off := IO)
      (tgt := IT) (g := g₁) (σ := σ₁)
      (by decide) (by decide) (by decide) (by decide) (by decide) hB1 hi (by omega)
      (by omega) hnB (by rw [hfa₁ "ioff" (by decide)]; exact hioff) (hE.mono i hi)
      (le_trans (hIle i hi) hmeW) (by have := hIle i hi; omega)
      (by rw [hfv₁ "i" (by simp [RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.wvars])]
          exact hiv)
      (by rw [hfa₁ "itg" (by decide)]; exact hitg)
      (fun p hp => hE.target_lt p (lt_of_lt_of_le hp (hIle i hi))) hg₁
  refine ⟨σ₂, K₁ + K₂, hr₁.seq hr₂, ?_, Marks.trans hg₁k hm₂,
    fun a ha => by rw [hfa₂ a ha, hfa₁ a ha],
    fun y h1 h2 h3 h4 h5 h6 => by
      rw [hfv₂ y h1 h2 h6,
        hfv₁ y (by
          simp [RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.wvars, h1, h2, h3, h4, h5,
            h6])]⟩
  have hK₁' : K₁ ≤ (14 * d + 23) * (DO (i + 1) - DO i) + 12 := by
    refine le_trans hK₁ ?_
    rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
    exact le_of_eq (by ring)
  omega

end AsmStamp

/-! ### The elimination, with the rank bound *and* the certificate

`RamAugment.ElimAvail` hands the engine's `RamElim.Implements`, whose
postcondition `RamElim.ElimMem` carries the certificate but **not** the
bound `∀ v < n, R v < n` — and the assembly reads `rnk[u]`, so without
it there is no run. `RamDriverCompose.elimRank_spec` keeps the bound,
but post-processes to `RamElim.ElimPost`, which *drops* the certificate
(`min_deg` and `attained` are nowhere in it) and `RamAugment.AugMem`
asks for the certificate. So the engine's five phase specs are
re-sequenced here once more, at `ns = RamAugment.fratSlots D`, against
the same four predicates and with the one postcondition that has both.

**Defect record.** The proper repair is one conjunct in
`RamElim.ElimMem`, which `RamElim.implements`'s own last phase has in
hand. The engines are frozen for this wave, so it is done here instead:
a wave that may edit `RamElim` should add the conjunct there and delete
**both** this bridge and `RamDriverCompose.elimRank_spec`, which exist
for the same reason and die together. -/

/-- **The elimination, keeping the rank bound its own surface drops.** -/
theorem elimCert_spec {B n ns W : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B) (hMB : ∀ z < n, M z < B)
    (hW : ns ≤ W) :
    Spec B (ElimPre n ns W O T M) elimCom
      (fun _ σ' => ElimMem G M ns W σ' σ' ∧
        ∃ R, σ'.arrs "rnk" = arrOf n R ∧ (∀ v < n, R v < n))
      (elimCost n ns) := by
  have hDlt : ∀ v < n, RamElim.adeg G M v < n := fun v hv => by
    rw [RamElim.adeg_eq hv]; exact RamElim.card_nbrsIn_lt _ _
  have w1 : Spec B (ElimPre n ns W O T M) RamElim.initDeg
      (fun _ σ' => RamElim.AfterDeg n ns W G O T M σ') (48 * n + 44 * ns + 10) := by
    intro σ hσ
    obtain ⟨hn, hoff, htgt, halv, hdeg0, helm, hrnk, hidg, hbh, hbv, hbn, hioff, hifl,
      hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨hI, hi⟩, -, hfa, -, -⟩ :=
      (RamElim.initDeg_spec B n ns G O T M hcsr (by omega) (by omega) hMB).frame σ
        ⟨hn, hoff, htgt, halv, hdeg0⟩
    obtain ⟨hn', hoff', htgt', halv', -, g, hdegg, hg⟩ := hI
    obtain ⟨e, he1, he2⟩ := helm
    obtain ⟨r, hr1⟩ := hrnk
    obtain ⟨d, hd1⟩ := hidg
    obtain ⟨bh, hbh1, hbh2⟩ := hbh
    obtain ⟨bv, hbv1⟩ := hbv
    obtain ⟨bn, hbn1⟩ := hbn
    obtain ⟨io, hio1⟩ := hioff
    obtain ⟨fl, hfl1⟩ := hifl
    obtain ⟨tg, htg1⟩ := hitg
    exact ⟨σ', hrun, hn', hoff', htgt', halv',
      by rw [hdegg, RamDriverOrder.arrOf_congr (fun j hj => hg j (by rw [hi]; exact hj))],
      ⟨e, by rw [hfa "elm" (by decide)]; exact he1, he2⟩,
      ⟨r, by rw [hfa "rnk" (by decide)]; exact hr1⟩,
      ⟨d, by rw [hfa "idg" (by decide)]; exact hd1⟩,
      ⟨bh, by rw [hfa "bh" (by decide)]; exact hbh1, hbh2⟩,
      ⟨bv, by rw [hfa "bv" (by decide)]; exact hbv1⟩,
      ⟨bn, by rw [hfa "bn" (by decide)]; exact hbn1⟩,
      ⟨io, by rw [hfa "ioff" (by decide)]; exact hio1⟩,
      ⟨fl, by rw [hfa "ifl" (by decide)]; exact hfl1⟩,
      ⟨tg, by rw [hfa "itg" (by decide)]; exact htg1⟩⟩
  have w2 : Spec B (RamElim.AfterDeg n ns W G O T M) RamElim.initBuck
      (fun _ σ' => RamElim.AfterBuck n ns W G O T M σ') (29 * n + 10) := by
    intro σ hσ
    obtain ⟨hn, hoff, htgt, halv, hdeg, helm, hrnk, hidg, hbh, hbv, hbn, hioff, hifl,
      hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨hI, hi⟩, -, hfa, -, -⟩ :=
      (RamElim.initBuck_spec B n W (RamElim.adeg G M) (by omega) hDlt).frame σ
        ⟨hn, hdeg, hbh, hbv, hbn⟩
    obtain ⟨e, he1, he2⟩ := helm
    obtain ⟨r, hr1⟩ := hrnk
    obtain ⟨d, hd1⟩ := hidg
    obtain ⟨io, hio1⟩ := hioff
    obtain ⟨fl, hfl1⟩ := hifl
    obtain ⟨tg, htg1⟩ := hitg
    exact ⟨σ', hrun, hI, hi,
      by rw [hfa "off" (by decide)]; exact hoff,
      by rw [hfa "tgt" (by decide)]; exact htgt,
      by rw [hfa "alv" (by decide)]; exact halv,
      ⟨e, by rw [hfa "elm" (by decide)]; exact he1, he2⟩,
      ⟨r, by rw [hfa "rnk" (by decide)]; exact hr1⟩,
      ⟨d, by rw [hfa "idg" (by decide)]; exact hd1⟩,
      ⟨io, by rw [hfa "ioff" (by decide)]; exact hio1⟩,
      ⟨fl, by rw [hfa "ifl" (by decide)]; exact hfl1⟩,
      ⟨tg, by rw [hfa "itg" (by decide)]; exact htg1⟩⟩
  have w3 : Spec B (RamElim.AfterBuck n ns W G O T M) RamElim.elimLoop
      (fun _ σ' => RamElim.AfterLoop n ns W G O T M σ') (160 * n + 100 * ns + 52) := by
    intro σ hσ
    obtain ⟨hbi, hi, hoff, htgt, halv, helm, hrnk, hidg, hioff, hifl, hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨R, ID, k, hn', hk', hrnk', hidg', hRlt, hcert, hIDc, hpsum⟩, -,
      hfa, -, -⟩ :=
      (RamElim.elimLoop_spec B n ns W G O T M (RamElim.adeg G M) hcsr hB hW hMB
        (fun _ _ => rfl)).frame σ ⟨hbi, hi, hoff, htgt, halv, helm, hrnk, hidg⟩
    obtain ⟨io, hio1⟩ := hioff
    obtain ⟨fl, hfl1⟩ := hifl
    obtain ⟨tg, htg1⟩ := hitg
    exact ⟨σ', hrun, R, ID, k, hn', hk',
      by rw [hfa "off" (by decide)]; exact hoff,
      by rw [hfa "tgt" (by decide)]; exact htgt,
      by rw [hfa "alv" (by decide)]; exact halv,
      hrnk', hidg', hRlt, hcert, hIDc, hpsum,
      ⟨io, by rw [hfa "ioff" (by decide)]; exact hio1⟩,
      ⟨fl, by rw [hfa "ifl" (by decide)]; exact hfl1⟩,
      ⟨tg, by rw [hfa "itg" (by decide)]; exact htg1⟩⟩
  have w4 : Spec B (RamElim.AfterLoop n ns W G O T M) RamElim.offPass
      (fun _ σ' => RamElim.AfterOff n ns W G O T M σ') (24 * n + 12) := by
    intro σ hσ
    obtain ⟨R, ID, k, hn, hk, hoff, htgt, halv, hrnk, hidg, hRlt, hcert, hIDc, hpsum,
      hioff, hifl, hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨hn', hs', hio', hfl'⟩, hfv, hfa, -, -⟩ :=
      (RamElim.offPass_spec B n ID (by omega) (by omega)).frame σ ⟨hn, hidg, hioff, hifl⟩
    obtain ⟨tg, htg1⟩ := hitg
    exact ⟨σ', hrun, R, ID, k, hn', by rw [hfv "kmax" (by decide)]; exact hk,
      by rw [hfa "off" (by decide)]; exact hoff,
      by rw [hfa "tgt" (by decide)]; exact htgt,
      by rw [hfa "alv" (by decide)]; exact halv,
      by rw [hfa "rnk" (by decide)]; exact hrnk,
      hRlt, hcert, hIDc, hpsum, hio', hfl',
      ⟨tg, by rw [hfa "itg" (by decide)]; exact htg1⟩⟩
  have w5 : Spec B (RamElim.AfterOff n ns W G O T M) RamElim.fillPass
      (fun _ σ' => ElimMem G M ns W σ' σ' ∧
        ∃ R, σ'.arrs "rnk" = arrOf n R ∧ (∀ v < n, R v < n))
      (32 * n + 32 * ns + 10) := by
    intro σ hσ
    obtain ⟨R, ID, k, hn, hk, hoff, htgt, halv, hrnk, hRlt, hcert, hIDc, hpsum, hioff,
      hifl, hitg⟩ := hσ
    obtain ⟨g, hioffg, hioffv⟩ := hioff
    obtain ⟨σ', hrun, ⟨IT, hitg', harcs⟩, hfv, hfa, -, -⟩ :=
      (RamElim.fillPass_spec B n ns W G O T M R ID hcsr hB hW hMB hRlt hIDc hpsum).frame σ
        ⟨hn, hoff, htgt, halv, hrnk, hifl, hitg⟩
    have hrnk' : σ'.arrs "rnk" = arrOf n R := by
      rw [hfa "rnk" (by decide)]; exact hrnk
    exact ⟨σ', hrun, ⟨R, RamElim.psum ID, IT, k, RamElim.psum ID n, hrnk',
      by rw [hfv "kmax" (by decide)]; exact hk,
      by rw [hfa "ioff" (by decide), hioffg]
         exact RamDriverOrder.arrOf_congr (fun j hj => hioffv j (by omega)),
      hitg', by omega, ⟨hcert, harcs⟩⟩, R, hrnk', hRlt⟩
  show Spec B (ElimPre n ns W O T M) elimCom _ (600 * n + 600 * ns + 100)
  run_vcg [w1, w2, w3, w4, w5] <;> assumption

/-! ### The assembly's emit walk

`RamAugment.asmEmit act` is three walks under one accounting: the old
in-block, unguarded — its freshness is `incsr_nodup` — then the
transitive candidates as a nested walk of the in-blocks under
`guardAsmTrans_of_emits`, then the engine's own in-block under
`guardAsmIn_of_emits`. The three sets they accumulate union — as
`(Base ∪ T) ∪ F` — to `valSet ((augOr D ρ).inN i)` by `asmRow_eq`,
which is also the capacity all three run inside. -/

/-- The rows of an `InCsr` tile its slot array. -/
theorem incsr_sum_rowLen {n m : ℕ} {D : Orientation n} {IO IT : ℕ → ℕ}
    (h : InCsr D m IO IT) : ∑ i ∈ Finset.range n, (IO (i + 1) - IO i) = m := by
  have key : ∀ k, k ≤ n → ∑ i ∈ Finset.range k, (IO (i + 1) - IO i) = IO k := by
    intro k
    induction k with
    | zero => intro _; simp [h.zero]
    | succ k ih =>
        intro hk
        rw [Finset.sum_range_succ, ih (by omega)]
        have := h.mono k (by omega)
        omega
  rw [key n le_rfl, h.last]

/-- A weight summed over the slot array splits into a sum over each
row. This is `tile_filter_card` for a weight instead of a predicate,
and it is what turns the assembly's per-row cost into a cost over the
whole array. -/
theorem tile_sum {off : ℕ → ℕ} {nv m : ℕ} (hz : off 0 = 0) (hlast : off nv = m)
    (hmono : ∀ i < nv, off i ≤ off (i + 1)) (f : ℕ → ℕ) :
    ∑ p ∈ Finset.range m, f p
      = ∑ u ∈ Finset.range nv, ∑ p ∈ Finset.Ico (off u) (off (u + 1)), f p := by
  have key : ∀ k, k ≤ nv →
      ∑ p ∈ Finset.range (off k), f p
        = ∑ u ∈ Finset.range k, ∑ p ∈ Finset.Ico (off u) (off (u + 1)), f p := by
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
        have hdis : Disjoint (Finset.range (off k)) (Finset.Ico (off k) (off (k + 1))) := by
          rw [Finset.disjoint_left]
          intro a ha ha'
          rw [Finset.mem_range] at ha
          rw [Finset.mem_Ico] at ha'
          omega
        rw [hsplit, Finset.sum_union hdis, ih (by omega), Finset.sum_range_succ]
  rw [← hlast]; exact key nv le_rfl

namespace Demo

-- **the exchange, at the cost it pays for**: the assembly's third
-- stamp walk charges the out-block of every vertex an out-slot names,
-- so its bill is `∑_{p < m} outdeg (OT p)` — which is
-- `∑_u slotCnt OT m u · outdeg u` and, by `slotCnt_out_eq`, the
-- in-degrees against the out-degrees, at most `d · m`
#guard (List.range 4).map (fun p => demoOO (demoOT p + 1) - demoOO (demoOT p)) = [1, 1, 1, 0]

#guard ((List.range 4).map (fun p => demoOO (demoOT p + 1) - demoOO (demoOT p))).sum
  = ((List.range 4).map (fun u => slotCnt demoOT 4 u * (demoOO (u + 1) - demoOO u))).sum

#guard ((List.range 4).map (fun u => slotCnt demoOT 4 u * (demoOO (u + 1) - demoOO u))).sum
  ≤ 2 * 4

-- and `tile_sum`: a weight over the slots is the weights over the rows
#guard ((List.range 4).map (fun p => demoDT p * demoDT p)).sum
  = ((List.range 4).map (fun i =>
      ((List.range (demoDO (i + 1) - demoDO i)).map
        (fun t => demoDT (demoDO i + t) * demoDT (demoDO i + t))).sum)).sum

end Demo

/-- The six arrays and the one scalar the assembly's walks read:
`NestArr`'s four, and the engine's own in-blocks. -/
def AsmArr (n W : ℕ) (DO DT OO OT IO IT : ℕ → ℕ) (τ : Env) : Prop :=
  NestArr n W DO DT OO OT τ ∧ τ.arrs "ioff" = arrOf (n + 1) IO ∧
    τ.arrs "itg" = arrOf W IT

namespace AsmArr

variable {n W : ℕ} {DO DT OO OT IO IT : ℕ → ℕ} {τ τ' : Env}

theorem setVar (h : AsmArr n W DO DT OO OT IO IT τ) (y : String) (hy : y ≠ "n") (x : ℕ) :
    AsmArr n W DO DT OO OT IO IT (τ.setVar y x) :=
  ⟨h.1.setVar y hy x, by simpa using h.2.1, by simpa using h.2.2⟩

theorem setArr (h : AsmArr n W DO DT OO OT IO IT τ) {a : String} (h1 : a ≠ "doff")
    (h2 : a ≠ "dtg") (h3 : a ≠ "ooff") (h4 : a ≠ "otg") (h5 : a ≠ "ioff") (h6 : a ≠ "itg")
    (p x : ℕ) : AsmArr n W DO DT OO OT IO IT (τ.setArr a p x) :=
  ⟨h.1.setArr h1 h2 h3 h4 p x,
    by rw [arrs_setArr, if_neg (Ne.symm h5)]; exact h.2.1,
    by rw [arrs_setArr, if_neg (Ne.symm h6)]; exact h.2.2⟩

/-- The relation crosses any command that leaves the six arrays and the
scalar `"n"` alone — which every accounting's action does. -/
theorem of_frame {a₁ a₂ : String} (h : AsmArr n W DO DT OO OT IO IT τ)
    (ha₁ : ReadArrs a₁) (ha₂ : ReadArrs a₂)
    (hv : ∀ y, y ≠ "c" → τ'.vars y = τ.vars y)
    (hfa : ∀ a, a ≠ a₁ → a ≠ a₂ → τ'.arrs a = τ.arrs a) :
    AsmArr n W DO DT OO OT IO IT τ' :=
  ⟨h.1.of_frame ha₁ ha₂ hv hfa,
    by rw [hfa "ioff" (Ne.symm ha₁.2.2.2.2.2.2.2.2.2.1)
      (Ne.symm ha₂.2.2.2.2.2.2.2.2.2.1)]; exact h.2.1,
    by rw [hfa "itg" (Ne.symm ha₁.2.2.2.2.2.2.2.2.2.2)
      (Ne.symm ha₂.2.2.2.2.2.2.2.2.2.2)]; exact h.2.2⟩

/-- And it crosses the round's own stamping walks, which write nothing
but the three stamp arrays. -/
theorem of_stampFrame (h : AsmArr n W DO DT OO OT IO IT τ)
    (hn : τ'.vars "n" = τ.vars "n")
    (hfa : ∀ a, a ≠ "sta" → a ≠ "std" → a ≠ "ste" → τ'.arrs a = τ.arrs a) :
    AsmArr n W DO DT OO OT IO IT τ' :=
  ⟨⟨by rw [hn]; exact h.1.1,
      by rw [hfa "doff" (by decide) (by decide) (by decide)]; exact h.1.2.1,
      by rw [hfa "dtg" (by decide) (by decide) (by decide)]; exact h.1.2.2.1,
      by rw [hfa "ooff" (by decide) (by decide) (by decide)]; exact h.1.2.2.2.1,
      by rw [hfa "otg" (by decide) (by decide) (by decide)]; exact h.1.2.2.2.2⟩,
    by rw [hfa "ioff" (by decide) (by decide) (by decide)]; exact h.2.1,
    by rw [hfa "itg" (by decide) (by decide) (by decide)]; exact h.2.2⟩

/-- The out-block structure is a statement about two of the six
arrays. -/
theorem blocks {m : ℕ} {σ : Env} (hbo : Blocks "ooff" "otg" n W m OO OT σ)
    (h : AsmArr n W DO DT OO OT IO IT τ) : Blocks "ooff" "otg" n W m OO OT τ :=
  hbo.of_eq (by rw [h.1.2.2.2.1, hbo.offArr]) (by rw [h.1.2.2.2.2, hbo.tgtArr])

end AsmArr

section AsmEmit

variable {B n d W m me Ka i : ℕ} {a₁ a₂ : String} {act : Com}
variable {D : Orientation n} {ρ : Fin n → ℕ} {DO DT OO OT IO IT R : ℕ → ℕ}
variable {Acc : Finset ℕ → Env → Prop} {σ : Env}

/-- **The assembly's three lists, emitted.** The old in-block runs
unguarded; the transitive candidates and the engine's own in-block run
under the two guards, sharing the stamp `ste` and the base the first
list already handed the accounting. What reaches the action is
`valSet ((augOr D ρ).inN i)`, once each, by `asmRow_eq`. -/
theorem asmEmit_run
    (ha₁ : ReadArrs a₁) (ha₂ : ReadArrs a₂)
    (hactw : ∀ a, a ≠ a₁ → a ≠ a₂ → a ∉ act.warrs)
    (hB1 : 1 < B) (hnB : n < B) (hi : i < n)
    (hcsr : InCsr D m DO DT) (hdeg : D.InDegLE d) (hmW : m ≤ W)
    (hE : InCsr (RamElim.ElimCert.elimOr (fratGraph D) ρ) me IO IT) (hmeW : me ≤ W)
    (hWB : W < B)
    (hρ : ∀ v : Fin n, ρ v = R (v : ℕ)) (hRn : ∀ v, v < n → R v < n)
    (hiv : σ.vars "i" = i) (harr : AsmArr n W DO DT OO OT IO IT σ)
    (hrnk : σ.arrs "rnk" = arrOf n R)
    (hsta : Marks "sta" n 1 (valSet (RamAugment.adjSet D ⟨i, hi⟩)) (fun _ => 0) σ)
    (hstd : Marks "std" n 1 (valSet (RamAugment.demandOut D ⟨i, hi⟩)) (fun _ => 0) σ)
    (hste : Marks "ste" n 1 (∅ : Finset ℕ) (fun _ => 0) σ)
    (hAccSt : ∀ S τ p x, Acc S τ → Acc S (τ.setArr "ste" p x))
    (hAccI : ∀ S τ, Acc S τ → τ.vars "i" = i)
    (hAccV : ∀ S τ (y : String) (z : ℕ),
      (y = "j" ∨ y = "jend" ∨ y = "w" ∨ y = "q" ∨ y = "qe" ∨ y = "u") → Acc S τ →
      Acc S (τ.setVar y z))
    (hAcc : Emits B n Ka a₁ a₂ act (valSet ((RamAugment.augOr D ρ).inN ⟨i, hi⟩)) Acc)
    (hA0 : Acc ∅ σ) :
    ∃ σ' K, Run B (RamAugment.asmEmit act) σ σ' K ∧
      K ≤ ((Ka + 35) * d + Ka + 34) * (DO (i + 1) - DO i)
          + (Ka + 24) * (IO (i + 1) - IO i) + 36 ∧
      Acc (valSet ((RamAugment.augOr D ρ).inN ⟨i, hi⟩)) σ' ∧
      AsmArr n W DO DT OO OT IO IT σ' ∧
      σ'.arrs "rnk" = arrOf n R ∧
      Marks "sta" n 1 (valSet (RamAugment.adjSet D ⟨i, hi⟩)) (fun _ => 0) σ' ∧
      Marks "std" n 1 (valSet (RamAugment.demandOut D ⟨i, hi⟩)) (fun _ => 0) σ' ∧
      (∃ S, S ⊆ rowAcc DO DT (fun w => rowTgt DO DT w) i ∪ rowTgt IO IT i ∧
        Marks "ste" n 1 S (fun _ => 0) σ') ∧
      (∀ a, a ≠ a₁ → a ≠ a₂ → a ≠ "ste" → σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" → y ≠ "u" → y ≠ "c" →
        σ'.vars y = σ.vars y) := by
  classical
  set A : Finset ℕ := valSet (RamAugment.adjSet D ⟨i, hi⟩) with hAdef
  set Dm : Finset ℕ := valSet (RamAugment.demandOut D ⟨i, hi⟩) with hDmdef
  set Cap : Finset ℕ := valSet ((RamAugment.augOr D ρ).inN ⟨i, hi⟩) with hCapdef
  set Base : Finset ℕ := rowTgt DO DT i with hBasedef
  set feT : ℕ → Finset ℕ := fun y => if y ∈ A then ∅ else
    if y ∈ Dm ∧ ¬ R y < R i then ∅ else {y} with hfeT
  set feF : ℕ → Finset ℕ := fun y => if y ∈ A then ∅ else {y} with hfeF
  set T : Finset ℕ := rowAcc DO DT (fun w => rowAcc DO DT feT w) i with hTdef
  set F : Finset ℕ := rowAcc IO IT feF i with hFdef
  have hunion : Base ∪ T ∪ F = Cap := by
    rw [hBasedef, hTdef, hFdef, hfeT, hfeF, hAdef, hDmdef, hCapdef]
    exact asmRow_eq hcsr hE hi hρ
  have hDle : ∀ z, z < n → DO (z + 1) ≤ m := fun z hz => incsr_le hcsr (by omega)
  have hIle : ∀ z, z < n → IO (z + 1) ≤ me := fun z hz => incsr_le hE (by omega)
  have hDd : ∀ z, z < n → DO (z + 1) - DO z ≤ d := fun z hz => by
    have h : DO (z + 1) - DO z = (D.inN ⟨z, hz⟩).card := hcsr.len ⟨z, hz⟩
    rw [h]; exact hdeg ⟨z, hz⟩
  have hBcap : Base ⊆ Cap := by
    rw [← hunion]; exact fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hTcap : T ⊆ Cap := by
    rw [← hunion]; exact fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hFcap : F ⊆ Cap := by
    rw [← hunion]; exact fun x hx => Finset.mem_union_right _ hx
  have hBA : Base ⊆ A := by
    rw [hBasedef, hAdef, rowTgt_eq_inN hcsr hi, adjSet_eq, valSet_union]
    exact fun x hx => Finset.mem_union_left _ hx
  -- the array facts the walks carry along in the accounting
  set P : Env → Prop := fun τ => AsmArr n W DO DT OO OT IO IT τ ∧
    Marks "std" n 1 Dm (fun _ => 0) τ ∧ τ.arrs "rnk" = arrOf n R with hPdef
  have hPfr : ∀ τ τ', P τ → (∀ y, y ≠ "c" → τ'.vars y = τ.vars y) →
      (∀ a, a ≠ a₁ → a ≠ a₂ → τ'.arrs a = τ.arrs a) → P τ' := by
    rintro τ τ' ⟨h1, h2, h3⟩ hv hfa
    exact ⟨h1.of_frame ha₁ ha₂ hv hfa,
      h2.of_eq (hfa "std" (Ne.symm ha₁.2.2.2.2.2.2.1) (Ne.symm ha₂.2.2.2.2.2.2.1)),
      by rw [hfa "rnk" (Ne.symm ha₁.2.2.2.2.2.2.2.2.1)
        (Ne.symm ha₂.2.2.2.2.2.2.2.2.1)]; exact h3⟩
  have hPv : ∀ (τ : Env) (y : String) (z : ℕ), y ≠ "n" → P τ → P (τ.setVar y z) := by
    rintro τ y z hy ⟨h1, h2, h3⟩
    exact ⟨h1.setVar y hy z, h2.setVar y z, by rw [arrs_setVar]; exact h3⟩
  have hPste : ∀ (τ : Env) (p x : ℕ), P τ → P (τ.setArr "ste" p x) := by
    rintro τ p x ⟨h1, h2, h3⟩
    exact ⟨h1.setArr (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) p x,
      h2.setArr_of_ne (by decide) p x, by rw [arrs_setArr, if_neg (by decide)]; exact h3⟩
  have hAccP : Emits B n Ka a₁ a₂ act Cap (fun S τ => Acc S τ ∧ P τ) := hAcc.and hPfr
  have hAccPSt : ∀ S τ p x, (Acc S τ ∧ P τ) → (Acc S (τ.setArr "ste" p x) ∧
      P (τ.setArr "ste" p x)) := fun S τ p x h => ⟨hAccSt S τ p x h.1, hPste τ p x h.2⟩
  have hAccPI : ∀ S τ, (Acc S τ ∧ P τ) → τ.vars "i" = i := fun S τ h => hAccI S τ h.1
  have hAccPV : ∀ S τ (y : String) (z : ℕ),
      (y = "j" ∨ y = "jend" ∨ y = "w" ∨ y = "q" ∨ y = "qe" ∨ y = "u") →
      (Acc S τ ∧ P τ) → (Acc S (τ.setVar y z) ∧ P (τ.setVar y z)) := by
    rintro S τ y z hy ⟨h1, h2⟩
    exact ⟨hAccV S τ y z hy h1,
      hPv τ y z (by rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) h2⟩
  -- **the old in-block**, unguarded: a repeat would be two slots with the same target
  obtain ⟨σ₁, K₁, hr₁, hK₁, hA₁, hfv₁, hfa₁⟩ :=
    emitAllRow_run (B := B) (o := "doff") (t := "dtg") (x := "i") (j := "j") (jend := "jend")
      (a₁ := a₁) (a₂ := a₂) (act := act) (n := n) (nv := n) (len := W) (v := i) (Ka := Ka)
      (off := DO) (tgt := DT) (Acc := fun S τ => Acc S τ ∧ P τ) (E₀ := ∅) (Cap := Cap)
      (σ := σ)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hB1 hi (by omega) hnB harr.1.2.1 (hcsr.mono i hi) (le_trans (hDle i hi) hmW)
      (by have := hDle i hi; omega) hiv
      (fun _ _ h => h.2.1.1.2.2.1)
      (fun p hp => hcsr.target_lt p (lt_of_lt_of_le hp (hDle i hi)))
      (fun S τ y z hy h => hAccPV S τ y z (by
        rcases hy with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) h)
      (by
        intro p h₁ h₂ hc
        rw [Finset.empty_union, mem_accUpto] at hc
        obtain ⟨s, hs₁, hs₂, hs₃⟩ := hc
        have := incsr_nodup hcsr hi hs₁ (by omega) h₁ h₂ (Finset.mem_singleton.1 hs₃).symm
        omega)
      (fun p h₁ h₂ => hBcap (by rw [hBasedef]; exact mem_rowTgt.2 ⟨p, h₁, h₂, rfl⟩))
      hAccP ⟨hA0, harr, hstd, hrnk⟩
  have hP₁ : P σ₁ := hA₁.2
  have hiv₁ : σ₁.vars "i" = i := by
    rw [hfv₁ "i" (by decide) (by decide) (by decide) (by decide)]; exact hiv
  have hsta₁ : Marks "sta" n 1 A (fun _ => 0) σ₁ :=
    hsta.of_eq (hfa₁ "sta" (Ne.symm ha₁.2.2.2.2.2.1) (Ne.symm ha₂.2.2.2.2.2.1))
  have hste₁ : Marks "ste" n 1 (∅ : Finset ℕ) (fun _ => 0) σ₁ :=
    hste.of_eq (hfa₁ "ste" (Ne.symm ha₁.2.2.2.2.2.2.2.1) (Ne.symm ha₂.2.2.2.2.2.2.2.1))
  -- **the transitive candidates**, a nested walk under the arc rule
  have hgT := guardAsmTrans_of_emits (B := B) (n := n) (Ka := Ka) (i := i)
      (a₁ := a₁) (a₂ := a₂) (act := act) (Acc := fun S τ => Acc S τ ∧ P τ)
      (A := A) (Dm := Dm) (Base := Base) (Cap := Cap) (R := R)
      ha₁.2.2.2.2.2.2.2.1 ha₂.2.2.2.2.2.2.2.1 ha₁.2.2.2.2.2.1 ha₂.2.2.2.2.2.1
      ha₁.2.2.2.2.2.2.1 ha₂.2.2.2.2.2.2.1 ha₁.2.2.2.2.2.2.2.2.1 ha₂.2.2.2.2.2.2.2.2.1
      hB1 hnB hi hRn hBA hAccPSt hAccPI hAccP
  obtain ⟨σ₂, K₂, hr₂, hK₂, hJ₂, hfv₂⟩ :=
    emitNest_run (B := B) (o := "doff") (t := "dtg") (o2 := "doff") (t2 := "dtg")
      (n := n) (nv := n) (len := W) (nv2 := n) (len2 := W) (v := i) (Kg := Ka + 24)
      (dd := d) (off := DO) (tgt := DT) (off2 := DO) (tgt2 := DT) (fe := feT)
      (J := fun S τ => Marks "ste" n 1 S (fun _ => 0) τ ∧ Marks "sta" n 1 A (fun _ => 0) τ ∧
        Marks "std" n 1 Dm (fun _ => 0) τ ∧ τ.arrs "rnk" = arrOf n R ∧
        (Acc (Base ∪ S) τ ∧ P τ))
      (E₀ := ∅) (Cap := Cap) (σ := σ₁)
      hB1 hnB hi (by omega) hP₁.1.1.2.1 (hcsr.mono i hi) (le_trans (hDle i hi) hmW)
      (by have := hDle i hi; omega) hiv₁
      (fun _ _ h => h.2.2.2.2.2.1.1.2.2.1)
      (fun p hp => hcsr.target_lt p (lt_of_lt_of_le hp (hDle i hi))) le_rfl
      (fun _ _ h => h.2.2.2.2.2.1.1.2.1) (fun _ _ h => h.2.2.2.2.2.1.1.2.2.1)
      (fun z hz => hcsr.mono z hz) (fun z hz => le_trans (hDle z hz) hmW)
      (fun z hz => by have := hDle z hz; omega)
      (fun z hz q hq => hcsr.target_lt q (lt_of_lt_of_le hq (hDle z hz)))
      (fun z hz => hDd z hz)
      (fun S τ y z hy h => ⟨h.1.setVar y z, h.2.1.setVar y z, h.2.2.1.setVar y z,
        by rw [arrs_setVar]; exact h.2.2.2.1,
        hAccPV _ τ y z (by
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) h.2.2.2.2⟩)
      (fun p h₁ h₂ => Finset.Subset.trans
        (by rw [hTdef] at hTcap; exact subset_rowAcc h₁ h₂) hTcap)
      hgT
      ⟨hste₁, hsta₁, hP₁.2.1, hP₁.2.2,
        by rw [Finset.union_empty]; exact (by rw [Finset.empty_union] at hA₁; exact hA₁.1),
        hP₁⟩
  have hP₂ : P σ₂ := hJ₂.2.2.2.2.2
  have hiv₂ : σ₂.vars "i" = i := by
    rw [hfv₂ "i" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hiv₁
  -- **the engine's own in-block**, minus what `D` already carries
  have hgF := guardAsmIn_of_emits (B := B) (n := n) (Ka := Ka)
      (a₁ := a₁) (a₂ := a₂) (act := act) (Acc := fun S τ => Acc S τ ∧ P τ)
      (A := A) (Base := Base) (Cap := Cap)
      ha₁.2.2.2.2.2.2.2.1 ha₂.2.2.2.2.2.2.2.1 ha₁.2.2.2.2.2.1 ha₂.2.2.2.2.2.1
      hB1 hnB hBA hAccPSt hAccP
  obtain ⟨σ₃, K₃, hr₃, hK₃, hJ₃, hfv₃⟩ :=
    emitRow_run (B := B) (o := "ioff") (t := "itg") (x := "i") (j := "j") (jend := "jend")
      (n := n) (nv := n) (len := W) (v := i) (Kg := Ka + 13) (off := IO) (tgt := IT)
      (fe := feF)
      (J := fun S τ => Marks "ste" n 1 S (fun _ => 0) τ ∧ Marks "sta" n 1 A (fun _ => 0) τ ∧
        (Acc (Base ∪ S) τ ∧ P τ))
      (E₀ := T) (Cap := Cap) (σ := σ₂)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hB1 hi (by omega) hnB hP₂.1.2.1 (hE.mono i hi) (le_trans (hIle i hi) hmeW)
      (by have := hIle i hi; omega) hiv₂
      (fun _ _ h => h.2.2.2.1.2.2)
      (fun p hp => hE.target_lt p (lt_of_lt_of_le hp (hIle i hi)))
      (fun S τ y z hy h => ⟨h.1.setVar y z, h.2.1.setVar y z,
        hAccPV _ τ y z (by
          rcases hy with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) h.2.2⟩)
      (fun p h₁ h₂ => Finset.Subset.trans
        (by rw [hFdef] at hFcap; exact subset_rowAcc h₁ h₂) hFcap)
      hgF
      ⟨by rw [Finset.empty_union] at hJ₂; exact hJ₂.1, hJ₂.2.1,
        by rw [Finset.empty_union] at hJ₂; exact hJ₂.2.2.2.2.1, hP₂⟩
  have hP₃ : P σ₃ := hJ₃.2.2.2
  -- the three sets union to the block of `augOr`
  have hAccFin : Acc Cap σ₃ := by
    have h := hJ₃.2.2.1
    rw [← Finset.union_assoc, hunion] at h
    exact h
  have hsub : T ∪ F ⊆ rowAcc DO DT (fun w => rowTgt DO DT w) i ∪ rowTgt IO IT i := by
    have hTs : T ⊆ rowAcc DO DT (fun w => rowTgt DO DT w) i := by
      rw [hTdef]
      exact rowAcc_mono (fun w => rowAcc_mono (fun y => by
        rw [hfeT]; simp only []; split
        · exact Finset.empty_subset _
        · split
          · exact Finset.empty_subset _
          · exact Finset.Subset.refl _) w) i
    have hFs : F ⊆ rowTgt IO IT i := by
      rw [hFdef]
      exact rowAcc_mono (fun y => by
        rw [hfeF]; simp only []; split
        · exact Finset.empty_subset _
        · exact Finset.Subset.refl _) i
    exact Finset.union_subset (fun x hx => Finset.mem_union_left _ (hTs hx))
      (fun x hx => Finset.mem_union_right _ (hFs hx))
  refine ⟨σ₃, K₁ + (K₂ + K₃), hr₁.seq (hr₂.seq hr₃), ?_, hAccFin, hP₃.1, hP₃.2.2,
    hJ₃.2.1, hP₃.2.1, ⟨T ∪ F, hsub, hJ₃.1⟩, fun a h1 h2 h3 => ?_,
    fun y h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  · have e₁ : (Ka + 11) * (DO (i + 1) - DO i)
        + ((Ka + 24 + 11) * d + 23) * (DO (i + 1) - DO i)
        = ((Ka + 35) * d + Ka + 34) * (DO (i + 1) - DO i) := by ring
    have e₂ : (Ka + 13 + 11) * (IO (i + 1) - IO i)
        = (Ka + 24) * (IO (i + 1) - IO i) := by ring
    omega
  · rw [hr₃.frame_arr a (by
        simp [RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.warrs, h3, hactw a h1 h2]),
      hr₂.frame_arr a (by
        simp [RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.warrs, h3, hactw a h1 h2]),
      hr₁.frame_arr a (by
        simp [RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.warrs, hactw a h1 h2])]
  · rw [hfv₃ y h1 h2 h6 h7, hfv₂ y h1 h2 h3 h4 h5 h6 h7, hfv₁ y h1 h2 h6 h7]

/-! ### The assembly's turn

`RamAugment.asmRow act` is `asmStamp 1`, the emit walk, `asmStamp 0`
and `asmClearE`. The two clearing walks return all three stamps to zero
— the `b = 0` walk's set is the `b = 1` walk's on the nose, and the
guard's emitted set sits inside what `asmClearE` clears, by
`rowAcc_mono`. -/

/-- **One vertex's turn of the assembly.** -/
theorem asmRow_run
    (ha₁ : ReadArrs a₁) (ha₂ : ReadArrs a₂)
    (hactw : ∀ a, a ≠ a₁ → a ≠ a₂ → a ∉ act.warrs)
    (hB1 : 1 < B) (hnB : n < B) (hWB : W < B) (hi : i < n)
    (hcsr : InCsr D m DO DT) (hdeg : D.InDegLE d) (hmW : m ≤ W)
    (hE : InCsr (RamElim.ElimCert.elimOr (fratGraph D) ρ) me IO IT) (hmeW : me ≤ W)
    (hρ : ∀ v : Fin n, ρ v = R (v : ℕ)) (hRn : ∀ v, v < n → R v < n)
    (hbo : Blocks "ooff" "otg" n W m OO OT σ)
    (hsnd : ∀ u < n, ∀ q, OO u ≤ q → q < OO (u + 1) → Pts DO DT (OT q) u)
    (hcmp : ∀ u < n, ∀ z < n, Pts DO DT z u → ∃ q, OO u ≤ q ∧ q < OO (u + 1) ∧ OT q = z)
    (hiv : σ.vars "i" = i) (harr : AsmArr n W DO DT OO OT IO IT σ)
    (hrnk : σ.arrs "rnk" = arrOf n R)
    (hsta0 : ∃ g, σ.arrs "sta" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hstd0 : ∃ g, σ.arrs "std" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hste0 : ∃ g, σ.arrs "ste" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hAccFr : ∀ S τ τ', Acc S τ →
      (∀ y, y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" → y ≠ "u" →
        τ'.vars y = τ.vars y) →
      (∀ a, a ≠ "sta" → a ≠ "std" → a ≠ "ste" → τ'.arrs a = τ.arrs a) → Acc S τ')
    (hAccI : ∀ S τ, Acc S τ → τ.vars "i" = i)
    (hAcc : Emits B n Ka a₁ a₂ act (valSet ((RamAugment.augOr D ρ).inN ⟨i, hi⟩)) Acc)
    (hA0 : Acc ∅ σ) :
    ∃ σ' K, Run B (RamAugment.asmRow act) σ σ' K ∧
      K ≤ ((Ka + 49) * d + Ka + 85) * (DO (i + 1) - DO i)
          + (28 * d + 98) * (OO (i + 1) - OO i)
          + (Ka + 38) * (IO (i + 1) - IO i)
          + 28 * (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)), (OO (OT p + 1) - OO (OT p)))
          + 132 ∧
      Acc (valSet ((RamAugment.augOr D ρ).inN ⟨i, hi⟩)) σ' ∧
      AsmArr n W DO DT OO OT IO IT σ' ∧ σ'.arrs "rnk" = arrOf n R ∧
      (∃ g, σ'.arrs "sta" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
      (∃ g, σ'.arrs "std" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
      (∃ g, σ'.arrs "ste" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
      (∀ a, a ≠ "sta" → a ≠ "std" → a ≠ "ste" → a ≠ a₁ → a ≠ a₂ →
        σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" → y ≠ "u" → y ≠ "c" →
        σ'.vars y = σ.vars y) := by
  classical
  obtain ⟨gsta₀, hgsta₀, hgstaz₀⟩ := hsta0
  obtain ⟨gstd₀, hgstd₀, hgstdz₀⟩ := hstd0
  obtain ⟨gste₀, hgste₀, hgstez₀⟩ := hste0
  have hmB : m < B := by omega
  have hmeB : me < B := by omega
  have hadj : rowTgt DO DT i ∪ rowTgt OO OT i = valSet (RamAugment.adjSet D ⟨i, hi⟩) :=
    adjRow_eq hcsr hbo hsnd hcmp hi
  have hdem : rowAcc OO OT (fun w => rowTgt DO DT w ∪ rowTgt OO OT w) i
      = valSet (RamAugment.demandOut D ⟨i, hi⟩) := demandRow_eq hcsr hbo hsnd hcmp hi
  have hAccSt : ∀ S τ p x, Acc S τ → Acc S (τ.setArr "ste" p x) := fun S τ p x h =>
    hAccFr S τ _ h (fun y _ _ _ _ _ _ => by rw [vars_setArr])
      (fun a _ _ ha => by rw [arrs_setArr, if_neg ha])
  have hAccV : ∀ S τ (y : String) (z : ℕ),
      (y = "j" ∨ y = "jend" ∨ y = "w" ∨ y = "q" ∨ y = "qe" ∨ y = "u") → Acc S τ →
      Acc S (τ.setVar y z) := by
    rintro S τ y z hy h
    refine hAccFr S τ _ h (fun y' h1 h2 h3 h4 h5 h6 => ?_)
      (fun a _ _ _ => by rw [arrs_setVar])
    rw [vars_setVar, if_neg]
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4, h5, h6]
  -- (1) the two stamps, set
  obtain ⟨σ₁, K₁, hr₁, hK₁, hm₁a, hm₁d, hfa₁, hfv₁⟩ :=
    asmStamp_run (B := B) (n := n) (d := d) (W := W) (m := m) (i := i) (D := D) (DO := DO)
      (DT := DT) (OO := OO) (OT := OT) (σ := σ) (b := 1) (gsta := gsta₀) (gstd := gstd₀)
      hB1 hnB (by omega) hmB hi hcsr hdeg hmW hbo hiv harr.1 hgsta₀ hgstd₀
  have hsta₁ : Marks "sta" n 1 (valSet (RamAugment.adjSet D ⟨i, hi⟩)) (fun _ => 0) σ₁ := by
    obtain ⟨g, hg, hgk⟩ := hm₁a
    exact ⟨g, hg, fun k hk => by rw [hgk k hk, hadj, hgstaz₀ k hk]⟩
  have hstd₁ : Marks "std" n 1 (valSet (RamAugment.demandOut D ⟨i, hi⟩)) (fun _ => 0) σ₁ := by
    obtain ⟨g, hg, hgk⟩ := hm₁d
    exact ⟨g, hg, fun k hk => by rw [hgk k hk, hdem, hgstdz₀ k hk]⟩
  have hste₁ : Marks "ste" n 1 (∅ : Finset ℕ) (fun _ => 0) σ₁ :=
    Marks.zero ⟨gste₀, by rw [hfa₁ "ste" (by decide) (by decide)]; exact hgste₀, hgstez₀⟩
  have harr₁ : AsmArr n W DO DT OO OT IO IT σ₁ :=
    harr.of_stampFrame
      (hfv₁ "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun a h1 h2 _ => hfa₁ a h1 h2)
  have hiv₁ : σ₁.vars "i" = i := by
    rw [hfv₁ "i" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hiv
  have hrnk₁ : σ₁.arrs "rnk" = arrOf n R := by
    rw [hfa₁ "rnk" (by decide) (by decide)]; exact hrnk
  have hA₁ : Acc ∅ σ₁ :=
    hAccFr _ _ _ hA0 (fun y h1 h2 h3 h4 h5 h6 => hfv₁ y h1 h2 h3 h4 h5 h6)
      (fun a h1 h2 _ => hfa₁ a h1 h2)
  -- (2) the three lists, emitted
  obtain ⟨σ₂, K₂, hr₂, hK₂, hA₂, harr₂, hrnk₂, hsta₂, hstd₂, ⟨S, hS, hste₂⟩, hfa₂, hfv₂⟩ :=
    asmEmit_run (B := B) (n := n) (d := d) (W := W) (m := m) (me := me) (Ka := Ka)
      (i := i) (a₁ := a₁) (a₂ := a₂) (act := act) (D := D) (ρ := ρ) (DO := DO) (DT := DT)
      (OO := OO) (OT := OT) (IO := IO) (IT := IT) (R := R) (Acc := Acc) (σ := σ₁)
      ha₁ ha₂ hactw hB1 hnB hi hcsr hdeg hmW hE hmeW hWB hρ hRn hiv₁ harr₁ hrnk₁
      hsta₁ hstd₁ hste₁ hAccSt hAccI hAccV hAcc hA₁
  obtain ⟨g₂a, hg₂a, hg₂ak⟩ := hsta₂
  obtain ⟨g₂d, hg₂d, hg₂dk⟩ := hstd₂
  obtain ⟨g₂e, hg₂e, hg₂ek⟩ := hste₂
  -- (3) the two stamps, cleared
  obtain ⟨σ₃, K₃, hr₃, hK₃, hm₃a, hm₃d, hfa₃, hfv₃⟩ :=
    asmStamp_run (B := B) (n := n) (d := d) (W := W) (m := m) (i := i) (D := D) (DO := DO)
      (DT := DT) (OO := OO) (OT := OT) (σ := σ₂) (b := 0) (gsta := g₂a) (gstd := g₂d)
      hB1 hnB (by omega) hmB hi hcsr hdeg hmW (harr₂.blocks hbo)
      (by rw [hfv₂ "i" (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; exact hiv₁)
      harr₂.1 hg₂a hg₂d
  have harr₃ : AsmArr n W DO DT OO OT IO IT σ₃ :=
    harr₂.of_stampFrame
      (hfv₃ "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun a h1 h2 _ => hfa₃ a h1 h2)
  -- (4) the duplicate stamp, cleared
  obtain ⟨σ₄, K₄, hr₄, hK₄, hm₄e, hfa₄, hfv₄⟩ :=
    asmClearE_run (B := B) (n := n) (d := d) (W := W) (m := m) (i := i) (D := D) (DO := DO)
      (DT := DT) (OO := OO) (OT := OT) (σ := σ₃) (me := me)
      (Eo := RamElim.ElimCert.elimOr (fratGraph D) ρ) (IO := IO) (IT := IT) (gste := g₂e)
      hB1 hnB hmB hmeB hi hcsr hdeg hmW hE hmeW
      (by
        rw [hfv₃ "i" (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide),
          hfv₂ "i" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)]
        exact hiv₁)
      harr₃.1 harr₃.2.1 harr₃.2.2
      (by rw [hfa₃ "ste" (by decide) (by decide)]; exact hg₂e)
  have harr₄ : AsmArr n W DO DT OO OT IO IT σ₄ :=
    harr₃.of_stampFrame
      (hfv₄ "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun a _ _ h3 => hfa₄ a h3)
  -- the three stamps are zero again
  have hstaz : ∃ g, σ₄.arrs "sta" = arrOf n g ∧ ∀ k < n, g k = 0 := by
    obtain ⟨g, hg, hgk⟩ := hm₃a
    refine ⟨g, by rw [hfa₄ "sta" (by decide)]; exact hg, fun k hk => ?_⟩
    rw [hgk k hk, hadj]
    by_cases h : k ∈ valSet (RamAugment.adjSet D ⟨i, hi⟩)
    · rw [if_pos h]
    · rw [if_neg h, hg₂ak k hk, if_neg h]
  have hstdz : ∃ g, σ₄.arrs "std" = arrOf n g ∧ ∀ k < n, g k = 0 := by
    obtain ⟨g, hg, hgk⟩ := hm₃d
    refine ⟨g, by rw [hfa₄ "std" (by decide)]; exact hg, fun k hk => ?_⟩
    rw [hgk k hk, hdem]
    by_cases h : k ∈ valSet (RamAugment.demandOut D ⟨i, hi⟩)
    · rw [if_pos h]
    · rw [if_neg h, hg₂dk k hk, if_neg h]
  have hstez : ∃ g, σ₄.arrs "ste" = arrOf n g ∧ ∀ k < n, g k = 0 := by
    obtain ⟨g, hg, hgk⟩ := hm₄e
    refine ⟨g, hg, fun k hk => ?_⟩
    rw [hgk k hk]
    by_cases h : k ∈ rowAcc DO DT (fun w => rowTgt DO DT w) i ∪ rowTgt IO IT i
    · rw [if_pos h]
    · rw [if_neg h, hg₂ek k hk, if_neg (fun hc => h (hS hc))]
  -- the accounting and the ranking cross the two clearing walks
  have hA₄ : Acc (valSet ((RamAugment.augOr D ρ).inN ⟨i, hi⟩)) σ₄ :=
    hAccFr _ _ _ (hAccFr _ _ _ hA₂ (fun y h1 h2 h3 h4 h5 h6 => hfv₃ y h1 h2 h3 h4 h5 h6)
        (fun a h1 h2 _ => hfa₃ a h1 h2))
      (fun y h1 h2 h3 h4 h5 h6 => hfv₄ y h1 h2 h3 h4 h5 h6) (fun a _ _ h3 => hfa₄ a h3)
  have hrnk₄ : σ₄.arrs "rnk" = arrOf n R := by
    rw [hfa₄ "rnk" (by decide), hfa₃ "rnk" (by decide) (by decide)]; exact hrnk₂
  -- the cost: the two stamping walks' nested sums, split
  have hsum : (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)),
        (14 * (OO (OT p + 1) - OO (OT p)) + 14 * d + 35))
      = 14 * (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)), (OO (OT p + 1) - OO (OT p)))
        + (14 * d + 35) * (OO (i + 1) - OO i) := by
    have h1 : (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)),
          (14 * (OO (OT p + 1) - OO (OT p)) + 14 * d + 35))
        = ∑ p ∈ Finset.Ico (OO i) (OO (i + 1)),
            (14 * (OO (OT p + 1) - OO (OT p)) + (14 * d + 35)) :=
      Finset.sum_congr rfl (fun p _ => by ring)
    rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Ico,
      smul_eq_mul]
    ring
  rw [hsum] at hK₁ hK₃
  refine ⟨σ₄, K₁ + (K₂ + (K₃ + K₄)), hr₁.seq (hr₂.seq (hr₃.seq hr₄)), ?_, hA₄, harr₄,
    hrnk₄, hstaz, hstdz, hstez, fun a h1 h2 h3 h4 h5 => ?_,
    fun y h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  · have e₁ : ((Ka + 35) * d + Ka + 34) * (DO (i + 1) - DO i)
        + (14 * d + 23) * (DO (i + 1) - DO i)
        + 14 * (DO (i + 1) - DO i) + 14 * (DO (i + 1) - DO i)
        = ((Ka + 49) * d + Ka + 85) * (DO (i + 1) - DO i) := by ring
    have e₂ : (14 * d + 35) * (OO (i + 1) - OO i) + (14 * d + 35) * (OO (i + 1) - OO i)
        + 14 * (OO (i + 1) - OO i) + 14 * (OO (i + 1) - OO i)
        = (28 * d + 98) * (OO (i + 1) - OO i) := by ring
    have e₃ : (Ka + 24) * (IO (i + 1) - IO i) + 14 * (IO (i + 1) - IO i)
        = (Ka + 38) * (IO (i + 1) - IO i) := by ring
    omega
  · rw [hfa₄ a h3, hfa₃ a h1 h2, hfa₂ a h4 h5 h3, hfa₁ a h1 h2]
  · rw [hfv₄ y h1 h2 h3 h4 h5 h6, hfv₃ y h1 h2 h3 h4 h5 h6,
      hfv₂ y h1 h2 h3 h4 h5 h6 h7, hfv₁ y h1 h2 h3 h4 h5 h6]

end AsmEmit

/-! ### The two assembly passes

The counting sort once more, at the two accountings: `cntAcc_emits`
for the degrees and `fillAcc_emits "ntg" "nfl"` for the blocks. The one
piece of arithmetic that is not a row length is the third walk of
`asmStamp`, which charges the out-block of every vertex an out-slot
names; `tile_sum`, `sum_slot_weight` and `slotCnt_out_eq` turn that
into `d · m`. -/

/-- The new in-degree of a vertex, at the number level. -/
noncomputable def augDeg {n : ℕ} (D : Orientation n) (ρ : Fin n → ℕ) (u : ℕ) : ℕ :=
  if h : u < n then ((RamAugment.augOr D ρ).inN ⟨u, h⟩).card else 0

/-- And its new block, at the number level. -/
noncomputable def augSet {n : ℕ} (D : Orientation n) (ρ : Fin n → ℕ) (u : ℕ) : Finset ℕ :=
  if h : u < n then valSet ((RamAugment.augOr D ρ).inN ⟨u, h⟩) else ∅

theorem augSet_eq {n : ℕ} {D : Orientation n} {ρ : Fin n → ℕ} {u : ℕ} (h : u < n) :
    augSet D ρ u = valSet ((RamAugment.augOr D ρ).inN ⟨u, h⟩) := dif_pos h

theorem augDeg_eq {n : ℕ} {D : Orientation n} {ρ : Fin n → ℕ} {u : ℕ} (h : u < n) :
    augDeg D ρ u = ((RamAugment.augOr D ρ).inN ⟨u, h⟩).card := dif_pos h

theorem card_augSet {n : ℕ} (D : Orientation n) (ρ : Fin n → ℕ) (u : ℕ) :
    (augSet D ρ u).card = augDeg D ρ u := by
  by_cases h : u < n
  · rw [augSet_eq h, card_valSet, augDeg_eq h]
  · rw [augSet, dif_neg h, augDeg, dif_neg h]; simp

theorem augDeg_le {n : ℕ} (D : Orientation n) (ρ : Fin n → ℕ) (u : ℕ) : augDeg D ρ u ≤ n := by
  rw [augDeg]
  split
  · exact le_trans (Finset.card_le_univ _) (by simp)
  · exact Nat.zero_le _

/-- The new arcs are at most `n²`, which is the room `augWidth` keeps
for them. -/
theorem sum_augDeg_le {n : ℕ} (D : Orientation n) (ρ : Fin n → ℕ) :
    RamElim.psum (augDeg D ρ) n ≤ n * n := by
  show ∑ u ∈ Finset.range n, augDeg D ρ u ≤ n * n
  calc ∑ u ∈ Finset.range n, augDeg D ρ u ≤ ∑ _u ∈ Finset.range n, n :=
        Finset.sum_le_sum fun u _ => augDeg_le D ρ u
    _ = n * n := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **The assembly's cost, summed.** Three of the four per-row charges
are row lengths and tile their arrays; the fourth is the out-block of
every vertex an out-slot names, and that is where the exchange is
spent. -/
theorem asm_cost_le {n d W m me c c₁ c₂ c₃ : ℕ} {D Eo : Orientation n}
    {DO DT OO OT IO IT : ℕ → ℕ} {σ : Env}
    (hcsr : InCsr D m DO DT) (hdeg : D.InDegLE d) (hE : InCsr Eo me IO IT)
    (hbo : Blocks "ooff" "otg" n W m OO OT σ)
    (hxch : ∀ w, w < n → inDeg D w = slotCnt OT m w) :
    ∑ i ∈ Finset.range n,
        (c₁ * (DO (i + 1) - DO i) + c₂ * (OO (i + 1) - OO i) + c₃ * (IO (i + 1) - IO i)
          + 28 * (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)), (OO (OT p + 1) - OO (OT p))) + c)
      ≤ c₁ * m + c₂ * m + c₃ * me + 28 * (d * m) + c * n := by
  classical
  have hinDeg : ∀ u, u < n → inDeg D u ≤ d := fun u hu => by
    rw [inDeg, dif_pos hu]; exact hdeg ⟨u, hu⟩
  have hSout : ∑ i ∈ Finset.range n,
      (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)), (OO (OT p + 1) - OO (OT p))) ≤ d * m := by
    have h1 : ∑ i ∈ Finset.range n,
        (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)), (OO (OT p + 1) - OO (OT p)))
        = ∑ p ∈ Finset.range m, (OO (OT p + 1) - OO (OT p)) :=
      (tile_sum hbo.zero hbo.last hbo.mono (fun p => OO (OT p + 1) - OO (OT p))).symm
    have h2 : ∑ p ∈ Finset.range m, (OO (OT p + 1) - OO (OT p))
        = ∑ u ∈ Finset.range n, slotCnt OT m u * (OO (u + 1) - OO u) :=
      sum_slot_weight (T := OT) (nv := n) (fun u => OO (u + 1) - OO u) m
        (fun s hs => hbo.target_lt s hs)
    rw [h1, h2]
    calc ∑ u ∈ Finset.range n, slotCnt OT m u * (OO (u + 1) - OO u)
        ≤ ∑ u ∈ Finset.range n, d * (OO (u + 1) - OO u) := by
          refine Finset.sum_le_sum fun u hu => ?_
          rw [← hxch u (Finset.mem_range.1 hu)]
          exact Nat.mul_le_mul_right _ (hinDeg u (Finset.mem_range.1 hu))
      _ = d * m := by rw [← Finset.mul_sum, hbo.sum_rowLen]
  have hd1 : ∑ i ∈ Finset.range n, c₁ * (DO (i + 1) - DO i) = c₁ * m := by
    rw [← Finset.mul_sum, incsr_sum_rowLen hcsr]
  have hd2 : ∑ i ∈ Finset.range n, c₂ * (OO (i + 1) - OO i) = c₂ * m := by
    rw [← Finset.mul_sum, hbo.sum_rowLen]
  have hd3 : ∑ i ∈ Finset.range n, c₃ * (IO (i + 1) - IO i) = c₃ * me := by
    rw [← Finset.mul_sum, incsr_sum_rowLen hE]
  simp only [Finset.sum_add_distrib]
  rw [hd1, hd2, hd3, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have ecn : n * c = c * n := by ring
  omega

section AsmPasses

variable {B n d W m me : ℕ} {D : Orientation n} {ρ : Fin n → ℕ}
variable {DO DT OO OT IO IT R : ℕ → ℕ} {σ : Env}

/-- **The new in-degrees, counted.** One turn zeroes the counter, runs
the stamped assembly of `i`, and writes the count one place up in the
offsets. -/
theorem asmCount_run
    (hnB : n + 1 < B) (hWB : W < B)
    (hcsr : InCsr D m DO DT) (hdeg : D.InDegLE d) (hmW : m ≤ W)
    (hE : InCsr (RamElim.ElimCert.elimOr (fratGraph D) ρ) me IO IT) (hmeW : me ≤ W)
    (hρ : ∀ v : Fin n, ρ v = R (v : ℕ)) (hRn : ∀ v, v < n → R v < n)
    (hbo : Blocks "ooff" "otg" n W m OO OT σ)
    (hsnd : ∀ u < n, ∀ q, OO u ≤ q → q < OO (u + 1) → Pts DO DT (OT q) u)
    (hcmp : ∀ u < n, ∀ z < n, Pts DO DT z u → ∃ q, OO u ≤ q ∧ q < OO (u + 1) ∧ OT q = z)
    (hxch : ∀ w, w < n → inDeg D w = slotCnt OT m w)
    (harr : AsmArr n W DO DT OO OT IO IT σ) (hrnk : σ.arrs "rnk" = arrOf n R)
    (hsta0 : ∃ g, σ.arrs "sta" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hstd0 : ∃ g, σ.arrs "std" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hste0 : ∃ g, σ.arrs "ste" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hnoff0 : ∃ g, σ.arrs "noff" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0) :
    ∃ σ' K, Run B RamAugment.asmCount σ σ' K ∧
      K ≤ 109 * (d * m) + 187 * m + 42 * me + 147 * n + 8 ∧
      AsmArr n W DO DT OO OT IO IT σ' ∧ σ'.arrs "rnk" = arrOf n R ∧
      (∃ g, σ'.arrs "sta" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
      (∃ g, σ'.arrs "std" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
      (∃ g, σ'.arrs "ste" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
      (∃ g, σ'.arrs "noff" = arrOf (n + 1) g ∧ g 0 = 0 ∧
        ∀ u < n, g (u + 1) = augDeg D ρ u) ∧
      (∀ a, a ≠ "sta" → a ≠ "std" → a ≠ "ste" → a ≠ "noff" → σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "i" → y ≠ "c" → y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" →
        y ≠ "u" → σ'.vars y = σ.vars y) := by
  classical
  obtain ⟨gno₀, hgno₀, hgnoz₀⟩ := hnoff0
  set I : ℕ → Env → Prop := fun i τ => τ.vars "i" = i ∧ i ≤ n ∧
    AsmArr n W DO DT OO OT IO IT τ ∧ τ.arrs "rnk" = arrOf n R ∧
    (∃ g, τ.arrs "sta" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
    (∃ g, τ.arrs "std" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
    (∃ g, τ.arrs "ste" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
    (∃ g, τ.arrs "noff" = arrOf (n + 1) g ∧ g 0 = 0 ∧
      ∀ u < i, g (u + 1) = augDeg D ρ u) with hIdef
  have hstep : ∀ i, i < n → ∀ τ, I i τ →
      ∃ τ' K, Run B (.seq (.assign "c" (.lit 0))
          (.seq (RamAugment.asmRow (.assign "c" (.add (.var "c") (.lit 1))))
            (.store "noff" (.add (.var "i") (.lit 1)) (.var "c")))) τ τ' K ∧
        K ≤ ((4 + 49) * d + 4 + 85) * (DO (i + 1) - DO i)
            + (28 * d + 98) * (OO (i + 1) - OO i) + (4 + 38) * (IO (i + 1) - IO i)
            + 28 * (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)), (OO (OT p + 1) - OO (OT p)))
            + 139 ∧ τ'.vars "i" = i ∧ I (i + 1) (τ'.setVar "i" (i + 1)) := by
    intro i hi τ hτ
    obtain ⟨hiv, -, harrτ, hrnkτ, hstaτ, hstdτ, hsteτ, ⟨gno, hgno, hgno0, hgnoI⟩⟩ := hτ
    have hcard : (valSet ((RamAugment.augOr D ρ).inN ⟨i, hi⟩)).card = augDeg D ρ i := by
      rw [card_valSet, augDeg_eq hi]
    -- `c := 0`
    set τ₁ := τ.setVar "c" 0 with hτ₁
    have hr₁ : Run B (.assign "c" (.lit 0)) τ τ₁ 2 :=
      (Run.assign (evalB_lit (by omega))).mono (by simp)
    have hiv₁ : τ₁.vars "i" = i := by rw [hτ₁, vars_setVar, if_neg (by decide), hiv]
    have harr₁ : AsmArr n W DO DT OO OT IO IT τ₁ := harrτ.setVar "c" (by decide) 0
    have hAccFr : ∀ (S : Finset ℕ) (τ' τ'' : Env), CntAcc n i S τ' →
        (∀ y, y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" → y ≠ "u" →
          τ''.vars y = τ'.vars y) →
        (∀ a, a ≠ "sta" → a ≠ "std" → a ≠ "ste" → τ''.arrs a = τ'.arrs a) →
        CntAcc n i S τ'' := by
      rintro S τ' τ'' ⟨h1, h2, h3⟩ hv -
      exact ⟨by rw [hv "c" (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact h1,
        by rw [hv "i" (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact h2, h3⟩
    obtain ⟨τ₂, K₂, hr₂, hK₂, hA₂, harr₂, hrnk₂, hsta₂, hstd₂, hste₂, hfa₂, hfv₂⟩ :=
      asmRow_run (B := B) (n := n) (d := d) (W := W) (m := m) (me := me) (Ka := 4) (i := i)
        (a₁ := "@") (a₂ := "@") (act := .assign "c" (.add (.var "c") (.lit 1))) (D := D)
        (ρ := ρ) (DO := DO) (DT := DT) (OO := OO) (OT := OT) (IO := IO) (IT := IT)
        (R := R) (Acc := CntAcc n i) (σ := τ₁)
        readArrs_at readArrs_at (by intro a _ _; simp [Com.warrs]) (by omega) (by omega)
        hWB hi hcsr hdeg hmW hE hmeW hρ hRn (harr₁.blocks hbo) hsnd hcmp hiv₁ harr₁
        (by rw [hτ₁, arrs_setVar]; exact hrnkτ)
        (by obtain ⟨g, hg, hz⟩ := hstaτ; exact ⟨g, by rw [hτ₁, arrs_setVar]; exact hg, hz⟩)
        (by obtain ⟨g, hg, hz⟩ := hstdτ; exact ⟨g, by rw [hτ₁, arrs_setVar]; exact hg, hz⟩)
        (by obtain ⟨g, hg, hz⟩ := hsteτ; exact ⟨g, by rw [hτ₁, arrs_setVar]; exact hg, hz⟩)
        hAccFr (fun _ _ h => h.2.1) (cntAcc_emits hnB)
        ⟨by rw [hτ₁, vars_setVar, if_pos rfl]; simp, hiv₁, by simp⟩
    -- `noff[i+1] := c`
    have hiv₂ : τ₂.vars "i" = i := by
      rw [hfv₂ "i" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]
      exact hiv₁
    have hcv₂ : τ₂.vars "c" = augDeg D ρ i := by rw [hA₂.1, hcard]
    have eidx : (Expr.add (.var "i") (.lit 1)).evalB B τ₂ = some (i + 1) := by
      have h := evalB_bin (B := B) (op := .add) (σ := τ₂) (m := τ₂.vars "i") (n := 1)
        (evalB_var (by rw [hiv₂]; omega)) (evalB_lit (by omega))
        (by rw [hiv₂]; simpa [Bop.apply] using (by omega : i + 1 < B))
      rw [hiv₂] at h
      simpa [Bop.apply] using h
    have ecv : (Expr.var "c").evalB B τ₂ = some (augDeg D ρ i) := by
      have hlt : augDeg D ρ i < B := lt_of_le_of_lt (augDeg_le D ρ i) (by omega)
      have h := evalB_var (B := B) (x := "c") (σ := τ₂) (by rw [hcv₂]; omega)
      rwa [hcv₂] at h
    have hgno₂ : τ₂.arrs "noff" = arrOf (n + 1) gno := by
      rw [hfa₂ "noff" (by decide) (by decide) (by decide) (by decide) (by decide), hτ₁,
        arrs_setVar]
      exact hgno
    have hl : i + 1 < (τ₂.arrs "noff").length := by rw [hgno₂, length_arrOf]; omega
    refine ⟨τ₂.setArr "noff" (i + 1) (augDeg D ρ i), 2 + (K₂ + 5),
      hr₁.seq (hr₂.seq ((Run.store eidx ecv hl).mono
        (by simp only [size_add, size_var, size_lit]; omega))), by omega,
      by rw [vars_setArr]; exact hiv₂, ?_⟩
    refine ⟨by simp, by omega,
      (harr₂.setArr (a := "noff") (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (i + 1) (augDeg D ρ i)).setVar "i" (by decide) (i + 1),
      by rw [arrs_setVar, arrs_setArr, if_neg (by decide)]; exact hrnk₂,
      (by obtain ⟨g, hg, hz⟩ := hsta₂
          exact ⟨g, by rw [arrs_setVar, arrs_setArr, if_neg (by decide)]; exact hg, hz⟩),
      (by obtain ⟨g, hg, hz⟩ := hstd₂
          exact ⟨g, by rw [arrs_setVar, arrs_setArr, if_neg (by decide)]; exact hg, hz⟩),
      (by obtain ⟨g, hg, hz⟩ := hste₂
          exact ⟨g, by rw [arrs_setVar, arrs_setArr, if_neg (by decide)]; exact hg, hz⟩),
      ⟨fun k => if k = i + 1 then augDeg D ρ i else gno k, ?_, ?_, ?_⟩⟩
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, hgno₂, set_arrOf]
    · simp only []; rw [if_neg (by omega)]; exact hgno0
    · intro u hu
      simp only []
      rcases Nat.lt_or_ge u i with h | h
      · rw [if_neg (by omega)]; exact hgnoI u h
      · rw [if_pos (show u + 1 = i + 1 by omega), show u = i from by omega]
  obtain ⟨σ', K, hrun, hK, hIn⟩ :=
    forVerts_run (B := B) (n := n)
      (costs := fun i => ((4 + 49) * d + 4 + 85) * (DO (i + 1) - DO i)
          + (28 * d + 98) * (OO (i + 1) - OO i) + (4 + 38) * (IO (i + 1) - IO i)
          + 28 * (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)), (OO (OT p + 1) - OO (OT p)))
          + 139)
      (I := I) (σ := σ) hnB (fun _ _ h => h.2.2.1.1.1) (fun _ _ h => h.1)
      (fun _ _ h => h.2.1) hstep
      ⟨by simp, by omega, harr.setVar "i" (by decide) 0,
        by rw [arrs_setVar]; exact hrnk,
        (by obtain ⟨g, hg, hz⟩ := hsta0; exact ⟨g, by rw [arrs_setVar]; exact hg, hz⟩),
        (by obtain ⟨g, hg, hz⟩ := hstd0; exact ⟨g, by rw [arrs_setVar]; exact hg, hz⟩),
        (by obtain ⟨g, hg, hz⟩ := hste0; exact ⟨g, by rw [arrs_setVar]; exact hg, hz⟩),
        ⟨gno₀, by rw [arrs_setVar]; exact hgno₀, hgnoz₀ 0 (by omega),
          fun u hu => absurd hu (by omega)⟩⟩
  obtain ⟨-, -, harr', hrnk', hsta', hstd', hste', hnoff'⟩ := hIn
  refine ⟨σ', K, hrun, le_trans hK ?_, harr', hrnk', hsta', hstd', hste', hnoff',
    fun a h1 h2 h3 h4 => hrun.frame_arr a ?_,
    fun y h1 h2 h3 h4 h5 h6 h7 h8 => hrun.frame_var y ?_⟩
  · have hcong : ∑ i ∈ Finset.range n,
        (((4 + 49) * d + 4 + 85) * (DO (i + 1) - DO i)
            + (28 * d + 98) * (OO (i + 1) - OO i) + (4 + 38) * (IO (i + 1) - IO i)
            + 28 * (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)), (OO (OT p + 1) - OO (OT p)))
            + 139 + 8)
        = ∑ i ∈ Finset.range n,
          ((53 * d + 89) * (DO (i + 1) - DO i) + (28 * d + 98) * (OO (i + 1) - OO i)
            + 42 * (IO (i + 1) - IO i)
            + 28 * (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)), (OO (OT p + 1) - OO (OT p)))
            + 147) := Finset.sum_congr rfl (fun i _ => by ring)
    rw [hcong]
    have hle := asm_cost_le (n := n) (d := d) (W := W) (m := m) (me := me) (c := 147)
      (c₁ := 53 * d + 89) (c₂ := 28 * d + 98) (c₃ := 42) (D := D)
      (Eo := RamElim.ElimCert.elimOr (fratGraph D) ρ) (DO := DO) (DT := DT) (OO := OO)
      (OT := OT) (IO := IO) (IT := IT) (σ := σ) hcsr hdeg hE hbo hxch
    have e₁ : (53 * d + 89) * m = 53 * (d * m) + 89 * m := by ring
    have e₂ : (28 * d + 98) * m = 28 * (d * m) + 98 * m := by ring
    omega
  · simp [RamAugment.forVerts, RamAugment.asmRow, RamAugment.asmStamp, RamAugment.asmEmit,
      RamAugment.asmClearE, RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.warrs,
      h1, h2, h3, h4]
  · simp [RamAugment.forVerts, RamAugment.asmRow, RamAugment.asmStamp, RamAugment.asmEmit,
      RamAugment.asmClearE, RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.wvars,
      h1, h2, h3, h4, h5, h6, h7, h8]

/-- **The new in-lists, written out once each.** The same turn as the
count, with the fill pointer of the current vertex for its action. -/
theorem asmFill_run {m' : ℕ} {NT₀ : ℕ → ℕ}
    (hnB : n + 1 < B) (hWB : W < B)
    (hcsr : InCsr D m DO DT) (hdeg : D.InDegLE d) (hmW : m ≤ W)
    (hE : InCsr (RamElim.ElimCert.elimOr (fratGraph D) ρ) me IO IT) (hmeW : me ≤ W)
    (hρ : ∀ v : Fin n, ρ v = R (v : ℕ)) (hRn : ∀ v, v < n → R v < n)
    (hbo : Blocks "ooff" "otg" n W m OO OT σ)
    (hsnd : ∀ u < n, ∀ q, OO u ≤ q → q < OO (u + 1) → Pts DO DT (OT q) u)
    (hcmp : ∀ u < n, ∀ z < n, Pts DO DT z u → ∃ q, OO u ≤ q ∧ q < OO (u + 1) ∧ OT q = z)
    (hxch : ∀ w, w < n → inDeg D w = slotCnt OT m w)
    (hm' : RamElim.psum (augDeg D ρ) n = m') (hm'W : m' ≤ W)
    (harr : AsmArr n W DO DT OO OT IO IT σ) (hrnk : σ.arrs "rnk" = arrOf n R)
    (hsta0 : ∃ g, σ.arrs "sta" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hstd0 : ∃ g, σ.arrs "std" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hste0 : ∃ g, σ.arrs "ste" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hnfl : σ.arrs "nfl" = arrOf n (RamElim.psum (augDeg D ρ)))
    (hntg : σ.arrs "ntg" = arrOf W NT₀) :
    ∃ σ' K, Run B RamAugment.asmFill σ σ' K ∧
      K ≤ 115 * (d * m) + 193 * m + 48 * me + 140 * n + 8 ∧
      AsmArr n W DO DT OO OT IO IT σ' ∧ σ'.arrs "rnk" = arrOf n R ∧
      (∃ NT, σ'.arrs "ntg" = arrOf W NT ∧ ∀ u < n,
        (∀ q, RamElim.psum (augDeg D ρ) u ≤ q → q < RamElim.psum (augDeg D ρ) (u + 1) →
          NT q ∈ augSet D ρ u) ∧
        (∀ z ∈ augSet D ρ u, ∃ q, RamElim.psum (augDeg D ρ) u ≤ q ∧
          q < RamElim.psum (augDeg D ρ) (u + 1) ∧ NT q = z)) ∧
      (∀ a, a ≠ "sta" → a ≠ "std" → a ≠ "ste" → a ≠ "ntg" → a ≠ "nfl" →
        σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "i" → y ≠ "c" → y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" →
        y ≠ "u" → σ'.vars y = σ.vars y) := by
  classical
  set FO : ℕ → ℕ := RamElim.psum (augDeg D ρ) with hFO
  have hFOsucc : ∀ u, FO (u + 1) = FO u + augDeg D ρ u := fun u => RamElim.psum_succ _ u
  have hFOle : ∀ u, u ≤ n → FO u ≤ m' := fun u hu => by
    rw [← hm']; exact RamElim.psum_mono _ hu
  set I : ℕ → Env → Prop := fun i τ => τ.vars "i" = i ∧ i ≤ n ∧
    AsmArr n W DO DT OO OT IO IT τ ∧ τ.arrs "rnk" = arrOf n R ∧
    (∃ g, τ.arrs "sta" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
    (∃ g, τ.arrs "std" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
    (∃ g, τ.arrs "ste" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
    (∃ f, τ.arrs "nfl" = arrOf n f ∧ ∀ k, i ≤ k → f k = FO k) ∧
    (∃ NT, τ.arrs "ntg" = arrOf W NT ∧ ∀ u < i,
      (∀ q, FO u ≤ q → q < FO (u + 1) → NT q ∈ augSet D ρ u) ∧
      (∀ z ∈ augSet D ρ u, ∃ q, FO u ≤ q ∧ q < FO (u + 1) ∧ NT q = z)) with hIdef
  have hstep : ∀ i, i < n → ∀ τ, I i τ →
      ∃ τ' K, Run B (RamAugment.asmRow
          (.seq (.store "ntg" (.get "nfl" (.var "i")) (.var "u"))
            (.store "nfl" (.var "i") (.add (.get "nfl" (.var "i")) (.lit 1))))) τ τ' K ∧
        K ≤ ((10 + 49) * d + 10 + 85) * (DO (i + 1) - DO i)
            + (28 * d + 98) * (OO (i + 1) - OO i) + (10 + 38) * (IO (i + 1) - IO i)
            + 28 * (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)), (OO (OT p + 1) - OO (OT p)))
            + 132 ∧ τ'.vars "i" = i ∧ I (i + 1) (τ'.setVar "i" (i + 1)) := by
    intro i hi τ hτ
    obtain ⟨hiv, -, harrτ, hrnkτ, hstaτ, hstdτ, hsteτ, ⟨f, hf, hfk⟩, ⟨NT, hNT, hNTI⟩⟩ := hτ
    have hEs : augSet D ρ i = valSet ((RamAugment.augOr D ρ).inN ⟨i, hi⟩) := augSet_eq hi
    have hcard : (valSet ((RamAugment.augOr D ρ).inN ⟨i, hi⟩)).card = augDeg D ρ i := by
      rw [card_valSet, augDeg_eq hi]
    have hEcard : FO i + (valSet ((RamAugment.augOr D ρ).inN ⟨i, hi⟩)).card = FO (i + 1) := by
      rw [hcard, hFOsucc]
    set Cap : Finset ℕ := valSet ((RamAugment.augOr D ρ).inN ⟨i, hi⟩) with hCap
    have hAccFr : ∀ (S : Finset ℕ) (τ' τ'' : Env),
        FillAcc "ntg" "nfl" n W i (FO i) NT f Cap S τ' →
        (∀ y, y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" → y ≠ "u" →
          τ''.vars y = τ'.vars y) →
        (∀ a, a ≠ "sta" → a ≠ "std" → a ≠ "ste" → τ''.arrs a = τ'.arrs a) →
        FillAcc "ntg" "nfl" n W i (FO i) NT f Cap S τ'' := by
      rintro S τ' τ'' ⟨h1, h2, ⟨f', hf', hfi', hfk'⟩, ⟨g, hg, g1, g2, g3⟩⟩ hv hfa
      exact ⟨by rw [hv "i" (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact h1, h2,
        ⟨f', by rw [hfa "nfl" (by decide) (by decide) (by decide)]; exact hf', hfi', hfk'⟩,
        ⟨g, by rw [hfa "ntg" (by decide) (by decide) (by decide)]; exact hg, g1, g2, g3⟩⟩
    obtain ⟨τ', K', hr, hK, hA', harr', hrnk', hsta', hstd', hste', hfa', hfv'⟩ :=
      asmRow_run (B := B) (n := n) (d := d) (W := W) (m := m) (me := me) (Ka := 10) (i := i)
        (a₁ := "ntg") (a₂ := "nfl")
        (act := .seq (.store "ntg" (.get "nfl" (.var "i")) (.var "u"))
          (.store "nfl" (.var "i") (.add (.get "nfl" (.var "i")) (.lit 1))))
        (D := D) (ρ := ρ) (DO := DO) (DT := DT) (OO := OO) (OT := OT) (IO := IO) (IT := IT)
        (R := R) (Acc := FillAcc "ntg" "nfl" n W i (FO i) NT f Cap) (σ := τ)
        readArrs_ntg readArrs_nfl (by intro a h1 h2; simp [Com.warrs, h1, h2]) (by omega)
        (by omega) hWB hi hcsr hdeg hmW hE hmeW hρ hRn (harrτ.blocks hbo) hsnd hcmp hiv
        harrτ hrnkτ hstaτ hstdτ hsteτ hAccFr (fun _ _ h => h.1)
        (fillAcc_emits (by decide) hi (by omega) (by omega)
          (by rw [hEcard]; exact le_trans (hFOle (i + 1) (by omega)) hm'W))
        ⟨hiv, by simp, ⟨f, hf, by rw [hfk i le_rfl]; simp, fun k _ => rfl⟩,
          ⟨NT, hNT, fun q h₁ h₂ => by simp at h₂; omega, fun z hz => absurd hz (by simp),
            fun q _ => rfl⟩⟩
    obtain ⟨-, -, ⟨f', hf'a, hf'i, hf'k⟩, ⟨G, hGa, hG₁, hG₂, hG₃⟩⟩ := hA'
    refine ⟨τ', K', hr, hK,
      hfv' "i" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) |>.trans hiv, ?_⟩
    refine ⟨by simp, by omega, harr'.setVar "i" (by decide) (i + 1),
      by rw [arrs_setVar]; exact hrnk',
      (by obtain ⟨g, hg, hz⟩ := hsta'; exact ⟨g, by rw [arrs_setVar]; exact hg, hz⟩),
      (by obtain ⟨g, hg, hz⟩ := hstd'; exact ⟨g, by rw [arrs_setVar]; exact hg, hz⟩),
      (by obtain ⟨g, hg, hz⟩ := hste'; exact ⟨g, by rw [arrs_setVar]; exact hg, hz⟩),
      ⟨f', by rw [arrs_setVar]; exact hf'a, ?_⟩, ⟨G, by rw [arrs_setVar]; exact hGa, ?_⟩⟩
    · intro k hk
      rw [hf'k k (by omega)]
      exact hfk k (by omega)
    · intro u hu
      rcases Nat.lt_or_ge u i with h | h
      · have hlo : FO (u + 1) ≤ FO i := RamElim.psum_mono _ (by omega)
        refine ⟨fun q h₁ h₂ => ?_, fun z hz => ?_⟩
        · rw [hG₃ q (Or.inl (by omega))]
          exact (hNTI u h).1 q h₁ h₂
        · obtain ⟨q, hq₁, hq₂, hq₃⟩ := (hNTI u h).2 z hz
          exact ⟨q, hq₁, hq₂, by rw [hG₃ q (Or.inl (by omega))]; exact hq₃⟩
      · have hui : u = i := by omega
        subst hui
        rw [hEs]
        refine ⟨fun q h₁ h₂ => hG₁ q h₁ (by rw [hEcard]; exact h₂), fun z hz => ?_⟩
        obtain ⟨q, hq₁, hq₂, hq₃⟩ := hG₂ z hz
        exact ⟨q, hq₁, by rw [← hEcard]; exact hq₂, hq₃⟩
  obtain ⟨σ', K, hrun, hK, hIn⟩ :=
    forVerts_run (B := B) (n := n)
      (costs := fun i => ((10 + 49) * d + 10 + 85) * (DO (i + 1) - DO i)
          + (28 * d + 98) * (OO (i + 1) - OO i) + (10 + 38) * (IO (i + 1) - IO i)
          + 28 * (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)), (OO (OT p + 1) - OO (OT p)))
          + 132)
      (I := I) (σ := σ) hnB (fun _ _ h => h.2.2.1.1.1) (fun _ _ h => h.1)
      (fun _ _ h => h.2.1) hstep
      ⟨by simp, by omega, harr.setVar "i" (by decide) 0,
        by rw [arrs_setVar]; exact hrnk,
        (by obtain ⟨g, hg, hz⟩ := hsta0; exact ⟨g, by rw [arrs_setVar]; exact hg, hz⟩),
        (by obtain ⟨g, hg, hz⟩ := hstd0; exact ⟨g, by rw [arrs_setVar]; exact hg, hz⟩),
        (by obtain ⟨g, hg, hz⟩ := hste0; exact ⟨g, by rw [arrs_setVar]; exact hg, hz⟩),
        ⟨FO, by rw [arrs_setVar]; exact hnfl, fun k _ => rfl⟩,
        ⟨NT₀, by rw [arrs_setVar]; exact hntg, fun u hu => absurd hu (by omega)⟩⟩
  obtain ⟨-, -, harr', hrnk', -, -, -, -, hntg'⟩ := hIn
  refine ⟨σ', K, hrun, le_trans hK ?_, harr', hrnk', hntg',
    fun a h1 h2 h3 h4 h5 => hrun.frame_arr a ?_,
    fun y h1 h2 h3 h4 h5 h6 h7 h8 => hrun.frame_var y ?_⟩
  · have hcong : ∑ i ∈ Finset.range n,
        (((10 + 49) * d + 10 + 85) * (DO (i + 1) - DO i)
            + (28 * d + 98) * (OO (i + 1) - OO i) + (10 + 38) * (IO (i + 1) - IO i)
            + 28 * (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)), (OO (OT p + 1) - OO (OT p)))
            + 132 + 8)
        = ∑ i ∈ Finset.range n,
          ((59 * d + 95) * (DO (i + 1) - DO i) + (28 * d + 98) * (OO (i + 1) - OO i)
            + 48 * (IO (i + 1) - IO i)
            + 28 * (∑ p ∈ Finset.Ico (OO i) (OO (i + 1)), (OO (OT p + 1) - OO (OT p)))
            + 140) := Finset.sum_congr rfl (fun i _ => by ring)
    rw [hcong]
    have hle := asm_cost_le (n := n) (d := d) (W := W) (m := m) (me := me) (c := 140)
      (c₁ := 59 * d + 95) (c₂ := 28 * d + 98) (c₃ := 48) (D := D)
      (Eo := RamElim.ElimCert.elimOr (fratGraph D) ρ) (DO := DO) (DT := DT) (OO := OO)
      (OT := OT) (IO := IO) (IT := IT) (σ := σ) hcsr hdeg hE hbo hxch
    have e₁ : (59 * d + 95) * m = 59 * (d * m) + 95 * m := by ring
    have e₂ : (28 * d + 98) * m = 28 * (d * m) + 98 * m := by ring
    omega
  · simp [RamAugment.forVerts, RamAugment.asmRow, RamAugment.asmStamp, RamAugment.asmEmit,
      RamAugment.asmClearE, RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.warrs,
      h1, h2, h3, h4, h5]
  · simp [RamAugment.forVerts, RamAugment.asmRow, RamAugment.asmStamp, RamAugment.asmEmit,
      RamAugment.asmClearE, RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.wvars,
      h1, h3, h4, h5, h6, h7, h8]

/-- **The next orientation's block structure.** The three passes and
the report, sequenced: what they leave in `noff`/`ntg` is
`InCsr (augOr D ρ)`, the surface the next round reads as this one read
its own, and what they leave in `mn` is its arc count. -/
theorem asmPass_run
    (hnB : n + 1 < B) (hWB : W < B)
    (hcsr : InCsr D m DO DT) (hdeg : D.InDegLE d) (hmW : m ≤ W)
    (hE : InCsr (RamElim.ElimCert.elimOr (fratGraph D) ρ) me IO IT) (hmeW : me ≤ W)
    (hρ : ∀ v : Fin n, ρ v = R (v : ℕ)) (hRn : ∀ v, v < n → R v < n)
    (hbo : Blocks "ooff" "otg" n W m OO OT σ)
    (hsnd : ∀ u < n, ∀ q, OO u ≤ q → q < OO (u + 1) → Pts DO DT (OT q) u)
    (hcmp : ∀ u < n, ∀ z < n, Pts DO DT z u → ∃ q, OO u ≤ q ∧ q < OO (u + 1) ∧ OT q = z)
    (hxch : ∀ w, w < n → inDeg D w = slotCnt OT m w)
    (hm'W : RamElim.psum (augDeg D ρ) n ≤ W)
    (harr : AsmArr n W DO DT OO OT IO IT σ) (hrnk : σ.arrs "rnk" = arrOf n R)
    (hsta0 : ∃ g, σ.arrs "sta" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hstd0 : ∃ g, σ.arrs "std" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hste0 : ∃ g, σ.arrs "ste" = arrOf n g ∧ ∀ k < n, g k = 0)
    (hnoff0 : ∃ g, σ.arrs "noff" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0)
    (hnfl0 : ∃ g, σ.arrs "nfl" = arrOf n g) (hntg0 : ∃ g, σ.arrs "ntg" = arrOf W g) :
    ∃ σ' K, Run B RamAugment.asmPass σ σ' K ∧
      K ≤ 224 * (d * m) + 380 * m + 90 * me + 310 * n + 27 ∧
      σ'.arrs "rnk" = arrOf n R ∧
      σ'.arrs "noff" = arrOf (n + 1) (RamElim.psum (augDeg D ρ)) ∧
      (∃ NT, σ'.arrs "ntg" = arrOf W NT ∧
        InCsr (RamAugment.augOr D ρ) (RamElim.psum (augDeg D ρ) n)
          (RamElim.psum (augDeg D ρ)) NT) ∧
      σ'.vars "mn" = RamElim.psum (augDeg D ρ) n ∧
      (∀ a, a ≠ "sta" → a ≠ "std" → a ≠ "ste" → a ≠ "noff" → a ≠ "ntg" → a ≠ "nfl" →
        σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "i" → y ≠ "c" → y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" →
        y ≠ "u" → y ≠ "mn" → σ'.vars y = σ.vars y) := by
  classical
  obtain ⟨σ₁, K₁, hr₁, hK₁, harr₁, hrnk₁, hsta₁, hstd₁, hste₁, hnoff₁, hfa₁, hfv₁⟩ :=
    asmCount_run hnB hWB hcsr hdeg hmW hE hmeW hρ hRn hbo hsnd hcmp hxch harr hrnk
      hsta0 hstd0 hste0 hnoff0
  obtain ⟨σ₂, K₂, hr₂, hK₂, hn₂, hnoffa₂, hnfl₂⟩ :=
    prefixPass_run (B := B) (a := "noff") (b := "nfl") (n := n) (d := augDeg D ρ)
      (σ := σ₁) (by decide) hnB (by omega) harr₁.1.1 hnoff₁
      (by
        obtain ⟨g, hg⟩ := hnfl0
        refine ⟨g, ?_⟩
        rw [hfa₁ "nfl" (by decide) (by decide) (by decide) (by decide)]
        exact hg)
  have hfa₂ : ∀ a, a ≠ "noff" → a ≠ "nfl" → σ₂.arrs a = σ₁.arrs a :=
    fun a ha hb => hr₂.frame_arr a (by
      simp [prefixCom, RamAugment.forVerts, Com.warrs, ha, hb])
  have hfv₂ : ∀ y, y ≠ "i" → σ₂.vars y = σ₁.vars y :=
    fun y hy => hr₂.frame_var y (by simp [prefixCom, RamAugment.forVerts, Com.wvars, hy])
  have harr₂ : AsmArr n W DO DT OO OT IO IT σ₂ :=
    ⟨⟨hn₂, by rw [hfa₂ "doff" (by decide) (by decide)]; exact harr₁.1.2.1,
        by rw [hfa₂ "dtg" (by decide) (by decide)]; exact harr₁.1.2.2.1,
        by rw [hfa₂ "ooff" (by decide) (by decide)]; exact harr₁.1.2.2.2.1,
        by rw [hfa₂ "otg" (by decide) (by decide)]; exact harr₁.1.2.2.2.2⟩,
      by rw [hfa₂ "ioff" (by decide) (by decide)]; exact harr₁.2.1,
      by rw [hfa₂ "itg" (by decide) (by decide)]; exact harr₁.2.2⟩
  obtain ⟨NT₀, hNT₀⟩ := hntg0
  obtain ⟨σ₃, K₃, hr₃, hK₃, harr₃, hrnk₃, hntg₃, hfa₃, hfv₃⟩ :=
    asmFill_run (B := B) (n := n) (d := d) (W := W) (m := m) (me := me) (D := D) (ρ := ρ)
      (DO := DO) (DT := DT) (OO := OO) (OT := OT) (IO := IO) (IT := IT) (R := R)
      (σ := σ₂) (m' := RamElim.psum (augDeg D ρ) n) (NT₀ := NT₀)
      hnB hWB hcsr hdeg hmW hE hmeW hρ hRn (harr₂.blocks hbo) hsnd hcmp hxch rfl hm'W
      harr₂ (by rw [hfa₂ "rnk" (by decide) (by decide)]; exact hrnk₁)
      (by obtain ⟨g, hg, hz⟩ := hsta₁
          exact ⟨g, by rw [hfa₂ "sta" (by decide) (by decide)]; exact hg, hz⟩)
      (by obtain ⟨g, hg, hz⟩ := hstd₁
          exact ⟨g, by rw [hfa₂ "std" (by decide) (by decide)]; exact hg, hz⟩)
      (by obtain ⟨g, hg, hz⟩ := hste₁
          exact ⟨g, by rw [hfa₂ "ste" (by decide) (by decide)]; exact hg, hz⟩)
      hnfl₂
      (by rw [hfa₂ "ntg" (by decide) (by decide),
            hfa₁ "ntg" (by decide) (by decide) (by decide) (by decide)]
          exact hNT₀)
  -- the report
  have hnoff₃ : σ₃.arrs "noff" = arrOf (n + 1) (RamElim.psum (augDeg D ρ)) := by
    rw [hfa₃ "noff" (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hnoffa₂
  have hnv₃ : σ₃.vars "n" = n := harr₃.1.1
  have en : (Expr.var "n").evalB B σ₃ = some n := by
    have h := evalB_var (B := B) (x := "n") (σ := σ₃) (by rw [hnv₃]; omega)
    rwa [hnv₃] at h
  have eget : (Expr.get "noff" (.var "n")).evalB B σ₃
      = some (RamElim.psum (augDeg D ρ) n) :=
    evalB_get en (by rw [hnoff₃, getElem?_arrOf (RamElim.psum (augDeg D ρ)) (by omega)])
      (by omega)
  refine ⟨σ₃.setVar "mn" (RamElim.psum (augDeg D ρ) n), K₁ + (K₂ + (K₃ + 3)),
    hr₁.seq (hr₂.seq (hr₃.seq ((Run.assign eget).mono (by simp)))), by omega,
    by rw [arrs_setVar]; exact hrnk₃, by rw [arrs_setVar]; exact hnoff₃, ?_, by simp, ?_, ?_⟩
  · obtain ⟨NT, hNTa, hNTb⟩ := hntg₃
    refine ⟨NT, by rw [arrs_setVar]; exact hNTa, ⟨RamElim.psum_zero _, rfl,
      fun i _ => RamElim.psum_mono _ (by omega), ?_, ?_, ?_⟩⟩
    · intro j hj
      obtain ⟨w, hw, ha, hb⟩ :=
        RamElim.exists_block (ID := augDeg D ρ) (m := n) (t := j) hj
      have h := (hNTb w hw).1 j ha hb
      rw [augSet_eq hw] at h
      exact valSet_lt h
    · intro u v
      constructor
      · intro hmem
        have hv : (v : ℕ) ∈ augSet D ρ (u : ℕ) := by
          rw [augSet_eq u.isLt]; exact mem_valSet_of hmem
        obtain ⟨q, hq₁, hq₂, hq₃⟩ := (hNTb (u : ℕ) u.isLt).2 (v : ℕ) hv
        exact ⟨q, hq₁, hq₂, hq₃⟩
      · rintro ⟨q, hq₁, hq₂, hq₃⟩
        have h := (hNTb (u : ℕ) u.isLt).1 q hq₁ hq₂
        rw [augSet_eq u.isLt] at h
        obtain ⟨hlt, hmem⟩ := mem_valSet.1 h
        have he : (⟨NT q, hlt⟩ : Fin n) = v := Fin.ext hq₃
        rw [he] at hmem
        exact hmem
    · intro w
      have he : (⟨(w : ℕ), w.isLt⟩ : Fin n) = w := Fin.ext rfl
      rw [RamElim.psum_succ, augDeg_eq w.isLt, he]
      omega
  · intro a h1 h2 h3 h4 h5 h6
    rw [arrs_setVar, hfa₃ a h1 h2 h3 h5 h6, hfa₂ a h4 h6, hfa₁ a h1 h2 h3 h4]
  · intro y h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [vars_setVar, if_neg h9, hfv₃ y h1 h2 h3 h4 h5 h6 h7 h8, hfv₂ y h1,
      hfv₁ y h1 h2 h3 h4 h5 h6 h7 h8]

end AsmPasses

/-! ### The round, whole

The five phases, sequenced: the out-lists, the fraternity graph, the
mask, the elimination — through `elimCert_spec`, so that
`RamAugment.ElimAvail` is never used — and the assembly. Every array a
phase does not write is carried across it by the frame that phase
exports, and the cost is one order inside `RamAugment.augCost`. -/

/-- **The augmentation round implements its specification.** -/
theorem implements {B n d nf W m : ℕ} {D : Orientation n} {DO DT : ℕ → ℕ} :
    RamAugment.Implements B n d nf W m D DO DT := by
  classical
  intro _he hcsr hdeg hnf hmW hW hB
  refine Spec.of_exists ?_
  intro σ hσ
  obtain ⟨hn, hdoff, hdtg, hooffA, hotgA, hoflA, hoffA, htgtA, hfflA, halvA, hdegA, helmA,
    hrnkA, hidgA, hbhA, hbvA, hbnA, hioffA, hiflA, hitgA, hnoffA, hnflA, hntgA, hstfA,
    hstaA, hstdA, hsteA⟩ := hσ
  -- the width's arithmetic: `n`, `m`, `d · m`, `nf` and `n²` all fit under `W`
  have hAW : n * (d + 1) ^ 2 + n * n + 1 ≤ W := hW
  have hsq : (d + 1) ^ 2 = d * d + 2 * d + 1 := by ring
  have hnW : n < W := by
    have h1 : n * 1 ≤ n * (d + 1) ^ 2 := Nat.mul_le_mul_left n (by omega)
    omega
  have hnnW : n * n < W := by omega
  have hdmW : d * m ≤ W := by
    have h1 : d * m ≤ d * (n * d) := Nat.mul_le_mul_left d (arcs_le hcsr hdeg)
    have h2 : d * (n * d) = n * (d * d) := by ring
    have h3 : n * (d * d) ≤ n * (d + 1) ^ 2 := Nat.mul_le_mul_left n (by omega)
    omega
  have hnfW : nf < W := by
    have h := RamAugment.fratSlots_lt_augWidth (D := D) hdeg
    rw [hnf] at h
    omega
  -- (1) the out-lists
  obtain ⟨σ₁, K₁, hr₁, hK₁, hScat, hfa₁, hfv₁⟩ :=
    outPass_run (B := B) (n := n) (W := W) (m := m) (DO := DO) (DT := DT) (σ := σ)
      (by omega) (by omega) hmW hn (Blocks.of_inCsr hcsr hdoff hdtg hmW) hooffA hoflA hotgA
  obtain ⟨OT, hbo, hsnd, hcmp⟩ := hScat.blocks
  have hxch : ∀ w, w < n → inDeg D w = slotCnt OT m w := fun w hw =>
    slotCnt_out_eq hcsr hbo hcmp w (Finset.mem_range.2 hw)
  have harr₁ : NestArr n W DO DT (outOff DT m) OT σ₁ :=
    ⟨hScat.1, hScat.2.1.offArr, hScat.2.1.tgtArr, hbo.offArr, hbo.tgtArr⟩
  -- (2) the fraternity graph
  obtain ⟨σ₂, K₂, hr₂, hK₂, harr₂, hstf₂, hoff₂, ⟨FT, hFT, hcsrF⟩, hmf₂, hfa₂, hfv₂⟩ :=
    fratPass_run (B := B) (n := n) (d := d) (W := W) (m := m) (D := D) (DO := DO)
      (DT := DT) (OO := outOff DT m) (OT := OT) (σ := σ₁) (nf := nf)
      (by omega) (by omega) (by omega) hcsr hdeg hmW hbo hsnd hcmp hnf harr₁
      (by
        obtain ⟨g, hg, hz⟩ := hstfA
        exact ⟨g, by rw [hfa₁ "stf" (by decide) (by decide) (by decide)]; exact hg, hz⟩)
      (by
        obtain ⟨g, hg, hz⟩ := hoffA
        exact ⟨g, by rw [hfa₁ "off" (by decide) (by decide) (by decide)]; exact hg, hz⟩)
      (by
        obtain ⟨g, hg⟩ := hfflA
        exact ⟨g, by rw [hfa₁ "ffl" (by decide) (by decide) (by decide)]; exact hg⟩)
      (by
        obtain ⟨g, hg⟩ := htgtA
        exact ⟨g, by rw [hfa₁ "tgt" (by decide) (by decide) (by decide)]; exact hg⟩)
  -- (3) the mask
  obtain ⟨σ₃, K₃, hr₃, hK₃, hn₃, halv₃, hfa₃, hfv₃⟩ :=
    alvSet_run (B := B) (n := n) (σ := σ₂) (by omega) harr₂.1
      (by
        obtain ⟨g, hg⟩ := halvA
        refine ⟨g, ?_⟩
        rw [hfa₂ "alv" (by decide) (by decide) (by decide) (by decide),
          hfa₁ "alv" (by decide) (by decide) (by decide)]
        exact hg)
  have hfa₃₀ : ∀ a, a ≠ "ooff" → a ≠ "ofl" → a ≠ "otg" → a ≠ "stf" → a ≠ "off" →
      a ≠ "tgt" → a ≠ "ffl" → a ≠ "alv" → σ₃.arrs a = σ.arrs a :=
    fun a h1 h2 h3 h4 h5 h6 h7 h8 => by
      rw [hfa₃ a h8, hfa₂ a h4 h5 h6 h7, hfa₁ a h1 h2 h3]
  -- (4) the elimination, at the postcondition that has both answers
  obtain ⟨σ₄, hr₄, hmem₄, R', hrnkR', hRlt⟩ :=
    (elimCert_spec (B := B) (n := n) (ns := nf) (W := W) (G := fratGraph D)
        (O := RamElim.psum (fratDeg D)) (T := FT) (M := fun _ => 1)
        hcsrF (by omega) (fun z _ => by show 1 < B; omega) (by omega)).run
      ⟨hn₃, by rw [hfa₃ "off" (by decide)]; exact hoff₂,
        by rw [hfa₃ "tgt" (by decide)]; exact hFT, halv₃,
        (by
          obtain ⟨g, hg⟩ := hdegA
          exact ⟨g, by rw [hfa₃₀ "deg" (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)]; exact hg⟩),
        (by
          obtain ⟨g, hg, hz⟩ := helmA
          exact ⟨g, by rw [hfa₃₀ "elm" (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)]; exact hg, hz⟩),
        (by
          obtain ⟨g, hg⟩ := hrnkA
          exact ⟨g, by rw [hfa₃₀ "rnk" (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)]; exact hg⟩),
        (by
          obtain ⟨g, hg⟩ := hidgA
          exact ⟨g, by rw [hfa₃₀ "idg" (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)]; exact hg⟩),
        (by
          obtain ⟨g, hg, hz⟩ := hbhA
          exact ⟨g, by rw [hfa₃₀ "bh" (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)]; exact hg, hz⟩),
        (by
          obtain ⟨g, hg⟩ := hbvA
          exact ⟨g, by rw [hfa₃₀ "bv" (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)]; exact hg⟩),
        (by
          obtain ⟨g, hg⟩ := hbnA
          exact ⟨g, by rw [hfa₃₀ "bn" (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)]; exact hg⟩),
        (by
          obtain ⟨g, hg⟩ := hioffA
          exact ⟨g, by rw [hfa₃₀ "ioff" (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)]; exact hg⟩),
        (by
          obtain ⟨g, hg⟩ := hiflA
          exact ⟨g, by rw [hfa₃₀ "ifl" (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)]; exact hg⟩),
        (by
          obtain ⟨g, hg⟩ := hitgA
          exact ⟨g, by rw [hfa₃₀ "itg" (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)]; exact hg⟩)⟩
  obtain ⟨R, IO, IT, k, mm, hrnk₄, hkmax₄, hioff₄, hitg₄, hmmnf, hout⟩ := hmem₄
  have hmask : RamBfs.masked (fratGraph D) (fun _ => 1) = fratGraph D :=
    RamElim.masked_of_all_alive _ (fun v _ => by simp)
  have hcert : ElimCert (fratGraph D) (fun v : Fin n => R (v : ℕ)) k := by
    have h := hout.cert
    rwa [hmask] at h
  have harcs : InCsr
      (RamElim.ElimCert.elimOr (fratGraph D) (fun v : Fin n => R (v : ℕ))) mm IO IT := by
    have h := hout.arcs
    rwa [hmask] at h
  have hRR : ∀ j, j < n → R j = R' j := by
    intro j hj
    have h : (arrOf n R)[j]? = (arrOf n R')[j]? := by rw [← hrnk₄, ← hrnkR']
    rw [getElem?_arrOf R hj, getElem?_arrOf R' hj] at h
    exact Option.some.inj h
  have hRn : ∀ v, v < n → R v < n := fun v hv => by rw [hRR v hv]; exact hRlt v hv
  -- the arrays the assembly is handed, across all four phases
  have hfaAll : ∀ a, a ≠ "ooff" → a ≠ "ofl" → a ≠ "otg" → a ≠ "stf" → a ≠ "off" →
      a ≠ "tgt" → a ≠ "ffl" → a ≠ "alv" → a ∉ RamElim.elimCom.warrs →
      σ₄.arrs a = σ.arrs a :=
    fun a h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
      rw [hr₄.frame_arr a h9, hfa₃₀ a h1 h2 h3 h4 h5 h6 h7 h8]
  have hooff₄ : σ₄.arrs "ooff" = arrOf (n + 1) (outOff DT m) := by
    rw [hr₄.frame_arr "ooff" (by decide), hfa₃ "ooff" (by decide),
      hfa₂ "ooff" (by decide) (by decide) (by decide) (by decide)]
    exact hbo.offArr
  have hotg₄ : σ₄.arrs "otg" = arrOf W OT := by
    rw [hr₄.frame_arr "otg" (by decide), hfa₃ "otg" (by decide),
      hfa₂ "otg" (by decide) (by decide) (by decide) (by decide)]
    exact hbo.tgtArr
  have hn₄ : σ₄.vars "n" = n := by
    rw [hr₄.frame_var "n" (by decide), hfv₃ "n" (by decide),
      hfv₂ "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide),
      hfv₁ "n" (by decide) (by decide) (by decide) (by decide)]
    exact hn
  have hdoff₄ : σ₄.arrs "doff" = arrOf (n + 1) DO := by
    rw [hfaAll "doff" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    exact hdoff
  have hdtg₄ : σ₄.arrs "dtg" = arrOf W DT := by
    rw [hfaAll "dtg" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    exact hdtg
  have harr₄ : AsmArr n W DO DT (outOff DT m) OT IO IT σ₄ :=
    ⟨⟨hn₄, hdoff₄, hdtg₄, hooff₄, hotg₄⟩, hioff₄, hitg₄⟩
  -- (5) the assembly
  obtain ⟨σ₅, K₅, hr₅, hK₅, hrnk₅, hnoff₅, ⟨NT, hntg₅, hincsr₅⟩, hmn₅, -, hfv₅⟩ :=
    asmPass_run (B := B) (n := n) (d := d) (W := W) (m := m) (me := mm) (D := D)
      (ρ := fun v : Fin n => R (v : ℕ)) (DO := DO) (DT := DT) (OO := outOff DT m)
      (OT := OT) (IO := IO) (IT := IT) (R := R) (σ := σ₄)
      (by omega) (by omega) hcsr hdeg hmW harcs (by omega) (fun _ => rfl) hRn
      (harr₄.blocks hbo) hsnd hcmp hxch
      (le_trans (sum_augDeg_le D (fun v : Fin n => R (v : ℕ))) (by omega))
      harr₄ hrnk₄
      (by
        obtain ⟨g, hg, hz⟩ := hstaA
        exact ⟨g, by rw [hfaAll "sta" (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg, hz⟩)
      (by
        obtain ⟨g, hg, hz⟩ := hstdA
        exact ⟨g, by rw [hfaAll "std" (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg, hz⟩)
      (by
        obtain ⟨g, hg, hz⟩ := hsteA
        exact ⟨g, by rw [hfaAll "ste" (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg, hz⟩)
      (by
        obtain ⟨g, hg, hz⟩ := hnoffA
        exact ⟨g, by rw [hfaAll "noff" (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg, hz⟩)
      (by
        obtain ⟨g, hg⟩ := hnflA
        exact ⟨g, by rw [hfaAll "nfl" (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg⟩)
      (by
        obtain ⟨g, hg⟩ := hntgA
        exact ⟨g, by rw [hfaAll "ntg" (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg⟩)
  refine ⟨σ₅, K₁ + (K₂ + (K₃ + (elimCost n nf + K₅))),
    hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq hr₅))), ?_,
    R, RamElim.psum (augDeg D (fun v : Fin n => R (v : ℕ))),
    NT, k, RamElim.psum (augDeg D (fun v : Fin n => R (v : ℕ))) n,
    hrnk₅, ?_, hnoff₅, hntg₅, hmn₅,
    le_trans (sum_augDeg_le D (fun v : Fin n => R (v : ℕ))) (by omega), hcert, hincsr₅⟩
  · have hcost : RamAugment.augCost n W = 8000 * (n + W + 1) := rfl
    have hec : elimCost n nf = 600 * n + 600 * nf + 100 := rfl
    have e1 : (80 * d + 92) * m = 80 * (d * m) + 92 * m := by ring
    omega
  · rw [hfv₅ "kmax" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hkmax₄

/-! ### The frontier — **COMPLETE**

`RamAugment.Implements` is discharged in full by `implements` above;
nothing of the round is left open. What follows is the map of what the
file is built out of.

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
  `FillAcc` also records that the fill pointers of the *other* vertices
  are untouched (its `F` parameter), which is what lets a fill pass
  carry the prefix sums of the vertices it has not reached yet.
* `Guarded B n Kg grd fe Cap J` — the guard's contract, with the
  emitted set growing by `fe z`, a singleton when the guard fires and
  `∅` when it does not, so no decidability rides in the statement.
  `guardFrat_of_emits`, `guardAsmIn_of_emits` and
  `guardAsmTrans_of_emits` are the round's three guards, at
  `Ka + 8`, `Ka + 13` and `Ka + 24`; `emitBranch_run` is their common
  emitting branch and `stampCond` the read of a stamp cell.
  The two assembly guards carry a `Base` the accounting has already
  seen and the stamp `ste` never saw, with `Base ⊆ A` — that is what
  lets the assembly's *first* list (the old in-block, excluded by `sta`
  alone) run before the two stamped ones under one accounting.
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
* `rowTgt_out_eq`, `adjRow_eq` and `demandRow_eq`: a row of the
  out-blocks names what its owner points at, the in-block and the
  out-block of `i` are `valSet (adjSet D i)`, and the nested row is
  `valSet (demandOut D i)` — the two sets `RamAugment.asmStamp` stamps.
* `incsr_nodup` and `block_nodup`: a block that names a set of its own
  size names it once. The first is the assembly's freshness (the old
  in-block carries no duplicate), the second is `CsrSimple`'s `nodup`
  for every block structure a fill pass writes.
* `slotCnt_out_eq`: an out-slot names `w` exactly as often as `w` has
  in-neighbours. This is the one non-obvious *cost* fact of the round:
  `RamAugment.asmStamp` walks the out-block of every vertex the current
  one points at, and no constant bounds an out-block, so the pass is
  linear only by this exchange. `tile_filter_card` (the rows tile the
  slots) and `sum_slot_weight` (a weighted count over the slots is a
  weighted count over the targets) are what it is proved from, and
  `sum_slot_weight` is also what turns a per-slot cost into a bound.
  `arcs_le` (`m ≤ n · d`) is the other half of the arithmetic: it is
  what puts `d · m` inside `augWidth n d`.

All of it is checked on `RamAugment.Demo`'s four-vertex orientation in
the section above: the in-lists and out-lists read back off the block
structures, the fraternity enumeration coming out `1 | 0 | | ` with two
slots — the round's own reported `mf` — the exchange coming out at the
in-degrees, the two stamps coming out at the adjacency and the demand,
and the transitive enumeration coming out — guarded, at the round's own
ranking — at the two arcs `0 → 3`, `1 → 3` the example names.

**Done — the fraternity build, whole.** `fratPass_run`:
`RamAugment.fratPass` leaves `off`/`tgt` carrying
`RamElim.CsrSimple (fratGraph D) nf (RamElim.psum (fratDeg D)) FT`, the
engine's input surface, and `mf = nf = RamAugment.fratSlots D`, at a
cost of `(80·d + 92)·m + 106·n + 40`. Its three pieces are

* `fratEmit_run` / `fratClear_run` — the guarded nested walk and the
  walk that clears every stamp it could have set (`rowAcc_mono` is why
  the second covers the first), shared by both passes at two `Emits`;
* `fratCount_run` — the turn `c := 0`, `stf[i] := 1`, emit, clear,
  `stf[i] := 0`, `off[i+1] := c`, leaving `off (u+1) = fratDeg D u`;
* `fratFill_run` — the same turn with the fill pointer for its action,
  leaving each block naming `fratSet D u` once.

`sum_fratDeg` is `RamElim.psum (fratDeg D) n = fratSlots D`, which is
what makes `off n` the reported `mf`.

**Done — the elimination bridge.** `elimCert_spec`, the engine's five
phase specs re-sequenced at the one postcondition that has both the
certificate and the rank bound. See its docstring for the defect record:
it and `RamDriverCompose.elimRank_spec` die together when a wave that
may edit `RamElim` adds the conjunct to `RamElim.ElimMem`.

**Done — two of the assembly's four walks.** `asmStamp_run` (the two
stamps of a turn, at `b` — a set at `b = 1` and its erasure at `b = 0`,
by `adjRow_eq` and `demandRow_eq`) and `asmClearE_run` (the duplicate
stamps of a turn, cleared).

**Done — the assembly, whole.** The four walks of a turn, the two
passes, and the round.

* `asmEmit_run` is `RamAugment.asmEmit act`: three walks under one
  accounting. The old in-block runs unguarded through `emitAllRow_run`,
  its freshness `incsr_nodup` — a repeat inside the in-block of `i`
  would be two slots with the same target. The transitive candidates
  run through `emitNest_run` under `guardAsmTrans_of_emits` at
  `Base := rowTgt DO DT i`, `A := valSet (adjSet D i)`,
  `Dm := valSet (demandOut D i)` and `R` the rank array, with
  `hBA : Base ⊆ A` off `rowTgt_eq_inN` and `adjSet = inN ∪ outSet`. The
  engine's own in-block runs through `emitRow_run` under
  `guardAsmIn_of_emits` at the same `Base` and `E₀` the transitive set.
  `asmRow_eq` reads the union — associated by `Finset.union_assoc` as
  `(Base ∪ T) ∪ F` — as `valSet ((augOr D ρ).inN i)`, which is also the
  capacity all three run inside. The array facts the walks need but do
  not carry — `AsmArr`, the stamp `std` and the rank array — ride in
  the accounting through `Emits.and`.
* `asmRow_run` is `asmStamp_run 1`, `asmEmit_run`, `asmStamp_run 0`,
  `asmClearE_run`. All three stamps come back zero: the `b = 0` walk's
  set is the `b = 1` walk's on the nose for `sta` and `std`, and for
  `ste` the guard's emitted set sits inside what `asmClearE` clears, by
  `rowAcc_mono` (the guards' `fe z ⊆ {z}`).
* `asmCount_run` and `asmFill_run` are `forVerts_run` over
  `asmRow_run` at `cntAcc_emits` and at `fillAcc_emits "ntg" "nfl"`,
  exactly as `fratCount_run` and `fratFill_run` are. The new degrees
  are `augDeg D ρ`, the blocks `augSet D ρ`; `sum_augDeg_le` is the
  `m' ≤ n²` that `fillAcc_emits`'s capacity wants (`augWidth n d ≤ W`
  gives `n² < W`). `asmPass_run` adds `prefixPass_run "noff" "nfl"` and
  the report `mn := noff[n]`, and reads the result back as
  `InCsr (augOr D ρ) m'`.
* **The cost exchange.** `asmStamp_run`'s bound is *not* a constant
  times the row length — its third walk charges the out-block of every
  vertex the out-block of `i` names. Summed over `i` that is
  `∑_{p < m} outdeg (OT p)`; `tile_sum` splits the per-row sums into
  the whole-array one, `sum_slot_weight` turns it into
  `∑_u slotCnt OT m u · outdeg u`, and `slotCnt_out_eq` into
  `∑_u inDeg D u · outdeg u ≤ d · m`. That is `asm_cost_le`, and it is
  the only place the exchange is needed.

**Done — the round.** `implements`:

    theorem implements {B n d nf W m : ℕ} {D : Orientation n}
        {DO DT : ℕ → ℕ} : RamAugment.Implements B n d nf W m D DO DT

with no theorem-level hypotheses, so
`fun _ _ _ _ _ _ _ => implements` inhabits `RamDriver.AugAvail B n`.
`RamAugment.ElimAvail` is *unused*: the engine enters through
`elimCert_spec`. The five phases are `outPass_run`, `fratPass_run`,
`alvSet_run`, `elimCert_spec` (at `ns = nf`, with
`RamElim.masked_of_all_alive` turning the all-ones mask back into
`fratGraph D`), and `asmPass_run`; `RamAugment.AugPre`'s twenty-seven
clauses cross the phases by the array frames each of the five exports,
and the elimination's by `a ∉ RamElim.elimCom.warrs`.

**The cost, and why it fits.** Every walk is charged per slot of the
block structure it walks. `outPass_run` is `42·m + 63·n + 24`,
`fratPass_run` is `(80·d + 92)·m + 106·n + 40`, `alvSet_run` is
`11·n + 8`, the engine's is `elimCost n nf = 600·n + 600·nf + 100`,
`asmCount_run` is `109·(d·m) + 187·m + 42·me + 147·n + 8` and
`asmFill_run` is `115·(d·m) + 193·m + 48·me + 140·n + 8`, so
`asmPass_run` is `224·(d·m) + 380·m + 90·me + 310·n + 27`. With
`arcs_le` (`m ≤ n·d`) every `d·m` is at most `n·d² ≤ n·(d+1)² ≤
augWidth n d ≤ W`; `nf = fratSlots D < augWidth n d ≤ W`, `me ≤ nf`,
`m ≤ W` and `n < W`. The sum is `1508·W + 1090·n + 199`, one order
inside `RamAugment.augCost`'s `8000·(n + W + 1)`. -/

end Lax3Proofs.RamDriverAugment
