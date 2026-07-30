import Lax13Proofs.Lib.Csr

/-!
**The widened block-structure relation (rebase B5).**

The reasoning kit's `Csr o t nv ns V off tgt σ` couples the target
array's *length* to the last offset — `σ.arrs t = arrOf ns tgt` with
`off nv = ns`. That coupling is what pins `tgt` at the level's slot
count through `RamElim.ElimPre`, `RamAugment.AugPre` and the four
search/cover/scatter files, and it is what the `R > 0` ordering phase
cannot satisfy: a round's fraternity graph needs more slots than the
level's `ns` (`TgtCoupling`'s `K₁,₄` refutation, machine half in
`TgtWidenProbe`), and an IMP+ run cannot re-allocate an array.

`CsrW` is the relation with the two numbers separated: the target array
is materialized at a caller-chosen physical width `nt`, the structure
occupies the prefix `ns = off nv ≤ nt`, and every *occupied* slot is
below `V`. This is `RamElim.ElimPre`'s scratch-width discipline
("caller-chosen width, the call's slot count only a lower bound")
applied to the one array that still lacked it. `Csr` is exactly the
case `nt = ns` (`csrW_of_csr` / `csr_of_csrW`), so the widening is a
hypothesis generalization: every landed walk built over `Csr` threads
through `CsrW` with its reads untouched — a row's slots live below
`off (v+1) ≤ ns ≤ nt`, so every read the old relation justified the
widened one justifies too.

The kit's design note carries over: the *scan* combinators
(`Csr.rowScan_spec`, `Csr.ownerScan_spec`) never mention the relation —
they take the numbers — so they serve the widened callers as they are.
Only the two straight-line reads package the relation, and those two
are re-derived here at the widened one: `loadRow_spec` and `slot_spec`,
statement and proof mirroring `Lib/Csr.lean`'s with the width threaded.
This file deliberately lives in the consumer package (ledger L3
discipline of the integration wave): `word-ram/` is another wave's
surface; if the kit later adopts the decoupled relation, dedupe then.
-/

namespace Lax3Proofs.CsrWide

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {B nv ns nt V i k p u : ℕ} {o t v j w b : String} {off tgt : ℕ → ℕ} {σ : Env}

/-! ### The relation -/

/-- `CsrW o t nv ns nt V off tgt σ`: in `σ`, the array named `o` is the
length-`nv + 1` array of offsets `off`, the array named `t` is the
length-**`nt`** array of targets `tgt`, the offsets are nondecreasing,
the last one is the slot count `ns ≤ nt`, and every target *below the
slot count* is smaller than `V`. Row `v` is the stretch
`off v … off (v + 1) − 1`; the cells at `ns … nt − 1` are the widened
array's tail and no clause speaks about them. -/
def CsrW (o t : String) (nv ns nt V : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  σ.arrs o = arrOf (nv + 1) off ∧ σ.arrs t = arrOf nt tgt ∧
    (∀ i', i' < nv → off i' ≤ off (i' + 1)) ∧ off nv = ns ∧ ns ≤ nt ∧
    ∀ p', p' < ns → tgt p' < V

/-- The kit's relation is the widened one at `nt = ns`. -/
theorem csrW_of_csr (hc : Csr o t nv ns V off tgt σ) : CsrW o t nv ns ns V off tgt σ :=
  ⟨hc.offArr, hc.tgtArr, fun _ hi => hc.off_le_succ hi, hc.last, le_rfl,
    fun _ hp => hc.target hp⟩

/-- And the widened relation at `nt = ns` is the kit's. -/
theorem csr_of_csrW (hc : CsrW o t nv ns ns V off tgt σ) : Csr o t nv ns V off tgt σ :=
  ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.2⟩

/-- The offsets array. -/
theorem CsrW.offArr (hc : CsrW o t nv ns nt V off tgt σ) : σ.arrs o = arrOf (nv + 1) off :=
  hc.1

/-- The targets array, at the physical width. -/
theorem CsrW.tgtArr (hc : CsrW o t nv ns nt V off tgt σ) : σ.arrs t = arrOf nt tgt := hc.2.1

/-- The offsets do not decrease, one step at a time. -/
theorem CsrW.off_le_succ (hc : CsrW o t nv ns nt V off tgt σ) (hi : i < nv) :
    off i ≤ off (i + 1) := hc.2.2.1 i hi

/-- The last offset is the slot count. -/
theorem CsrW.last (hc : CsrW o t nv ns nt V off tgt σ) : off nv = ns := hc.2.2.2.1

/-- The slot count is a lower bound of the width — the widening's one
new fact. -/
theorem CsrW.ns_le (hc : CsrW o t nv ns nt V off tgt σ) : ns ≤ nt := hc.2.2.2.2.1

/-- Every occupied target is below the bound. -/
theorem CsrW.target (hc : CsrW o t nv ns nt V off tgt σ) (hp : p < ns) : tgt p < V :=
  hc.2.2.2.2.2 p hp

/-- **The offsets do not decrease.** -/
theorem CsrW.mono (hc : CsrW o t nv ns nt V off tgt σ) (hik : i ≤ k) (hk : k ≤ nv) :
    off i ≤ off k := by
  induction k with
  | zero => have : i = 0 := by omega
            subst this; exact le_rfl
  | succ k ih =>
      by_cases hik' : i ≤ k
      · exact le_trans (ih hik' (by omega)) (hc.off_le_succ (by omega))
      · have : i = k + 1 := by omega
        subst this; exact le_rfl

/-- **Every row ends inside the occupied prefix** — and hence inside
the widened array. -/
theorem CsrW.le_ns (hc : CsrW o t nv ns nt V off tgt σ) (hi : i ≤ nv) : off i ≤ ns :=
  hc.last ▸ hc.mono hi le_rfl

/-- A row ends inside the occupied prefix. -/
theorem CsrW.row_le (hc : CsrW o t nv ns nt V off tgt σ) (hv : i < nv) : off (i + 1) ≤ ns :=
  hc.le_ns (by omega)

/-- The lengths, for a read's range condition. The target array's is
the *width*. -/
theorem CsrW.length_off (hc : CsrW o t nv ns nt V off tgt σ) : (σ.arrs o).length = nv + 1 := by
  rw [hc.offArr, length_arrOf]

theorem CsrW.length_tgt (hc : CsrW o t nv ns nt V off tgt σ) : (σ.arrs t).length = nt := by
  rw [hc.tgtArr, length_arrOf]

/-- Reading an offset. -/
theorem CsrW.getD_off (hc : CsrW o t nv ns nt V off tgt σ) (hi : i ≤ nv) :
    (σ.arrs o).getD i 0 = off i := by
  rw [hc.offArr, getD_arrOf off (by omega)]

/-- Reading an occupied target: the slot is inside the widened array
because the occupied prefix is. -/
theorem CsrW.getD_tgt (hc : CsrW o t nv ns nt V off tgt σ) (hp : p < ns) :
    (σ.arrs t).getD p 0 = tgt p := by
  rw [hc.tgtArr, getD_arrOf tgt (lt_of_lt_of_le hp hc.ns_le)]

/-- An offset in the `getElem?` form the walk's discharger normalizes
into. -/
theorem CsrW.off_getD (hc : CsrW o t nv ns nt V off tgt σ) (hi : i ≤ nv) :
    (σ.arrs o)[i]?.getD 0 = off i := by
  rw [← List.getD_eq_getElem?_getD, hc.getD_off hi]

/-- And an occupied target in the same form. -/
theorem CsrW.tgt_getD (hc : CsrW o t nv ns nt V off tgt σ) (hp : p < ns) :
    (σ.arrs t)[p]?.getD 0 = tgt p := by
  rw [← List.getD_eq_getElem?_getD, hc.getD_tgt hp]

/-- Every occupied target is a word as soon as `V` is. -/
theorem CsrW.lt (hc : CsrW o t nv ns nt V off tgt σ) (hVB : V ≤ B) (hp : p < ns) :
    tgt p < B :=
  lt_of_lt_of_le (hc.target hp) hVB

/-- Every offset is a word as soon as the slot count is. -/
theorem CsrW.off_lt (hc : CsrW o t nv ns nt V off tgt σ) (hnsB : ns < B) (hi : i ≤ nv) :
    off i < B :=
  lt_of_le_of_lt (hc.le_ns hi) hnsB

/-- **A slot has an owner**, exactly as at the pinned width: the extent
clause survives the widening untouched. -/
theorem CsrW.owner_lt (hc : CsrW o t nv ns nt V off tgt σ) (hu : u ≤ nv) (hlo : off u ≤ p)
    (hp : p < ns) : u < nv := by
  rcases Nat.lt_or_ge u nv with h | h
  · exact h
  · exfalso
    have hun : u = nv := by omega
    rw [hun, hc.last] at hlo
    omega

/-! ### Transport

The relation is a statement about two arrays, so it crosses any phase
that writes something else — the kit's `Csr.of_eq` family, mirrored at
the widened relation because a walk that loads a row after an
extraction (`RamElim.elimTake_run`) transports it across the write. -/

/-- **The transport lemma.** Any environment agreeing on the two arrays
satisfies the relation. -/
theorem CsrW.of_eq (hc : CsrW o t nv ns nt V off tgt σ) {σ' : Env}
    (ho : σ'.arrs o = σ.arrs o) (ht : σ'.arrs t = σ.arrs t) :
    CsrW o t nv ns nt V off tgt σ' :=
  ⟨by rw [ho, hc.offArr], by rw [ht, hc.tgtArr], hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1,
    hc.2.2.2.2.2⟩

/-- A scalar assignment leaves the structure alone. -/
theorem CsrW.setVar (hc : CsrW o t nv ns nt V off tgt σ) (y : String) (x : ℕ) :
    CsrW o t nv ns nt V off tgt (σ.setVar y x) :=
  hc.of_eq (by rw [arrs_setVar]) (by rw [arrs_setVar])

/-- A store into another array leaves the structure alone. -/
theorem CsrW.setArr_of_ne (hc : CsrW o t nv ns nt V off tgt σ) (hbo : b ≠ o) (hbt : b ≠ t)
    (k x : ℕ) : CsrW o t nv ns nt V off tgt (σ.setArr b k x) :=
  hc.of_eq (by rw [arrs_setArr, if_neg (Ne.symm hbo)])
    (by rw [arrs_setArr, if_neg (Ne.symm hbt)])

/-! ### The two straight-line reads, at the widened relation

Statement and proof mirror `Lib/Csr.lean`'s `loadRow_spec` and
`slot_spec`; the scan combinators need no mirror, since they never
mention the relation. -/

/-- What every operation needs: the widened relation, the target bound
inside the word bound, and a slot count that is a word. The width `nt`
needs no bound of its own — nothing reads above the occupied prefix. -/
abbrev PreW (o t : String) (nv ns nt V B : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  CsrW o t nv ns nt V off tgt σ ∧ V ≤ B ∧ ns < B

/-- What `loadRow` needs on top of that. -/
abbrev RowPreW (o t v : String) (nv ns nt V B : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  PreW o t nv ns nt V B off tgt σ ∧ σ.vars v < nv ∧ σ.vars v + 1 < B

/-- What `slot` needs on top of that: a pointer inside the *occupied*
prefix. -/
abbrev SlotPreW (o t j : String) (nv ns nt V B : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  PreW o t nv ns nt V B off tgt σ ∧ σ.vars j < ns

/-- What `loadRow` leaves, with the state handed back — the kit's
`LoadRowPost` at the widened relation. -/
abbrev LoadRowPostW (o t v j jend : String) (nv ns nt V : ℕ) (off tgt : ℕ → ℕ)
    (σ σ' : Env) : Prop :=
  CsrW o t nv ns nt V off tgt σ' ∧ σ'.vars j = off (σ.vars v) ∧
    σ'.vars jend = off (σ.vars v + 1) ∧
    σ' = (σ.setVar j (off (σ.vars v))).setVar jend (off (σ.vars v + 1))

/-- What `slot` leaves: the target at the pointer. -/
abbrev SlotPostW (o t j w : String) (nv ns nt V : ℕ) (off tgt : ℕ → ℕ) (σ σ' : Env) : Prop :=
  CsrW o t nv ns nt V off tgt σ' ∧ σ'.vars w = tgt (σ.vars j)

/-- **Loading a row's bounds, at the widened relation.** The two reads
are offset reads, which the widening does not touch; the proof is the
kit's with `CsrW`'s projections. -/
theorem loadRow_spec (B nv ns nt V : ℕ) (o t v j jend : String) (off tgt : ℕ → ℕ)
    (hvj : v ≠ j) (hjje : j ≠ jend) :
    Spec B (RowPreW o t v nv ns nt V B off tgt) (Csr.loadRow o v j jend)
      (LoadRowPostW o t v j jend nv ns nt V off tgt) 8 := by
  refine Spec.of_exists (fun σ hσ => ?_)
  have hc := hσ.1.1
  have hnsB := hσ.1.2.2
  have hv := hσ.2.1
  have e₁ : (Expr.get o (.var v)).evalB B σ = some (off (σ.vars v)) :=
    evalB_get (evalB_var (by omega)) (by rw [hc.offArr, getElem?_arrOf off (by omega)])
      (hc.off_lt hnsB (by omega))
  have hvars : (σ.setVar j (off (σ.vars v))).vars v = σ.vars v := by simp [hvj]
  have ev : (Expr.var v).evalB B (σ.setVar j (off (σ.vars v))) = some (σ.vars v) := by
    have h := evalB_var (B := B) (x := v) (σ := σ.setVar j (off (σ.vars v)))
      (by rw [hvars]; omega)
    rwa [hvars] at h
  have e₂ : (Expr.get o (.add (.var v) (.lit 1))).evalB B (σ.setVar j (off (σ.vars v)))
      = some (off (σ.vars v + 1)) := by
    refine evalB_get (k := σ.vars v + 1) ?_ ?_ (hc.off_lt hnsB hv)
    · simp only [evalB_bin_iff]
      exact ⟨σ.vars v, 1, ev, by simp; omega, by simp [Bop.apply], by omega⟩
    · rw [arrs_setVar, hc.offArr, getElem?_arrOf off (by omega)]
  refine ⟨_, 8, ((Run.assign e₁).seq (Run.assign e₂)).mono (by simp), le_rfl, ?_, ?_, ?_, rfl⟩
  · simpa [CsrW] using hc
  · simp [hjje]
  · simp

/-- The read obligations of a target read at the widened relation, in
the two forms the walk's discharger normalizes into. -/
theorem slotRead_of_preW (hσ : SlotPreW o t j nv ns nt V B off tgt σ) :
    σ.vars j < (σ.arrs t).length ∧ (σ.arrs t).getD (σ.vars j) 0 < B ∧
      (σ.arrs t)[σ.vars j]?.getD 0 < B ∧ σ.vars j < B := by
  have hc := hσ.1.1
  have hval : (σ.arrs t).getD (σ.vars j) 0 < B := by
    rw [hc.getD_tgt hσ.2]; exact hc.lt hσ.1.2.1 hσ.2
  exact ⟨by rw [hc.length_tgt]; exact lt_of_lt_of_le hσ.2 hc.ns_le, hval,
    by rwa [← List.getD_eq_getElem?_getD], by have := hσ.1.2.2; omega⟩

/-- **Reading the target at the pointer, at the widened relation.** -/
theorem slot_spec (B nv ns nt V : ℕ) (o t j w : String) (off tgt : ℕ → ℕ) :
    Spec B (SlotPreW o t j nv ns nt V B off tgt) (Csr.slot t j w)
      (SlotPostW o t j w nv ns nt V off tgt) 3 := by
  refine Spec.of_exists (fun σ hσ => ?_)
  have hc := hσ.1.1
  obtain ⟨-, hval, -, hjB⟩ := slotRead_of_preW hσ
  have e : (Expr.get t (.var j)).evalB B σ = some (tgt (σ.vars j)) :=
    evalB_get (evalB_var hjB)
      (by rw [hc.tgtArr, getElem?_arrOf tgt (lt_of_lt_of_le hσ.2 hc.ns_le)])
      (by rwa [hc.getD_tgt hσ.2] at hval)
  refine ⟨_, 3, (Run.assign e).mono (by simp), le_rfl, ?_, by simp⟩
  simpa [CsrW] using hc

/-! ### Falsification

The relation's one authored delta is the decoupling itself, and the
refutable readings are the two couplings it removes. Both are refuted
on the same two-row structure — offsets `0, 1, 2`, slot count `2` —
materialized in a width-`4` array. -/

section Falsification

private def demoOff : ℕ → ℕ := fun i => min i 2
private def demoTgt : ℕ → ℕ := fun p => if p < 2 then 1 - p else 7

private def demoEnv : Env where
  vars := fun _ => 0
  arrs := fun a => if a = "o" then arrOf 3 demoOff else if a = "t" then arrOf 4 demoTgt else []
  inp := []
  out := []

-- the widened relation holds of the widened state …
example : CsrW "o" "t" 2 2 4 2 demoOff demoTgt demoEnv := by
  refine ⟨by simp [demoEnv], by simp [demoEnv], ?_, rfl, by omega, ?_⟩
  · intro i hi
    interval_cases i <;> simp [demoOff]
  · intro p hp
    interval_cases p <;> simp [demoTgt]

-- … **refuted**: the kit's relation does not — the length coupling
-- `arrs t = arrOf ns tgt` fails at any function, because the array's
-- length is the width, not the slot count.
example : ¬ ∃ tgt', Csr "o" "t" 2 2 2 demoOff tgt' demoEnv := by
  rintro ⟨tgt', h⟩
  have hlen : (demoEnv.arrs "t").length = 2 := by rw [h.tgtArr, length_arrOf]
  simp [demoEnv] at hlen

-- **refuted**: the tail above the slot count cannot owe the target
-- bound — the widened state's tail holds `7 ≥ V = 2`, and the relation
-- above holds regardless. So the `V`-clause must be cut to the
-- occupied prefix, as `CsrW` states it.
example : ¬ ∀ p, p < 4 → demoTgt p < 2 := by
  intro h
  have := h 2 (by omega)
  simp [demoTgt] at this

end Falsification

end Lax3Proofs.CsrWide
