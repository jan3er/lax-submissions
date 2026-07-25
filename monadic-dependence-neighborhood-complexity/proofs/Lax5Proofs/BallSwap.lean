import Lax5Proofs.LocalTypes
import Lax5Proofs.EFAgreement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
The ball-swap lemma: the locality core of the Adler–Adler argument.

Setting: a colored graph `G` with a small deleted set `S`; `H` is `G`
with all edges at `S` removed, and all distances are `H`-distances (so
`S`-vertices are isolated and unreachable).  Two centers `w₁, w₂` far
apart in `H` have equal rank-`lvl q q` local types of their decorated
radius-`RR q` balls, where the decoration records colors and adjacency
to the (enumerated) deleted set.

The swap lemma builds a back-and-forth system whose budget-`q` position
contains `{v ↦ v, w₁ ↦ w₂, w₂ ↦ w₁}` for any `v` that is `H`-far from
both centers (or deleted).  Every formula of quantifier rank at most
`q` therefore cannot distinguish `(v, w₁)` from `(v, w₂)` *in `G`* —
the deleted set is handled entirely by the decoration, so no formula
rewriting for vertex deletions is ever needed.

A position is one mirrored tuple pair `(mt, mt')` — matched entry lists
of the two ball regions with a single local-type equality — plus
identity pairs that are either deleted vertices (decoration-transparent)
or `3^j`-far from every mirrored entry.  Each position pair is a
mirrored pair in one of its two orientations, or an identity pair.
Spoiler moves near either ball region extend the mirrored tuples by the
local-type extension property; distance transfer keeps the answer near
the old entries, which maintains the farness clauses; geometric decay
(`3^j` thresholds against `reach`-bounded growth) keeps identity
elements clear of the mirrored regions forever.  Everything else is
answered by the identity, which is why no threshold counting or basic
local sentences appear: both sides of the game are the same graph.
-/

namespace Lax5Proofs.BallSwap

open Lax5Proofs.LocalTypes Lax5Proofs.EFAgreement FirstOrder Lax5.Transductions

/-! ### Numeric bookkeeping -/

/-- The local-type level carried at game budget `j`. -/
def lvl (q j : ℕ) : ℕ := j + 2 * q + 4

/-- The ball radius. -/
def RR (q : ℕ) : ℕ := 3 ^ (q + 2)

/-- Distance bound from the centers for mirrored entries at budget
`j`: the growth room already consumed. -/
def reach (q j : ℕ) : ℕ := 3 ^ q - 3 ^ j

private lemma lvl_succ (q j : ℕ) : lvl q (j + 1) = lvl q j + 1 := by
  simp only [lvl]; omega

private lemma one_le_pow3 (j : ℕ) : 1 ≤ 3 ^ j :=
  Nat.one_le_pow j 3 (by omega)

private lemma pow3_le_pow3 {j j' : ℕ} (h : j ≤ j') : 3 ^ j ≤ 3 ^ j' :=
  Nat.pow_le_pow_right (by omega) h

private lemma pow3_le_pow2_lvl (q j : ℕ) (hj : j ≤ q) :
    3 ^ j ≤ 2 ^ lvl q j := by
  calc 3 ^ j ≤ 4 ^ q := le_trans (pow3_le_pow3 hj)
        (Nat.pow_le_pow_left (by omega) q)
    _ = 2 ^ (2 * q) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    _ ≤ 2 ^ lvl q j := Nat.pow_le_pow_right (by omega) (by simp only [lvl]; omega)

private lemma reach_le (q j : ℕ) : reach q j ≤ 3 ^ q := Nat.sub_le _ _

private lemma reach_mono (q : ℕ) {j j' : ℕ} (h : j ≤ j') :
    reach q j' ≤ reach q j :=
  Nat.sub_le_sub_left (pow3_le_pow3 h) _

private lemma reach_succ_add (q j : ℕ) (hj : j + 1 ≤ q) :
    reach q (j + 1) + 3 ^ j ≤ reach q j := by
  have h1 : (3 : ℕ) ^ (j + 1) = 3 * 3 ^ j := by rw [pow_succ]; ring
  have h2 : (3 : ℕ) ^ (j + 1) ≤ 3 ^ q := pow3_le_pow3 hj
  have h3 := one_le_pow3 j
  simp only [reach]
  omega

private lemma reach_add_le_R (q j : ℕ) (hj : j ≤ q) :
    reach q j + 3 ^ j ≤ RR q := by
  have h1 := reach_le q j
  have h2 : (3 : ℕ) ^ j ≤ 3 ^ q := pow3_le_pow3 hj
  have h3 : (3 : ℕ) ^ (q + 2) = 9 * 3 ^ q := by rw [pow_add]; ring
  have h4 := one_le_pow3 q
  simp only [RR]
  omega

private lemma reach_le_R (q j : ℕ) : reach q j ≤ RR q := by
  have h1 := reach_le q j
  have h3 : (3 : ℕ) ^ (q + 2) = 9 * 3 ^ q := by rw [pow_add]; ring
  have h4 := one_le_pow3 q
  simp only [RR]
  omega

/-! ### The setting -/

variable {n k q smax : ℕ}

/-- The data and hypotheses of one swap situation. -/
structure Setting (n k q smax : ℕ) where
  /-- The original graph, whose atoms formulas see. -/
  G : SimpleGraph (Fin n)
  /-- The graph with all edges at `S` removed; all distances are taken
  here. -/
  H : SimpleGraph (Fin n)
  /-- The coloring. -/
  colors : Fin k → Set (Fin n)
  /-- The deleted set. -/
  S : Finset (Fin n)
  /-- An enumeration of the deleted set (repetitions allowed). -/
  senum : Fin smax → Fin n
  /-- The first center. -/
  w₁ : Fin n
  /-- The second center. -/
  w₂ : Fin n
  hH : ∀ a b, H.Adj a b ↔ (G.Adj a b ∧ a ∉ S ∧ b ∉ S)
  hsenum : ∀ s ∈ S, ∃ i, senum i = s
  hw₁ : w₁ ∉ S
  hw₂ : w₂ ∉ S
  hgap : ¬ WLE H w₁ w₂ (3 ^ (q + 2))

/-- The swapped setting. -/
def Setting.symm (st : Setting n k q smax) : Setting n k q smax where
  G := st.G
  H := st.H
  colors := st.colors
  S := st.S
  senum := st.senum
  w₁ := st.w₂
  w₂ := st.w₁
  hH := st.hH
  hsenum := st.hsenum
  hw₁ := st.hw₂
  hw₂ := st.hw₁
  hgap := fun h => st.hgap h.symm

/-- The decoration: color bits and adjacency bits to the enumerated
deleted set. -/
noncomputable def Setting.dec (st : Setting n k q smax) :
    Fin n → (Fin k → Bool) × (Fin smax → Bool) :=
  fun x => (fun i => pb (x ∈ st.colors i), fun i => pb (st.G.Adj (st.senum i) x))

/-- Walks in `H` cannot enter the deleted set. -/
lemma Setting.eq_of_walk_mem_S (st : Setting n k q smax) :
    ∀ {a b : Fin n}, b ∈ st.S → st.H.Walk a b → a = b := by
  intro a b hb p
  induction p with
  | nil => rfl
  | @cons u v w hadj _ ih =>
    have hv : v = w := ih hb
    subst hv
    exact absurd hb ((st.hH u v).mp hadj).2.2

lemma Setting.not_mem_S_of_wle (st : Setting n k q smax)
    {a b : Fin n} {d : ℕ} (ha : a ∉ st.S) (h : WLE st.H a b d) :
    b ∉ st.S := by
  intro hb
  obtain ⟨p, _⟩ := h
  exact ha ((st.eq_of_walk_mem_S hb p) ▸ hb)

lemma Setting.adjG_iff_adjH (st : Setting n k q smax)
    {a b : Fin n} (ha : a ∉ st.S) (hb : b ∉ st.S) :
    st.G.Adj a b ↔ st.H.Adj a b := by
  rw [st.hH]; tauto

/-! ### The mirrored core -/

/-- The mirrored tuple pair at budget `j`: matched entries of the two
ball regions with a local-type equality, anchored at the centers. -/
structure Core (st : Setting n k q smax) (j a : ℕ) where
  /-- The `w₁`-region entries. -/
  mt : Fin (a + 1) → Fin n
  /-- The matched `w₂`-region entries. -/
  mt' : Fin (a + 1) → Fin n
  anchor : mt 0 = st.w₁
  anchor' : mt' 0 = st.w₂
  teq : ltype st.H st.dec st.w₁ (RR q) (lvl q j) mt
      = ltype st.H st.dec st.w₂ (RR q) (lvl q j) mt'
  hr : ∀ i, WLE st.H st.w₁ (mt i) (reach q j)
  hr' : ∀ i, WLE st.H st.w₂ (mt' i) (reach q j)

/-- The mirrored core of the swapped setting. -/
def Core.symm {st : Setting n k q smax} {j a : ℕ} (C : Core st j a) :
    Core st.symm j a where
  mt := C.mt'
  mt' := C.mt
  anchor := C.anchor'
  anchor' := C.anchor
  teq := C.teq.symm
  hr := C.hr'
  hr' := C.hr

/-- Lowering the budget of a core. -/
def Core.lower {st : Setting n k q smax} {j a : ℕ} (C : Core st (j + 1) a) :
    Core st j a where
  mt := C.mt
  mt' := C.mt'
  anchor := C.anchor
  anchor' := C.anchor'
  teq := ltype_mono (by rw [← lvl_succ]; exact C.teq)
  hr := fun i => (C.hr i).mono (reach_mono q (Nat.le_succ j))
  hr' := fun i => (C.hr' i).mono (reach_mono q (Nat.le_succ j))

section CoreLemmas

variable {st : Setting n k q smax} {j a : ℕ} (C : Core st j a)

lemma Core.mt_not_S (i : Fin (a + 1)) : C.mt i ∉ st.S :=
  st.not_mem_S_of_wle st.hw₁ (C.hr i)

lemma Core.mt'_not_S (i : Fin (a + 1)) : C.mt' i ∉ st.S :=
  st.not_mem_S_of_wle st.hw₂ (C.hr' i)

lemma Core.adjH_iff (i i' : Fin (a + 1)) :
    st.H.Adj (C.mt i) (C.mt i') ↔ st.H.Adj (C.mt' i) (C.mt' i') :=
  ltype_adj_iff C.teq i i'

lemma Core.entry_eq_iff (i i' : Fin (a + 1)) :
    (C.mt i = C.mt i') ↔ (C.mt' i = C.mt' i') :=
  ltype_eq_iff C.teq i i'

lemma Core.adjG_iff (i i' : Fin (a + 1)) :
    st.G.Adj (C.mt i) (C.mt i') ↔ st.G.Adj (C.mt' i) (C.mt' i') := by
  rw [st.adjG_iff_adjH (C.mt_not_S i) (C.mt_not_S i'),
    st.adjG_iff_adjH (C.mt'_not_S i) (C.mt'_not_S i'), C.adjH_iff]

lemma Core.colors_iff (i : Fin (a + 1)) (ci : Fin k) :
    (C.mt i ∈ st.colors ci) ↔ (C.mt' i ∈ st.colors ci) := by
  have h := ltype_dec_eq C.teq i
  exact pb_eq_pb.mp (congrFun (congrArg Prod.fst h) ci)

lemma Core.sadj_iff (i : Fin (a + 1)) {o : Fin n} (ho : o ∈ st.S) :
    st.G.Adj o (C.mt i) ↔ st.G.Adj o (C.mt' i) := by
  obtain ⟨idx, hidx⟩ := st.hsenum o ho
  have h := ltype_dec_eq C.teq i
  have := pb_eq_pb.mp (congrFun (congrArg Prod.snd h) idx)
  rwa [hidx] at this

/-- Entries of the two regions are far apart. -/
lemma Core.cross_far (i i' : Fin (a + 1)) :
    ¬ WLE st.H (C.mt i) (C.mt' i') 2 := by
  intro h
  apply st.hgap
  refine (((C.hr i).trans h).trans (C.hr' i').symm).mono ?_
  have h1 := reach_le q j
  have h3 : (3 : ℕ) ^ (q + 2) = 9 * 3 ^ q := by rw [pow_add]; ring
  have h4 := one_le_pow3 q
  omega

lemma Core.cross_ne (i i' : Fin (a + 1)) : C.mt i ≠ C.mt' i' := by
  intro h
  exact C.cross_far i i' (h ▸ WLE.refl st.H (C.mt i) 2)

lemma Core.cross_nadj (i i' : Fin (a + 1)) :
    ¬ st.G.Adj (C.mt i) (C.mt' i') := by
  intro h
  refine C.cross_far i i' ?_
  have : st.H.Adj (C.mt i) (C.mt' i') :=
    (st.adjG_iff_adjH (C.mt_not_S i) (C.mt'_not_S i')).mp h
  exact (wle_one.mpr (Or.inr this)).mono (by omega)

end CoreLemmas

/-! ### Positions -/

/-- An identity element is far from every mirrored entry. -/
def OFar {st : Setting n k q smax} {j a : ℕ} (C : Core st j a)
    (o : Fin n) : Prop :=
  (∀ i, ¬ WLE st.H o (C.mt i) (3 ^ j)) ∧
  (∀ i, ¬ WLE st.H o (C.mt' i) (3 ^ j))

lemma OFar.symm {st : Setting n k q smax} {j a : ℕ} {C : Core st j a}
    {o : Fin n} (h : OFar C o) : OFar C.symm o :=
  ⟨h.2, h.1⟩

/-- The classification of a position pair: a mirrored pair in one of
its two orientations, or an identity pair on a deleted or far
element. -/
def PairForm {st : Setting n k q smax} {j a : ℕ} (C : Core st j a)
    (x y : Fin n) : Prop :=
  (∃ i, x = C.mt i ∧ y = C.mt' i) ∨
  (∃ i, x = C.mt' i ∧ y = C.mt i) ∨
  (x = y ∧ (x ∈ st.S ∨ (x ∉ st.S ∧ OFar C x)))

/-- The swap invariant on positions. -/
def SwapInv (st : Setting n k q smax) (j : ℕ)
    (p : List (Fin n × Fin n)) : Prop :=
  j ≤ q ∧ ∃ (a : ℕ) (C : Core st j a), ∀ xy ∈ p, PairForm C xy.1 xy.2

lemma PairForm.toSymm {st : Setting n k q smax} {j a : ℕ}
    {C : Core st j a} {x y : Fin n} (h : PairForm C x y) :
    PairForm C.symm x y := by
  rcases h with ⟨i, hx, hy⟩ | ⟨i, hx, hy⟩ | ⟨heq, hid⟩
  · exact Or.inr (Or.inl ⟨i, hx, hy⟩)
  · exact Or.inl ⟨i, hx, hy⟩
  · exact Or.inr (Or.inr ⟨heq, hid.imp id (fun h => ⟨h.1, h.2.symm⟩)⟩)

lemma PairForm.swap {st : Setting n k q smax} {j a : ℕ}
    {C : Core st j a} {x y : Fin n} (h : PairForm C x y) :
    PairForm C y x := by
  rcases h with ⟨i, hx, hy⟩ | ⟨i, hx, hy⟩ | ⟨heq, hid⟩
  · exact Or.inr (Or.inl ⟨i, hy, hx⟩)
  · exact Or.inl ⟨i, hy, hx⟩
  · exact Or.inr (Or.inr ⟨heq.symm, heq ▸ hid⟩)

lemma swapInv_symm {st : Setting n k q smax} {j : ℕ}
    {p : List (Fin n × Fin n)} (h : SwapInv st j p) :
    SwapInv st.symm j p := by
  obtain ⟨hj, a, C, hcorr⟩ := h
  exact ⟨hj, a, C.symm, fun xy hxy => (hcorr xy hxy).toSymm⟩

lemma swapInv_reverse {st : Setting n k q smax} {j : ℕ}
    {p : List (Fin n × Fin n)} (h : SwapInv st j p) :
    SwapInv st j (p.map Prod.swap) := by
  obtain ⟨hj, a, C, hcorr⟩ := h
  refine ⟨hj, a, C, fun xy hxy => ?_⟩
  obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hxy
  exact (hcorr ab hab).swap

/-! ### Atom preservation -/

section Atoms

variable {st : Setting n k q smax} {j a : ℕ} {C : Core st j a}

private lemma ofar_ne_mt {o : Fin n} (h : OFar C o) (i : Fin (a + 1)) :
    o ≠ C.mt i :=
  fun he => h.1 i (he ▸ WLE.refl st.H o (3 ^ j))

private lemma ofar_ne_mt' {o : Fin n} (h : OFar C o) (i : Fin (a + 1)) :
    o ≠ C.mt' i :=
  fun he => h.2 i (he ▸ WLE.refl st.H o (3 ^ j))

private lemma ofar_nadjG_mt {o : Fin n} (hoS : o ∉ st.S) (h : OFar C o)
    (i : Fin (a + 1)) : ¬ st.G.Adj o (C.mt i) := by
  intro hadj
  refine h.1 i ((wle_one.mpr (Or.inr ?_)).mono (one_le_pow3 j))
  exact (st.adjG_iff_adjH hoS (C.mt_not_S i)).mp hadj

private lemma ofar_nadjG_mt' {o : Fin n} (hoS : o ∉ st.S) (h : OFar C o)
    (i : Fin (a + 1)) : ¬ st.G.Adj o (C.mt' i) := by
  intro hadj
  refine h.2 i ((wle_one.mpr (Or.inr ?_)).mono (one_le_pow3 j))
  exact (st.adjG_iff_adjH hoS (C.mt'_not_S i)).mp hadj

/-- The adjacency and equality atoms transfer between any two
classified pairs. -/
lemma pair_transfer {x y x' y' : Fin n}
    (h1 : PairForm C x y) (h2 : PairForm C x' y') :
    (st.G.Adj x x' ↔ st.G.Adj y y') ∧ ((x = x') ↔ (y = y')) := by
  rcases h1 with ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨heq, hid⟩
  · -- first pair (mt i, mt' i)
    rcases h2 with ⟨i', rfl, rfl⟩ | ⟨i', rfl, rfl⟩ | ⟨heq', hid'⟩
    · exact ⟨C.adjG_iff i i', C.entry_eq_iff i i'⟩
    · refine ⟨iff_of_false (C.cross_nadj i i')
        (fun h => C.cross_nadj i' i h.symm), ?_⟩
      exact iff_of_false (C.cross_ne i i') (fun h => C.cross_ne i' i h.symm)
    · subst heq'
      rcases hid' with hS | ⟨hnS, hfar⟩
      · refine ⟨?_, ?_⟩
        · rw [st.G.adj_comm, st.G.adj_comm (C.mt' i)]
          exact C.sadj_iff i hS
        · exact iff_of_false (fun h => C.mt_not_S i (h ▸ hS))
            (fun h => C.mt'_not_S i (h ▸ hS))
      · refine ⟨?_, ?_⟩
        · exact iff_of_false (fun h => ofar_nadjG_mt hnS hfar i h.symm)
            (fun h => ofar_nadjG_mt' hnS hfar i h.symm)
        · exact iff_of_false (fun h => ofar_ne_mt hfar i h.symm)
            (fun h => ofar_ne_mt' hfar i h.symm)
  · -- first pair (mt' i, mt i)
    rcases h2 with ⟨i', rfl, rfl⟩ | ⟨i', rfl, rfl⟩ | ⟨heq', hid'⟩
    · refine ⟨iff_of_false (fun h => C.cross_nadj i' i h.symm)
        (C.cross_nadj i i'), ?_⟩
      exact iff_of_false (fun h => C.cross_ne i' i h.symm) (C.cross_ne i i')
    · exact ⟨(C.adjG_iff i i').symm, (C.entry_eq_iff i i').symm⟩
    · subst heq'
      rcases hid' with hS | ⟨hnS, hfar⟩
      · refine ⟨?_, ?_⟩
        · rw [st.G.adj_comm, st.G.adj_comm (C.mt i)]
          exact (C.sadj_iff i hS).symm
        · exact iff_of_false (fun h => C.mt'_not_S i (h ▸ hS))
            (fun h => C.mt_not_S i (h ▸ hS))
      · refine ⟨?_, ?_⟩
        · exact iff_of_false (fun h => ofar_nadjG_mt' hnS hfar i h.symm)
            (fun h => ofar_nadjG_mt hnS hfar i h.symm)
        · exact iff_of_false (fun h => ofar_ne_mt' hfar i h.symm)
            (fun h => ofar_ne_mt hfar i h.symm)
  · -- first pair identity
    subst heq
    rcases h2 with ⟨i', rfl, rfl⟩ | ⟨i', rfl, rfl⟩ | ⟨heq', _⟩
    · rcases hid with hS | ⟨hnS, hfar⟩
      · exact ⟨C.sadj_iff i' hS,
          iff_of_false (fun h => C.mt_not_S i' (h ▸ hS))
            (fun h => C.mt'_not_S i' (h ▸ hS))⟩
      · exact ⟨iff_of_false (ofar_nadjG_mt hnS hfar i')
          (ofar_nadjG_mt' hnS hfar i'),
          iff_of_false (ofar_ne_mt hfar i') (ofar_ne_mt' hfar i')⟩
    · rcases hid with hS | ⟨hnS, hfar⟩
      · exact ⟨(C.sadj_iff i' hS).symm,
          iff_of_false (fun h => C.mt'_not_S i' (h ▸ hS))
            (fun h => C.mt_not_S i' (h ▸ hS))⟩
      · exact ⟨iff_of_false (ofar_nadjG_mt' hnS hfar i')
          (ofar_nadjG_mt hnS hfar i'),
          iff_of_false (ofar_ne_mt' hfar i') (ofar_ne_mt hfar i')⟩
    · subst heq'
      exact ⟨Iff.rfl, Iff.rfl⟩

/-- The color atoms hold along each classified pair. -/
lemma pair_colors {x y : Fin n} (h : PairForm C x y) (ci : Fin k) :
    (x ∈ st.colors ci) ↔ (y ∈ st.colors ci) := by
  rcases h with ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨heq, _⟩
  · exact C.colors_iff i ci
  · exact (C.colors_iff i ci).symm
  · exact heq ▸ Iff.rfl

end Atoms

lemma atoms_of_swapInv {st : Setting n k q smax} {j : ℕ}
    {p : List (Fin n × Fin n)} (h : SwapInv st j p) :
    AtomPreserving st.G st.colors p := by
  obtain ⟨hj, a, C, hcorr⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x y x' y' hxy hx'y'
    exact (pair_transfer (hcorr _ hxy) (hcorr _ hx'y')).1
  · intro x y x' y' hxy hx'y'
    exact (pair_transfer (hcorr _ hxy) (hcorr _ hx'y')).2
  · intro x y ci hxy
    exact pair_colors (hcorr _ hxy) ci

/-! ### Extension -/

section Extension

variable {st : Setting n k q smax}

/-- The mirror extension: a Spoiler move within `3^j` of a `w₁`-region
entry is answered inside the `w₂`-region, with matched local types,
matched center distance, and matched nearness to the witnessing
entry. -/
lemma extend_mirror {j a : ℕ} (hj : j + 1 ≤ q) (C : Core st (j + 1) a)
    {x : Fin n} {i₀ : Fin (a + 1)} (hx : WLE st.H x (C.mt i₀) (3 ^ j)) :
    ∃ (y : Fin n) (C' : Core st j (a + 1)),
      C'.mt = Fin.snoc C.mt x ∧ C'.mt' = Fin.snoc C.mt' y ∧
      WLE st.H y (C.mt' i₀) (3 ^ j) := by
  -- x is within `reach q j` of the first center, hence in the ball
  have hxr : WLE st.H st.w₁ x (reach q j) :=
    ((C.hr i₀).trans hx.symm).mono (reach_succ_add q j hj)
  have hxball : x ∈ ballFinset st.H st.w₁ (RR q) :=
    mem_ballFinset.mpr (hxr.mono (reach_le_R q j))
  -- extend the local-type equality
  have hteq : ltype st.H st.dec st.w₁ (RR q) (lvl q j + 1) C.mt
      = ltype st.H st.dec st.w₂ (RR q) (lvl q j + 1) C.mt' := by
    rw [← lvl_succ]; exact C.teq
  obtain ⟨y, hyball, hteq'⟩ := ltype_ext hteq hxball
  -- the answer's center distance
  have hyr : WLE st.H st.w₂ y (reach q j) := by
    have := ltype_cdist_iff' hteq' (Fin.last (a + 1))
      (d := reach q j) (reach_le_R q j)
    simp only [Fin.snoc_last] at this
    exact this.mp hxr
  -- the answer's nearness to the witnessing entry
  have hyx : WLE st.H y (C.mt' i₀) (3 ^ j) := by
    have := ltype_wle_transfer hteq' (Fin.last (a + 1)) i₀.castSucc
      (3 ^ j) (reach q j) (pow3_le_pow2_lvl q j (by omega))
      (by simpa only [Fin.snoc_last] using hxr)
      (reach_add_le_R q j (by omega))
      (by simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hx)
    simpa only [Fin.snoc_last, Fin.snoc_castSucc] using this
  refine ⟨y, ⟨Fin.snoc C.mt x, Fin.snoc C.mt' y, ?_, ?_, hteq', ?_, ?_⟩,
    rfl, rfl, hyx⟩
  · rw [show (0 : Fin (a + 2)) = Fin.castSucc 0 from (Fin.castSucc_zero).symm,
      Fin.snoc_castSucc]
    exact C.anchor
  · rw [show (0 : Fin (a + 2)) = Fin.castSucc 0 from (Fin.castSucc_zero).symm,
      Fin.snoc_castSucc]
    exact C.anchor'
  · intro i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simpa only [Fin.snoc_last] using hxr
    · simpa only [Fin.snoc_castSucc] using
        (C.hr i').mono (reach_mono q (Nat.le_succ j))
  · intro i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simpa only [Fin.snoc_last] using hyr
    · simpa only [Fin.snoc_castSucc] using
        (C.hr' i').mono (reach_mono q (Nat.le_succ j))

/-- Lifting the classification of old pairs along a mirror
extension. -/
lemma pairForm_lift {j a : ℕ} {C : Core st (j + 1) a}
    {C' : Core st j (a + 1)} {xn yn : Fin n} {i₀ : Fin (a + 1)}
    (hmt : C'.mt = Fin.snoc C.mt xn) (hmt' : C'.mt' = Fin.snoc C.mt' yn)
    (hxn : WLE st.H xn (C.mt i₀) (3 ^ j))
    (hyn : WLE st.H yn (C.mt' i₀) (3 ^ j))
    {x y : Fin n} (h : PairForm C x y) : PairForm C' x y := by
  have hmt_cast : ∀ i : Fin (a + 1), C'.mt i.castSucc = C.mt i := by
    intro i; rw [hmt, Fin.snoc_castSucc]
  have hmt'_cast : ∀ i : Fin (a + 1), C'.mt' i.castSucc = C.mt' i := by
    intro i; rw [hmt', Fin.snoc_castSucc]
  rcases h with ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨heq, hid⟩
  · exact Or.inl ⟨i.castSucc, (hmt_cast i).symm, (hmt'_cast i).symm⟩
  · exact Or.inr (Or.inl ⟨i.castSucc, (hmt'_cast i).symm, (hmt_cast i).symm⟩)
  · refine Or.inr (Or.inr ⟨heq, hid.imp id (fun hf => ⟨hf.1, ?_, ?_⟩)⟩)
    · intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · rw [hmt, Fin.snoc_last]
        intro hw
        refine hf.2.1 i₀ ((hw.trans hxn).mono ?_)
        have h1 : (3 : ℕ) ^ (j + 1) = 3 * 3 ^ j := by rw [pow_succ]; ring
        have := one_le_pow3 j
        omega
      · rw [hmt_cast i']
        intro hw
        exact hf.2.1 i' (hw.mono (pow3_le_pow3 (Nat.le_succ j)))
    · intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · rw [hmt', Fin.snoc_last]
        intro hw
        refine hf.2.2 i₀ ((hw.trans hyn).mono ?_)
        have h1 : (3 : ℕ) ^ (j + 1) = 3 * 3 ^ j := by rw [pow_succ]; ring
        have := one_le_pow3 j
        omega
      · rw [hmt'_cast i']
        intro hw
        exact hf.2.2 i' (hw.mono (pow3_le_pow3 (Nat.le_succ j)))

/-- Lifting the classification of old pairs when only the budget
drops. -/
lemma pairForm_lower {j a : ℕ} {C : Core st (j + 1) a} {x y : Fin n}
    (h : PairForm C x y) : PairForm C.lower x y := by
  rcases h with ⟨i, hx, hy⟩ | ⟨i, hx, hy⟩ | ⟨heq, hid⟩
  · exact Or.inl ⟨i, hx, hy⟩
  · exact Or.inr (Or.inl ⟨i, hx, hy⟩)
  · refine Or.inr (Or.inr ⟨heq, hid.imp id (fun hf => ⟨hf.1, ?_, ?_⟩)⟩)
    · exact fun i hw => hf.2.1 i (hw.mono (pow3_le_pow3 (Nat.le_succ j)))
    · exact fun i hw => hf.2.2 i (hw.mono (pow3_le_pow3 (Nat.le_succ j)))

/-- The forward extension of the swap system. -/
lemma swapInv_forth {j : ℕ} {p : List (Fin n × Fin n)}
    (hp : SwapInv st (j + 1) p) (x : Fin n) :
    ∃ y, SwapInv st j ((x, y) :: p) := by
  classical
  obtain ⟨hj, a, C, hcorr⟩ := hp
  by_cases hnear1 : ∃ i₀, WLE st.H x (C.mt i₀) (3 ^ j)
  · obtain ⟨i₀, hx⟩ := hnear1
    obtain ⟨y, C', hmt, hmt', hy⟩ := extend_mirror hj C hx
    refine ⟨y, by omega, a + 1, C', ?_⟩
    intro xy hxy
    rcases List.mem_cons.mp hxy with rfl | hxy
    · exact Or.inl ⟨Fin.last _, by simp [hmt, Fin.snoc_last],
        by simp [hmt', Fin.snoc_last]⟩
    · exact pairForm_lift hmt hmt' hx hy (hcorr xy hxy)
  · by_cases hnear2 : ∃ i₀, WLE st.H x (C.mt' i₀) (3 ^ j)
    · obtain ⟨i₀, hx⟩ := hnear2
      obtain ⟨y, C', hmt, hmt', hy⟩ :=
        extend_mirror (st := st.symm) hj C.symm hx
      refine ⟨y, by omega, a + 1, C'.symm, ?_⟩
      intro xy hxy
      rcases List.mem_cons.mp hxy with rfl | hxy
      · refine Or.inr (Or.inl ⟨Fin.last _, ?_, ?_⟩)
        · show x = C'.mt (Fin.last _)
          rw [hmt, Fin.snoc_last]
        · show y = C'.mt' (Fin.last _)
          rw [hmt', Fin.snoc_last]
      · exact (pairForm_lift (C := C.symm) hmt hmt' hx hy
          (hcorr xy hxy).toSymm).toSymm
    · -- identity extension
      push_neg at hnear1 hnear2
      refine ⟨x, by omega, a, C.lower, ?_⟩
      intro xy hxy
      rcases List.mem_cons.mp hxy with rfl | hxy
      · by_cases hxS : x ∈ st.S
        · exact Or.inr (Or.inr ⟨rfl, Or.inl hxS⟩)
        · exact Or.inr (Or.inr ⟨rfl, Or.inr ⟨hxS, hnear1, hnear2⟩⟩)
      · exact pairForm_lower (hcorr xy hxy)

/-- The backward extension, by reversal symmetry. -/
lemma swapInv_back {j : ℕ} {p : List (Fin n × Fin n)}
    (hp : SwapInv st (j + 1) p) (y : Fin n) :
    ∃ x, SwapInv st j ((x, y) :: p) := by
  obtain ⟨x, hx⟩ := swapInv_forth (swapInv_reverse hp) y
  refine ⟨x, ?_⟩
  have h2 := swapInv_reverse hx
  simpa [List.map_map, Function.comp_def, Prod.swap_swap] using h2

end Extension

/-! ### The swap system and the swap lemma -/

/-- The back-and-forth system of the swap argument. -/
noncomputable def swapSystem (st : Setting n k q smax) :
    EFSystem st.G st.colors where
  F := fun j p => SwapInv st j p
  atoms := fun h => atoms_of_swapInv h
  forth := fun h x => swapInv_forth h x
  back := fun h y => swapInv_back h y

/-- The ball-swap lemma: equal local types of the decorated balls of
two far-apart centers make them indistinguishable, over the original
graph `G`, by rank-`q` formulas with a far (or deleted) parameter. -/
theorem swap_agreement (st : Setting n k q smax)
    (hcolor : ltype st.H st.dec st.w₁ (RR q) (lvl q q)
        (fun _ : Fin 1 => st.w₁)
      = ltype st.H st.dec st.w₂ (RR q) (lvl q q) (fun _ : Fin 1 => st.w₂))
    {v : Fin n}
    (hv : v ∈ st.S ∨ (¬ WLE st.H v st.w₁ (3 ^ q) ∧ ¬ WLE st.H v st.w₂ (3 ^ q)))
    (φ : (withColors Language.graph k).Formula (Fin 2)) (hq : qrank φ ≤ q) :
    RealizeIn st.G.structure st.colors φ ![v, st.w₁]
      ↔ RealizeIn st.G.structure st.colors φ ![v, st.w₂] := by
  classical
  let hC : Core st q 0 :=
    { mt := fun _ => st.w₁
      mt' := fun _ => st.w₂
      anchor := rfl
      anchor' := rfl
      teq := hcolor
      hr := fun _ => WLE.refl st.H st.w₁ _
      hr' := fun _ => WLE.refl st.H st.w₂ _ }
  have hinit : SwapInv st q [(v, v), (st.w₁, st.w₂), (st.w₂, st.w₁)] := by
    refine ⟨le_refl q, 0, hC, ?_⟩
    intro xy hxy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hxy
    rcases hxy with rfl | rfl | rfl
    · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      by_cases hvS : v ∈ st.S
      · exact Or.inl hvS
      · rcases hv with hvS' | ⟨h1, h2⟩
        · exact absurd hvS' hvS
        · exact Or.inr ⟨hvS, fun _ => h1, fun _ => h2⟩
    · exact Or.inl ⟨0, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨0, rfl, rfl⟩)
  refine realizeIn_agreement (swapSystem st) φ hq hinit ?_
  intro i
  refine Fin.cases ?_ (fun i₁ => ?_) i
  · exact List.mem_cons_self ..
  · refine Fin.cases ?_ (fun i₂ => i₂.elim0) i₁
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

end Lax5Proofs.BallSwap
