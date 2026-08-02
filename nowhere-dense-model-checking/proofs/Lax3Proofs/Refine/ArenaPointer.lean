import Lax3Proofs.RamDriver
import Lax3Proofs.Refine.MassMath

/-!
**The two arena pointers, read at the ordering's degree** — ND-MC
rebase, wave E-mem, leaf W3.

This file holds the mathematics `Refine.ArenaWidth` §5 introduced and
the two slot readings `Refine.CoverWidth` §1 derived from it, and it
holds them *here* for one reason: the **import order**.

`Refine.ArenaWidth` imports `Refine.BridgeSeamProbe`, which imports
`RamDriverRoot` — the probe's finding 3 is a statement *about* the
landed root theorem, so it has to see it. `Refine.CoverWidth` is above
`ArenaWidth` again. So everything W1 and W2 proved about the arena
pointers sat strictly **above** the root, and W3 — which restates the
root's own word-bound slot and must supply the cover phase's two arena
slots from the mass readings — could not reach it.

Nothing about the mathematics needs to be up there. `ptr_le_mass` and
`mass_le` are facts about `RamCover.CoverInv` / `CoverOut` and the
cover-degree double count; their whole dependency is
`Refine.MassMath` + `RamDriver`, both far below the driver's assembly.
So the two readings move down here, and `Refine.ArenaWidth` §5 and
`Refine.CoverWidth` §1 re-export them under their landed names — every
consumer, every `#print axioms` and every docstring reference in the
tree keeps resolving.

**What is here.**

* §1 — the block-tiling reading of `CoverInv` and the sharp pointer
  ceiling `ptr_le_mass : xp ≤ n * d`, with `d` the ordering's weak
  `2r`-reachability degree (the root theorem's own `hdeg` slot), and
  `block_scan_lt`, the emission scan's word clause off `WordBoundK`.
* §2 — the two arena slots of the cover phase at that reading:
  `RamDriver.PtrWords` (the emission scan's running pointer) and
  `RamDriver.MassWords` (the pointer the pass reports).

**What is not here.** The C0-side flip (`word_size_for_encoded`), the
controls and the `CoverImplementsK` obligation stay in
`Refine.ArenaWidth`: they are statements about the *word length* C0
admits, and they need the seam probe. The re-walked pass and its own
controls stay in `Refine.CoverWidth`.
-/

namespace Lax3Proofs.Refine.ArenaPointer

open Finset
open Lax12.ColoringNumbers (wreach)
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamCover
open Lax3Proofs.RamDriver (WordBoundK PtrWords MassWords)
open Lax3Proofs.Refine.MassMath (blockSize clusterAt coverFam)

variable {n : ℕ} {G : SimpleGraph (Fin n)} {A₀ ord Xoff Xmem asg M : ℕ → ℕ}
  {π : Equiv.Perm (Fin n)} {r c xp d : ℕ}

/-! ## 1. The arena pointer is almost-linear at every centre boundary

`RamCover.CoverInv.ptr_le` is `xp ≤ c * n` — the trivial `n²`, and the
reason `RamDriver.WordBound` carried `n * n`. The invariant already
carries everything a sharper ceiling needs: `block` and `block_inj` for
every block below the current centre, `mono` and `zero` for the offsets,
and `ptr` for the pointer itself. Reading `Refine.MassMath`'s double
count over that *prefix* gives `xp ≤ n * d` with `d` the ordering's weak
reachability degree — which is the root theorem's own `hdeg` slot. -/

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
case and is what the `n * n` in `RamDriver.WordBound` paid for; this is
the same fact at the sharp constant. -/
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
    (le_trans (le_of_eq (MassMath.sum_clusterAt_eq hord)) (sum_coverFam_le hk))

/-- **What the new slot buys the block scan.** `RamDriverOrder`'s
emission scan starts at the pointer and may add one slot per carrier
vertex, so the widest value it forms is `xp + n`; under `WordBoundK` at
`K = d` that is a word. This is the inequality the `n * n < B` reading
is replaced by. -/
theorem block_scan_lt {B ns cap mb : ℕ} (hord : OrdersBy n π ord)
    (hI : CoverInv G A₀ π ord r c xp Xoff Xmem asg M)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hB : WordBoundK B n d ns cap mb) : xp + n < B := by
  have := ptr_le_mass hord hI hk
  have := hB.1
  omega

/-! ## 2. The two arena slots of the cover phase, at the mass reading

`RamDriver.PtrWords` and `RamDriver.MassWords` are the two values the
cover pass forms out of the cluster arena — the emission scan's running
pointer and the pointer the pass reports. Each has a **carrier**
reading (`RamDriver.ptrWords_of_square`, `massWords_of_square`, off the
retired `WordBound.cover`) and a **mass** reading, below. The mass
readings are what `RamDriverRoot` stands on since W3, and they are what
makes the root's word bound satisfiable at C0's own word lengths.

The `mb` slot of `WordBoundK` plays no part in the pointer reading —
the cover pass forms no padded width — so `ptrWords_of_mass` is stated
at the arena clause alone. -/

/-- **The arena reading of the scan's ceiling**: the pointer ceiling
from the mass bound rather than from the carrier. -/
theorem ptrWords_of_mass {B ns : ℕ} (hord : OrdersBy n π ord)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hB : n * d + n + ns + 2 * r + 2 < B) :
    PtrWords B G A₀ π ord r := by
  intro c xp Xoff Xmem asg M hI _
  exact block_scan_lt (ns := ns) (cap := r) (mb := 0) hord hI hk ⟨hB, by omega⟩

/-- The same, entered at the driver's own slot rather than at its arena
clause: `WordBoundK` at the search's radius. -/
theorem ptrWords_of_wordBoundK {B ns mb : ℕ} (hord : OrdersBy n π ord)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hB : WordBoundK B n d ns r mb) : PtrWords B G A₀ π ord r :=
  ptrWords_of_mass (ns := ns) hord hk hB.1

/-- **The arena reading of the exit ceiling.** The pointer the pass
reports is the mass of the cover it emitted, and `MassMath.mass_le`
bounds that by `n * d` off the pass's own block injectivity. -/
theorem massWords_of_mass {B ns mb : ℕ} (hord : OrdersBy n π ord)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hB : WordBoundK B n d ns r mb) : MassWords B G A₀ π ord r := fun hout _ =>
  lt_of_le_of_lt
    (MassMath.mass_le hord hout (MassMath.blockInj_of_coverOut hout) hk)
    (by have := hB.arena; omega)

/-! ## 3. The axiom check -/

#print axioms ptr_le_mass
#print axioms block_scan_lt
#print axioms ptrWords_of_mass
#print axioms ptrWords_of_wordBoundK
#print axioms massWords_of_mass

end Lax3Proofs.Refine.ArenaPointer
