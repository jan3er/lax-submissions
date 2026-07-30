import Lax3Proofs.RamDriver
import Lax3Proofs.Refine.MassAlive

/-!
**Arenas against blocks** — the two counting facts the Σ-shaped cost
interface needs (`plans/nowhere-dense-model-checking/integration-design.md`
§5, brief B2).

The Σ interface charges a level the *sum* of its turns, each read at its
own cover block's size. Two inequalities make that legal, and neither of
them is about the machine:

1. **A cluster is no bigger than its block** (`ncard_clusterAt_le_blockSize`).
   `RamCover.CoverOut.block` makes the block's slots *onto* the cluster,
   so the cluster is the image of an interval of `blockSize` positions.
   `Refine.MassMath.blockSize_eq_ncard` is the same statement with
   equality, and it needs `MassMath.BlockInj` — the clause `CoverOut`
   does not carry. The `≤` direction needs **no** injectivity: an image
   is never larger than its source. This is the direction the descent's
   §5.3 clause uses (`RamDriverDescend.descendStep`), so that clause
   costs nothing beyond what the cover pass already proves.

2. **The turns are at most the arena** (`cnum_le_arenaSize`). If the
   compacted list names *live* centres, then `k ↦ ord (cps k)` is an
   injection of the turns into the alive set, so `cnum ≤ arenaSize` —
   which is the `t ≤ m` antecedent
   `CostRecurrence.exists_driverCostsSigma` asks for, and which no
   counting against the arena's *length* can give (that number is at
   least `n` at every depth).

`mass_of_alive_compaction` puts the two together with wave B4's
`Refine.MassAlive.aliveMass_le` and delivers, in one term, exactly the
pair `RamDriverCluster.levelImplements` takes as its `hmass`.

# The one clause that is missing, and why it is not added here

Everything above is hypothetical on `halv : ∀ k < cnum, A₀ (ord (cps k)) ≠ 0`
— the compaction lists live centres. B3's `RamDriver.compactCom` filters
on *non-empty block* instead, and `MassAlive.block_nonempty` says every
block of a cover output is non-empty, so B3's list is the whole carrier
(`MassAlive.cnum_eq_of_nonempty`) and `halv` is not available. Adding
the aliveness test to `compactCom` is one nested `ite`; what it costs is
not the walk but the **induction**, and
`dead_vertex_has_no_alive_turn` below compiles the reason: a vertex lies
in its assigned centre's cluster, clusters are alive-homogeneous
(`MassAlive.inCluster_alive_iff`), so an alive-filtered list omits
exactly the *dead* vertices' positions — while
`RamDriverCluster.levelImplements`' partition step needs every carrier
vertex to have had a turn (`RamDriver.TableInv` quantifies over all of
them, and a turn's readback reads the depth-`(j+1)` table at cluster
vertices the batch has killed). A dead-vertex path in the level is a
semantic addition to the induction, so it is reported and not taken.

Everything here is a statement about counting, not about a program; all
of it was `#guard`-checked on degenerate covers before it was proved.
-/

namespace Lax3Proofs.Refine.ArenaBlock

open Finset
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.WalkDistance (mem_ball_self)
open Lax3Proofs.RamCover
open Lax3Proofs.RamDriver (arenaSize Compacted)
open Lax3Proofs.Refine.MassMath (blockSize clusterAt)

variable {n : ℕ} {G : SimpleGraph (Fin n)} {A₀ ord Xoff Xmem asg cps : ℕ → ℕ}
  {π : Equiv.Perm (Fin n)} {r m : ℕ}

/-! ### An arena, counted -/

/-- **An arena inside a set is no bigger than the set.** The form the
descent uses: its next-depth mask marks only vertices the cluster
indicator marks. -/
theorem arenaSize_le_ncard {M : ℕ → ℕ} {S : Set (Fin n)}
    (h : ∀ v : Fin n, M (v : ℕ) ≠ 0 → v ∈ S) : arenaSize n M ≤ S.ncard :=
  Set.ncard_le_ncard h S.toFinite

/-! ### A cluster against its block -/

/-- **A block lists at least its cluster**, so the cluster is no bigger
than the block. The map is `p ↦ Xmem p` read into the carrier; `CoverOut`
makes it onto the cluster, and an image is never larger than its
source — no injectivity anywhere. -/
theorem ncard_clusterAt_le_blockSize (h : CoverOut G A₀ π ord r m Xoff Xmem asg)
    {c : ℕ} (hc : c < n) :
    (clusterAt G A₀ π ord r c).ncard ≤ blockSize Xoff c := by
  classical
  have hn : 0 < n := by omega
  have hlt : ∀ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), Xmem p < n := by
    intro p hp
    rw [Finset.mem_Ico] at hp
    exact h.mem_lt p (lt_of_lt_of_le hp.2 (MassMath.off_le h (by omega)))
  set f : ℕ → Fin n := fun p => ⟨Xmem p % n, Nat.mod_lt _ hn⟩ with hf
  have hfval : ∀ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), ((f p : Fin n) : ℕ) = Xmem p :=
    fun p hp => Nat.mod_eq_of_lt (hlt p hp)
  have hsub : clusterAt G A₀ π ord r c ⊆ f '' ↑(Finset.Ico (Xoff c) (Xoff (c + 1))) := by
    intro z hz
    obtain ⟨p, hp1, hp2, hp3⟩ := (h.block c hc (z : ℕ)).mpr hz
    have hmem : p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)) := Finset.mem_Ico.mpr ⟨hp1, hp2⟩
    exact ⟨p, Finset.mem_coe.mpr hmem, Fin.ext (by rw [hfval p hmem, hp3])⟩
  calc (clusterAt G A₀ π ord r c).ncard
      ≤ (f '' ↑(Finset.Ico (Xoff c) (Xoff (c + 1)))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (↑(Finset.Ico (Xoff c) (Xoff (c + 1))) : Set ℕ).ncard :=
        Set.ncard_image_le (Set.toFinite _)
    _ = blockSize Xoff c := by
        rw [Set.ncard_coe_finset, Nat.card_Ico, blockSize]

/-! ### The turns, counted against the arena

The level condition of `CostRecurrence.exists_driverCostsSigma` reads
two numbers off a level: the number of turns `t` — which it needs below
the arena size `m` — and the total sub-arena size over the turns. The
first is here; the second is wave B4's `MassAlive.sum_blockSize_cps_le_aliveMass`
composed with `MassAlive.aliveMass_le`. -/

/-- **A compaction of live centres takes at most `arenaSize` turns.**
The turns' centres are distinct vertices (`cps` is injective by strict
monotonicity, `ord` is injective by `OrdersBy`) and every one of them is
alive, so the turn count is bounded by the alive set — which is the
`t ≤ m` antecedent of the Σ level condition.

This is the only route to that antecedent. Counting against the arena's
*length* cannot give it: `MassAlive.mass_eq_aliveMass_add_dead` says the
length is at least the number of dead centres, so at a nested depth it
exceeds the arena size. -/
theorem cnum_le_arenaSize {cnum : ℕ} (hord : OrdersBy n π ord)
    (hlt : ∀ k < cnum, cps k < n)
    (hmono : ∀ k k' : ℕ, k < k' → k' < cnum → cps k < cps k')
    (halv : ∀ k < cnum, A₀ (ord (cps k)) ≠ 0) :
    cnum ≤ arenaSize n A₀ := by
  classical
  rcases Nat.eq_zero_or_pos cnum with rfl | hcpos
  · exact Nat.zero_le _
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (hlt 0 hcpos)
  set f : ℕ → Fin n := fun k => ⟨ord (cps k) % n, Nat.mod_lt _ hn⟩ with hf
  have hfval : ∀ k < cnum, ((f k : Fin n) : ℕ) = ord (cps k) :=
    fun k hk => Nat.mod_eq_of_lt (hord.lt (hlt k hk))
  have hmaps : ∀ k ∈ range cnum, f k ∈ ({v : Fin n | A₀ (v : ℕ) ≠ 0} : Set (Fin n)).toFinset := by
    intro k hk
    have hkc := mem_range.mp hk
    simp only [Set.mem_toFinset, Set.mem_setOf_eq]
    rw [hfval k hkc]
    exact halv k hkc
  have hinj : ∀ k ∈ range cnum, ∀ k' ∈ range cnum, f k = f k' → k = k' := by
    intro k hk k' hk' he
    have hkc := mem_range.mp hk
    have hkc' := mem_range.mp hk'
    have hoe : ord (cps k) = ord (cps k') := by
      rw [← hfval k hkc, ← hfval k' hkc', he]
    have hpe : cps k = cps k' := by
      have h₁ := hord.eq_symm (hlt k hkc)
      have h₂ := hord.eq_symm (hlt k' hkc')
      have : ((π.symm ⟨cps k, hlt k hkc⟩ : Fin n) : ℕ)
          = ((π.symm ⟨cps k', hlt k' hkc'⟩ : Fin n) : ℕ) := by rw [← h₁, ← h₂, hoe]
      have hsym : (π.symm ⟨cps k, hlt k hkc⟩ : Fin n) = π.symm ⟨cps k', hlt k' hkc'⟩ :=
        Fin.ext this
      have := congrArg π hsym
      simpa using congrArg Fin.val this
    rcases Nat.lt_trichotomy k k' with h | h | h
    · exact absurd hpe (by have := hmono k k' h hkc'; omega)
    · exact h
    · exact absurd hpe.symm (by have := hmono k' k h hkc; omega)
  have hcard := Finset.card_le_card_of_injOn f hmaps
    (fun k hk k' hk' he => hinj k (Finset.mem_coe.mp hk) k' (Finset.mem_coe.mp hk') he)
  rw [Finset.card_range] at hcard
  have hcards : ({v : Fin n | A₀ (v : ℕ) ≠ 0} : Set (Fin n)).toFinset.card = arenaSize n A₀ := by
    rw [arenaSize, Set.ncard_eq_toFinset_card']
  omega

/-- **The level's whole cost supply, given the one missing clause.**
Exactly the pair `RamDriverCluster.levelImplements` takes as `hmass`: the
turn count under the arena size, and the turns' sub-arenas under
`d · (arenaSize + 1)`.

Its hypotheses are the cover pass's own postcondition
(`RamCover.CoverOut`, `OrdersBy`), the block injectivity of B6/B4
(`MassMath.BlockInj`), the cover-degree bound of B5
(`CoverDegree.exists_cover_degree`'s conclusion), and `halv` — the one
clause `RamDriver.compactCom` does not yet establish, see the header. -/
theorem mass_of_alive_compaction {cnum d : ℕ} (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) (hinj : MassMath.BlockInj n Xoff Xmem)
    (hk : ∀ v : Fin n, (Lax12.ColoringNumbers.wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hcomp : Compacted n cnum m Xoff cps) (halv : ∀ k < cnum, A₀ (ord (cps k)) ≠ 0) :
    cnum ≤ arenaSize n A₀ ∧
      (∑ k ∈ range cnum, blockSize Xoff (cps k)) ≤ d * (arenaSize n A₀ + 1) :=
  ⟨cnum_le_arenaSize hord hcomp.lt hcomp.mono halv,
    MassAlive.sum_blockSize_cps_le_mass_shape hord h hinj hk hcomp.mono hcomp.lt halv⟩

/-! ### The blocker, compiled -/

/-- **Why the aliveness filter is not a free program delta.** A vertex is
in the cluster of the centre it is assigned to, and clusters are
alive-homogeneous, so a *dead* vertex's assigned centre is dead — and an
alive-filtered compaction does not list it. `levelImplements`' partition
step asks the opposite: that every carrier vertex's assigned position is
listed. So the filter and the present induction cannot both stand; the
level needs a path for dead vertices first. -/
theorem dead_vertex_has_no_alive_turn (h : CoverOut G A₀ π ord r m Xoff Xmem asg)
    {v : ℕ} (hv : v < n) (hdead : A₀ v = 0) : A₀ (ord (asg v)) = 0 := by
  have hself : InCluster (masked G A₀) π r (ord (asg v)) v :=
    h.asg_cover v hv (mem_ball_self _ _ _)
  by_contra hc
  exact ((MassAlive.inCluster_alive_iff hself).mpr hc) hdead

/-! ### Falsification

Both statements were checked on data first, on the two degenerate covers
`Refine.MassMath` uses — a block that repeats a vertex, and an empty
block — plus the star instance the cost probe is built on. The second
`#guard` is a **refutation**: without the compaction's injectivity the
sum of the listed blocks overshoots the arena, so
`cnum_le_arenaSize` cannot drop `Compacted.mono`. -/

section Falsification

-- The star arena of `Refine.CostShapeProbe`: one block of seven and
-- seven singletons, laid out as offsets — total mass `14`.
private def starXoff : ℕ → ℕ := fun c => if c = 0 then 0 else 7 + (c - 1)

#guard (∑ c ∈ range 8, blockSize starXoff c) = 14

-- The compaction of a cover with three empty blocks: positions
-- `0, 2, 5` are the nonempty ones, and their sizes still fit.
private def gapXoff : ℕ → ℕ := fun c => [0, 3, 3, 5, 5, 5, 9].getD c 9
private def gapCps : ℕ → ℕ := fun k => [0, 2, 5].getD k 0

#guard (∑ c ∈ range 6, blockSize gapXoff c) = 9
#guard (∑ k ∈ range 3, blockSize gapXoff (gapCps k)) = 9
#guard (∑ k ∈ range 3, blockSize gapXoff (gapCps k)) ≤ 9

-- **Refuted**: a "compaction" that repeats a position double-charges
-- its block, and the sum leaves the arena — the strict monotonicity of
-- `Compacted` is load-bearing in `cnum_le_arenaSize`, not decoration.
private def badCps : ℕ → ℕ := fun _ => 5

#guard ¬ ((∑ k ∈ range 3, blockSize gapXoff (badCps k)) ≤ 9)

-- An empty block contributes nothing, and a cluster of one inside a
-- block of three is the `≤` the first theorem states — with equality
-- refuted, which is exactly why `BlockInj` is not assumed here.
#guard blockSize gapXoff 1 = 0
#guard 1 ≤ blockSize (fun c => if c = 0 then 0 else 3) 0
#guard ¬ (blockSize (fun c => if c = 0 then 0 else 3) 0 ≤ 1)

end Falsification

end Lax3Proofs.Refine.ArenaBlock
