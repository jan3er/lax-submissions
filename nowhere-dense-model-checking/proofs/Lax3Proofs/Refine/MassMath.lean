import Lax3Proofs.CoverDegree
import Lax3Proofs.RamCover

/-!
**The mass of a level** — brief B6 of the ND-MC integration wave
(`plans/nowhere-dense-model-checking/integration-design.md` §5.5, §8).

The Σ-shaped cost interface charges a level the sum of its turns, each
at its own block's size, so the whole almost-linear headline rests on
one number: the **mass** `m` of the cover the cover phase emits, the
length of the cluster arena. This file bounds it.

# The chain

```
CoverOut.block            each block lists exactly its centre's cluster
  + block injectivity     each block lists it *without repetition*
    ⇒ blockSize c = |cluster c|            (`blockSize_eq_ncard`)
    ⇒ m = ∑_{c < n} |cluster c|            (`mass_eq_sum_ncard`)
  + OrdersBy              positions and centres are the same n things
    ⇒ m = ∑_{u : Fin n} |X u|              (`sum_clusterAt_eq`)
  + CoverDegree.sum_ncard_le_mul_of_subset (the cover's degree bound)
    ⇒ m ≤ |S| · d for any support S of the blocks    (`mass_le_of_support`)
```

`mass_le_succ` is the last line in the §5.5 shape
`mm ≤ Kmass · (arenaSize + 1)`, and `mass_le_of_alive` is it with the
support named by a mask array — `{v | Alv v ≠ 0}`, which is
`RamDriverCluster.markSet n Alv` unfolded, so the driver instantiates it
by `rfl`.

# The clause `CoverOut` does not carry (finding for B3/B4)

Block injectivity is **not** derivable from `RamCover.CoverInv` /
`CoverOut` as they stand. `CoverOut.block` fixes each block's *value
set*; nothing in the invariant forbids a block from listing one vertex
a hundred times, and the only length control it carries is
`CoverInv.ptr_le : xp ≤ c * n` — the trivial `n²`. The falsification
block below compiles that: a block of three slots all holding vertex
`0` satisfies every clause of the invariant that mentions the block and
has `blockSize = 3` against `|cluster| = 1`.

So injectivity is taken here as the named hypothesis `BlockInj`, and
the missing clause is reported rather than added (the pass's files are
another wave's). The tower-side twin is `CoverSynth.ReachedList`, whose
*second* conjunct is exactly this — `∀ k k' < max tl 1, reach[k]! =
reach[k']! → k = k'` — so the fact is true of the program and is
already checked on every worked run there; what is missing is the
clause's journey through `CoverInv.step` (one new hypothesis, on the
new block only) into `CoverInv`/`CoverOut`. §6 of the report names the
three lines.

# Carrier mass versus arena mass

`mass_le` bounds the mass by `n · d` — the *carrier*. That is the
honest ceiling for the pass as it stands, because `RamBfs.masked`
*isolates* the dead vertices instead of removing them, so a dead vertex
still lies in its own cluster and still gets emitted: at a nested
depth, mass `≥ n` no matter how small the arena. The recursion of §2.4
needs mass `≤ D · (arena + 1)`, so it needs the emission restricted to
the alive set — exactly the block-driven cover pass of R1.6/B4.
`mass_le_of_support` is stated against that hypothesis and nothing
else, so B4's block-driven pass discharges it the moment it exists.
-/

namespace Lax3Proofs.Refine.MassMath

open Finset
open Lax12.ColoringNumbers (wreach)
open Lax3.NeighborhoodCovers
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamCover

variable {n : ℕ} {G : SimpleGraph (Fin n)} {A₀ ord Xoff Xmem asg : ℕ → ℕ}
  {π : Equiv.Perm (Fin n)} {r m : ℕ}

/-! ### The size vocabulary -/

/-- **The size of cover block `c`**: the distance between two
consecutive offsets of the compressed-row arena. -/
def blockSize (Xoff : ℕ → ℕ) (c : ℕ) : ℕ := Xoff (c + 1) - Xoff c

/-- **The cluster of the centre at position `c`**, as a set of
vertices — what block `c` of the arena lists. -/
def clusterAt (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (ord : ℕ → ℕ) (r c : ℕ) : Set (Fin n) :=
  {z : Fin n | InCluster (masked G A₀) π r (ord c) (z : ℕ)}

/-- **The same family indexed by centre vertex** — the one
`RamCover.isNeighborhoodCover_of_out` produces and `CoverDegree`
counts. -/
def coverFam (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (r : ℕ)
    (u : Fin n) : Set (Fin n) :=
  {w : Fin n | u ∈ wreach (masked G A₀) π (2 * r) w}

/-- **The clause `CoverOut` is missing**: no block lists a vertex
twice. Hypothesis here, reported as a `CoverInv`/`CoverOut`
strengthening — see the header. -/
def BlockInj (n : ℕ) (Xoff Xmem : ℕ → ℕ) : Prop :=
  ∀ c < n, ∀ p q, Xoff c ≤ p → p < Xoff (c + 1) → Xoff c ≤ q → q < Xoff (c + 1) →
    Xmem p = Xmem q → p = q

/-! ### The arena's offsets -/

/-- The offsets are laid out in order all the way up. -/
theorem off_mono (h : CoverOut G A₀ π ord r m Xoff Xmem asg) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n) : Xoff i ≤ Xoff j := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact le_rfl
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact le_trans (ih (by omega) (by omega)) (h.mono j (by omega))
      · have : i = j + 1 := by omega
        subst this; exact le_rfl

/-- Every offset is inside the arena. -/
theorem off_le (h : CoverOut G A₀ π ord r m Xoff Xmem asg) {k : ℕ} (hk : k ≤ n) :
    Xoff k ≤ m := by
  have := off_mono h hk le_rfl
  rwa [h.last] at this

/-- **The blocks tile the arena**: their sizes sum to its length. -/
theorem sum_blockSize (h : CoverOut G A₀ π ord r m Xoff Xmem asg) :
    ∀ k ≤ n, ∑ c ∈ range k, blockSize Xoff c = Xoff k := by
  intro k hk
  induction k with
  | zero => simp [h.zero]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih (by omega), blockSize]
      have := h.mono k (by omega)
      omega

/-! ### Block injectivity is the mass equation -/

/-- Everything a block holds lies in the block's cluster, and — with no
injectivity needed — a block whose slots all land in a set `S` has its
whole cluster inside `S`. This is what turns "the pass emits only alive
vertices" into "the clusters live in the alive set". -/
theorem clusterAt_subset (h : CoverOut G A₀ π ord r m Xoff Xmem asg) {c : ℕ} (hc : c < n)
    {S : Set (Fin n)}
    (hS : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → ∀ hp : Xmem p < n, (⟨Xmem p, hp⟩ : Fin n) ∈ S) :
    clusterAt G A₀ π ord r c ⊆ S := by
  intro z hz
  obtain ⟨p, hp1, hp2, hp3⟩ := (h.block c hc (z : ℕ)).mpr hz
  have hpm : p < m := lt_of_lt_of_le hp2 (off_le h (by omega))
  have hlt : Xmem p < n := h.mem_lt p hpm
  have hz' : (⟨Xmem p, hlt⟩ : Fin n) = z := Fin.ext hp3
  rw [← hz']
  exact hS p hp1 hp2 hlt

/-- **A block's size is its cluster's size** — given that it lists the
cluster without repetition. The block clause makes the block's slots
*onto* the cluster; injectivity makes the map a bijection. -/
theorem blockSize_eq_ncard (h : CoverOut G A₀ π ord r m Xoff Xmem asg)
    (hinj : BlockInj n Xoff Xmem) {c : ℕ} (hc : c < n) :
    blockSize Xoff c = (clusterAt G A₀ π ord r c).ncard := by
  classical
  have hn : 0 < n := by omega
  have hlt : ∀ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), Xmem p < n := by
    intro p hp
    rw [Finset.mem_Ico] at hp
    exact h.mem_lt p (lt_of_lt_of_le hp.2 (off_le h (by omega)))
  set f : ℕ → Fin n := fun p => ⟨Xmem p % n, Nat.mod_lt _ hn⟩ with hf
  have hfval : ∀ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), ((f p : Fin n) : ℕ) = Xmem p :=
    fun p hp => Nat.mod_eq_of_lt (hlt p hp)
  have hinj' : Set.InjOn f ↑(Finset.Ico (Xoff c) (Xoff (c + 1))) := by
    intro p hp q hq hpq
    have hp' := Finset.mem_Ico.mp (Finset.mem_coe.mp hp)
    have hq' := Finset.mem_Ico.mp (Finset.mem_coe.mp hq)
    have hval : Xmem p = Xmem q := by
      rw [← hfval p (Finset.mem_coe.mp hp), ← hfval q (Finset.mem_coe.mp hq), hpq]
    exact hinj c hc p q hp'.1 hp'.2 hq'.1 hq'.2 hval
  have himg : clusterAt G A₀ π ord r c = f '' ↑(Finset.Ico (Xoff c) (Xoff (c + 1))) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp1, hp2, hp3⟩ := (h.block c hc (z : ℕ)).mpr hz
      have hmem : p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)) := Finset.mem_Ico.mpr ⟨hp1, hp2⟩
      exact ⟨p, Finset.mem_coe.mpr hmem, Fin.ext (by rw [hfval p hmem, hp3])⟩
    · rintro ⟨p, hp, rfl⟩
      have hmem := Finset.mem_coe.mp hp
      have hmem' := Finset.mem_Ico.mp hmem
      show InCluster (masked G A₀) π r (ord c) ((f p : Fin n) : ℕ)
      rw [hfval p hmem]
      exact (h.block c hc (Xmem p)).mp ⟨p, hmem'.1, hmem'.2, rfl⟩
  rw [himg, Set.InjOn.ncard_image hinj', Set.ncard_coe_finset, Nat.card_Ico, blockSize]

/-- **The mass equation** (B6/i): the arena's length is the total size
of the clusters. -/
theorem mass_eq_sum_ncard (h : CoverOut G A₀ π ord r m Xoff Xmem asg)
    (hinj : BlockInj n Xoff Xmem) :
    m = ∑ c ∈ range n, (clusterAt G A₀ π ord r c).ncard := by
  have h1 : ∑ c ∈ range n, blockSize Xoff c = m := by rw [sum_blockSize h n le_rfl, h.last]
  rw [← h1]
  exact Finset.sum_congr rfl fun c hc => blockSize_eq_ncard h hinj (mem_range.mp hc)

/-! ### Positions against centres -/

/-- The block at position `c` is the cluster of the vertex the ordering
puts there. -/
theorem clusterAt_eq_coverFam (hord : OrdersBy n π ord) {c : ℕ} (hc : c < n) :
    clusterAt G A₀ π ord r c = coverFam G A₀ π r (π.symm ⟨c, hc⟩) := by
  ext z
  have hordc : ord c = ((π.symm ⟨c, hc⟩ : Fin n) : ℕ) := hord.eq_symm hc
  show InCluster (masked G A₀) π r (ord c) (z : ℕ) ↔ _
  rw [hordc, inCluster_iff (π.symm ⟨c, hc⟩).isLt z.isLt]
  simp [coverFam]

/-- And every vertex is the centre of the block at its own position. -/
theorem coverFam_eq_clusterAt (hord : OrdersBy n π ord) (u : Fin n) :
    coverFam G A₀ π r u = clusterAt G A₀ π ord r ((π u : Fin n) : ℕ) := by
  rw [clusterAt_eq_coverFam (G := G) (A₀ := A₀) (r := r) hord (π u).isLt]
  congr 1
  simp

/-- **The two readings of the total mass agree**: summing the clusters
over the arena's positions is summing them over the carrier's
vertices. This is where `OrdersBy` is load-bearing — with a repeated
centre the two sums differ, which the falsification block compiles. -/
theorem sum_clusterAt_eq (hord : OrdersBy n π ord) :
    ∑ c ∈ range n, (clusterAt G A₀ π ord r c).ncard
      = ∑ u : Fin n, (coverFam G A₀ π r u).ncard := by
  classical
  calc ∑ c ∈ range n, (clusterAt G A₀ π ord r c).ncard
      = ∑ i : Fin n, (clusterAt G A₀ π ord r (i : ℕ)).ncard :=
        (Fin.sum_univ_eq_sum_range (fun c => (clusterAt G A₀ π ord r c).ncard) n).symm
    _ = ∑ i : Fin n, (coverFam G A₀ π r (π.symm i)).ncard := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [clusterAt_eq_coverFam (G := G) (A₀ := A₀) (r := r) hord i.isLt]
    _ = ∑ u : Fin n, (coverFam G A₀ π r u).ncard :=
        Equiv.sum_comp π.symm (fun u => (coverFam G A₀ π r u).ncard)

/-! ### The mass bound

`hmass` of §5.5, in the two forms the driver wants: against the
carrier, which is what the pass as it stands supports, and against a
support set of the blocks, which is what the recursion needs and what a
block-driven cover pass delivers. -/

/-- **The mass bound** (B6/ii). With the blocks inside `S` and the
ordering's weak-reachability degree at most `d`, the arena is at most
`|S| · d` long. -/
theorem mass_le_of_support (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) (hinj : BlockInj n Xoff Xmem)
    {S : Set (Fin n)} (hS : ∀ c < n, clusterAt G A₀ π ord r c ⊆ S)
    {d : ℕ} (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d) :
    m ≤ S.ncard * d := by
  classical
  have hsub : ∀ u : Fin n, coverFam G A₀ π r u ⊆ S := by
    intro u
    rw [coverFam_eq_clusterAt (G := G) (A₀ := A₀) (r := r) hord u]
    exact hS _ (π u).isLt
  have hdeg : ∀ w : Fin n, {u : Fin n | w ∈ coverFam G A₀ π r u}.ncard ≤ d := by
    intro w
    have : {u : Fin n | w ∈ coverFam G A₀ π r u} = wreach (masked G A₀) π (2 * r) w := by
      ext u; exact Iff.rfl
    rw [this]
    exact hk w
  calc m = ∑ c ∈ range n, (clusterAt G A₀ π ord r c).ncard := mass_eq_sum_ncard h hinj
    _ = ∑ u : Fin n, (coverFam G A₀ π r u).ncard := sum_clusterAt_eq hord
    _ ≤ S.ncard * d := CoverDegree.sum_ncard_le_mul_of_subset _ S d hsub hdeg

/-- The bound against the carrier: unconditional, and the best the pass
supports as it stands (dead vertices are isolated, not removed, so they
are emitted too). -/
theorem mass_le (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) (hinj : BlockInj n Xoff Xmem)
    {d : ℕ} (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d) :
    m ≤ n * d := by
  have huniv : (Set.univ : Set (Fin n)).ncard = n := by simp
  have := mass_le_of_support hord h hinj (S := Set.univ) (fun _ _ => Set.subset_univ _) hk
  rwa [huniv] at this

/-- **The §5.5 shape.** `mm ≤ Kmass · (arenaSize + 1)`: the level's
mass, read against the arena the level runs on, in the exact form the
Σ-shaped level condition of `CostRecurrence.exists_driverCostsSigma`
consumes. -/
theorem mass_le_succ (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) (hinj : BlockInj n Xoff Xmem)
    {S : Set (Fin n)} (hS : ∀ c < n, clusterAt G A₀ π ord r c ⊆ S)
    {d : ℕ} (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d) :
    m ≤ d * (S.ncard + 1) := by
  have h₁ := mass_le_of_support hord h hinj hS hk
  calc m ≤ S.ncard * d := h₁
    _ = d * S.ncard := Nat.mul_comm _ _
    _ ≤ d * (S.ncard + 1) := Nat.mul_le_mul_left _ (by omega)

/-- **The mass bound with the arena named by a mask**, which is how the
driver holds it: `{v | Alv v ≠ 0}` is `RamDriverCluster.markSet n Alv`
unfolded, so the consumer instantiates `S` by `rfl`. The hypothesis is
the block-driven emission of R1.6/B4 — the pass writes alive vertices
only. -/
theorem mass_le_of_alive (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) (hinj : BlockInj n Xoff Xmem)
    (Alv : ℕ → ℕ) (halive : ∀ p < m, Alv (Xmem p) ≠ 0)
    {d : ℕ} (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d) :
    m ≤ d * (({v : Fin n | Alv (v : ℕ) ≠ 0} : Set (Fin n)).ncard + 1) := by
  refine mass_le_succ hord h hinj (fun c hc => clusterAt_subset h hc ?_) hk
  intro p hp1 hp2 hlt
  exact halive p (lt_of_lt_of_le hp2 (off_le h (by omega)))

/-! ### Falsification

Every statement above was checked on data before it was proved: the
degenerate covers first — an empty block and a block that repeats a
vertex — then the telescoping on the star instance, then the
reindexing without an ordering. Two of the checks are refutations of
authored readings. -/

section Falsification

-- A three-slot block all of whose slots hold vertex `0`. Its value set
-- is `{0}`, so it satisfies `CoverOut.block` against the singleton
-- cluster, and every other clause of the invariant that mentions the
-- block (`mono`, `mem_lt`, `ptr_le`) as well.
private def badXoff : ℕ → ℕ := fun c => if c = 0 then 0 else 3
private def badXmem : ℕ → ℕ := fun _ => 0

#guard blockSize badXoff 0 = 3
#guard ((List.range 3).map badXmem).dedup.length = 1

-- **Refuted**: without injectivity a block's size is *not* its
-- cluster's size — `CoverOut` as it stands does not carry the mass
-- equation, and `BlockInj` is a genuine new hypothesis.
#guard ¬ (blockSize badXoff 0 ≤ ((List.range 3).map badXmem).dedup.length)

-- The edge case the other way: an empty block contributes nothing.
private def emptyXoff : ℕ → ℕ := fun _ => 7
#guard blockSize emptyXoff 3 = 0
#guard (∑ c ∈ range 5, blockSize emptyXoff c) = 0

-- The star instance — one cluster on `n - 1` vertices and `n - 1`
-- singletons — telescoped: eight positions, mass `14`, which is
-- `CostShapeProbe.starSizes` summed.
private def starXoff : ℕ → ℕ := fun c => if c = 0 then 0 else 7 + (c - 1)
#guard (∑ c ∈ range 8, blockSize starXoff c) = starXoff 8
#guard starXoff 8 = 14

-- The reindexing, on cluster sizes `2, 1, 1` and the order array
-- `[2, 0, 1]`: summing over positions and over vertices agree.
private def csize : ℕ → ℕ := fun u => if u = 0 then 2 else 1
private def sord : ℕ → ℕ := fun c => [2, 0, 1].getD c 0
#guard (∑ c ∈ range 3, csize (sord c)) = (∑ u ∈ range 3, csize u)

-- **Refuted**: with a repeated centre — an `ord` that is not an
-- ordering — they do not, so `sum_clusterAt_eq` cannot drop `OrdersBy`.
#guard ¬ ((∑ c ∈ range 3, csize ((fun _ => 0 : ℕ → ℕ) c)) = (∑ u ∈ range 3, csize u))

-- The mass bound itself, numerically: three vertices, degree `2`,
-- cluster sizes `2, 2, 1` — mass `5 ≤ 3 * 2`.
#guard (∑ u ∈ range 3, [2, 2, 1].getD u 0) = 5
#guard (∑ u ∈ range 3, [2, 2, 1].getD u 0) ≤ 3 * 2

-- and the §5.5 shape at the same data, against an arena of two alive
-- vertices: `5 ≤ 2 * (2 + 1)` — tight enough to be a real check.
#guard 5 ≤ 2 * (2 + 1)

end Falsification

end Lax3Proofs.Refine.MassMath
