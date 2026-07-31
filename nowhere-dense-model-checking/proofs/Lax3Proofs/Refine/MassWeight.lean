import Lax3Proofs.Refine.ArenaBlock
import Lax3Proofs.Refine.BlockLeaves
import Lax3Proofs.TgtCoupling

/-!
**The weighted mass mathematics** — ND-MC rebase G2, wave E5
(`plans/nowhere-dense-model-checking/g2-cost-design.md` §1, §2.6, §6-E5).

G2 replaces the carrier-blind size variable of the cost interface by ONE
size variable, the **arena weight**

    arenaWeight n H M = ∑_{v ∈ markSet n M} (1 + deg_H v)     (root: n + ns)
    blockWeight  … c  = ∑_{p ∈ block c}     (1 + deg_H (Xmem p))

and every phase budget is read at it (`G2CostProbe.orderCostA` &c.).
This file is the mathematics of that variable, and **nothing else**: no
program, no `Spec`, no cost function occurs below. It is the weighted
twin of the landed size mathematics —

| landed (size) | here (weight) |
|---|---|
| `RamDriver.arenaSize` | `arenaWeight` |
| `MassMath.blockSize` | `blockWeight` |
| `RamDriver.arenaSize_of_all_alive` | `arenaWeight_of_all_alive` |
| `ArenaBlock.ncard_clusterAt_le_blockSize` (the §5.3 descend clause) | `arenaWeight_le_blockWeight` |
| `MassMath.blockSize_eq_ncard` | `blockWeight_eq_wsum_clusterAt` |
| `MassAlive.aliveMass` / `aliveMass_le` | `aliveMassW` / `aliveMassW_le` |
| `ArenaBlock.mass_of_alive_compaction` | `mass_of_alive_compaction_weight` |

— and the landed proofs are threaded, not re-run: the descent's subset
step, `MassAlive`'s alive-homogeneity and `MassMath`'s block clauses all
enter as they stand.

# Why weights, and why the degree half is load-bearing

The recursion's coefficient is untouched by the change. The per-vertex
cover-degree bound `hdeg` that today gives `∑_c |X_c| ≤ D·(m+1)` gives
`∑_c blockWeight c ≤ D·(w+1)` by the same double count read with a
weight instead of a `1`: each vertex lies in at most `D` blocks, so its
`1 + deg v` is counted at most `D` times (`sum_wsum_le_mul_of_subset`,
the weighted `CoverDegree.sum_ncard_le_mul_of_subset`). What the weight
buys is that the *block-driven* engines — whose costs are sums over a
block's members AND over those members' arena slots (`BlockLeaves`'
`bexpK m d`, `d = degSum`) — are budgeted by one number:
`blockWeight = blockSize + degSum` exactly
(`blockWeight_eq_add_degSum`), which is why `blockDegSum_le_blockWeight`
closes B4c/N-2.

The degree half is not decoration, and §6 compiles the refutation: at a
star's centre block — one member, `D` slots — the landed leaf costs
exceed **every** budget read at the block's SIZE (`turn_size_refuted`),
while the same budget read at the block's WEIGHT clears
(`turn_weight_clears`). Sizes cannot bound the block-driven engines;
weights can.

# The two readings of a degree, and which one a consumer holds

`vdeg H v` is the mathematical degree (`{u | H.Adj v u}.ncard`) and
`csrW O v = 1 + Csr.rowLen O v` is the machine's — the compaction scan
adds `1 + (off[v+1] − off[v])` per alive member, one `aget` pair more
than the scan that today counts members. Under `RamElim.CsrSimple` the
two agree (`graphW_eq_csrW`), so `arenaWeight_of_all_alive_csr` reads
the root weight off the block structure as `n + ns` with no degree
argument at all. At a nested arena the weight may be read at the level's
own graph or at the parent's; `arenaWeight_masked_le` says the first is
never larger, so a budget granted at the parent's reading is granted at
either.

# Falsification

§6. Every authored inequality was checked on data before it was proved —
the star `K₁,₄` and a path, plus the campaign's degenerate covers (a
repeated block member, an empty block) — and three of the checks are
refutations: the size-only turn budget (above), the size-only mass
bound (`star_mass_size_refuted`: block weights do NOT sum below
`D·(arenaSize+1)`), and the descend clause without its subset
hypothesis.
-/

namespace Lax3Proofs.Refine.MassWeight

open Finset
open Lax12.ColoringNumbers (wreach)
open Lax13Proofs.Reasoning.Lib (Csr)
open Lax3.NeighborhoodCovers
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamCover
open Lax3Proofs.RamDriver (arenaSize Compacted)
open Lax3Proofs.Refine.MassMath (blockSize clusterAt coverFam BlockInj)

variable {n : ℕ} {G H : SimpleGraph (Fin n)} {A₀ ord Xoff Xmem asg O T : ℕ → ℕ}
  {π : Equiv.Perm (Fin n)} {r m : ℕ}

/-! ### §1 The weight vocabulary

A weight is a function `f : Fin n → ℕ` on the carrier; the two readings
the campaign uses are `graphW H = 1 + deg_H` and `csrW O = 1 + rowLen O`
(§2). Every lemma of §3–§5 is proved of a general `f` and then named at
`graphW`, so a consumer who holds the machine's reading rather than the
mathematical one instantiates the same statement. -/

/-- **The weight of a set**: the total weight of its members. Stated
with `Set.Finite.toFinset` rather than a `Fintype` instance so that no
decidability travels with it — every set this file weighs is a set of
`Fin n`, hence finite by `Set.toFinite`. -/
noncomputable def wsum (f : Fin n → ℕ) (A : Set (Fin n)) : ℕ :=
  ∑ v ∈ (Set.toFinite A).toFinset, f v

/-- A weight read at a vertex *number*, which is what a block's slots
hold; out of range it is zero, exactly as `RamElim.adeg` is. -/
noncomputable def natW (n : ℕ) (f : Fin n → ℕ) (a : ℕ) : ℕ :=
  if h : a < n then f ⟨a, h⟩ else 0

theorem natW_val (f : Fin n → ℕ) {a : ℕ} (h : a < n) : natW n f a = f ⟨a, h⟩ := dif_pos h

/-- **The weight of a block**, read off the arena the cover pass writes:
the total weight of the slots of block `c`. This is the machine's own
quantity — one pass over `Xmem[Xoff c .. Xoff (c+1))` — and §4 says it
is the weight of the block's cluster when the block lists it without
repetition. -/
noncomputable def slotWeight (n : ℕ) (f : Fin n → ℕ) (Xoff Xmem : ℕ → ℕ) (c : ℕ) : ℕ :=
  ∑ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), natW n f (Xmem p)

/-- The degree of a vertex, as a cardinal of a set — the reading that
needs no `DecidableRel` and so travels to `masked G M` for free. -/
noncomputable def vdeg (H : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  {u : Fin n | H.Adj v u}.ncard

/-- **The per-vertex weight of the G2 interface**: one for the vertex
and one for each of its arena slots. -/
noncomputable def graphW (H : SimpleGraph (Fin n)) (v : Fin n) : ℕ := 1 + vdeg H v

/-- The machine's reading of the same number: the vertex and its row. -/
noncomputable def csrW (n : ℕ) (O : ℕ → ℕ) (v : Fin n) : ℕ := 1 + Csr.rowLen O (v : ℕ)

theorem one_le_graphW (H : SimpleGraph (Fin n)) (v : Fin n) : 1 ≤ graphW H v := by
  simp [graphW]

theorem one_le_csrW (O : ℕ → ℕ) (v : Fin n) : 1 ≤ csrW n O v := by
  simp [csrW]

/-- **The weight of an arena** — the one size variable of the G2 phase
interface. The set is spelled out rather than written `markSet` for the
reason `RamDriver.arenaSize` spells it out: the driver's obligation
`Prop`s read it, and the two are the same term
(`RamDriverCluster.arenaSize_eq_markSet` is `rfl`). -/
noncomputable def arenaWeight (n : ℕ) (H : SimpleGraph (Fin n)) (M : ℕ → ℕ) : ℕ :=
  wsum (graphW H) {v : Fin n | M (v : ℕ) ≠ 0}

/-- **The weight of a cover block** — what a turn's budget is read at
(`G2CostProbe.turnCostSizeA` at `s := blockWeight …`). -/
noncomputable def blockWeight (n : ℕ) (H : SimpleGraph (Fin n)) (Xoff Xmem : ℕ → ℕ)
    (c : ℕ) : ℕ :=
  slotWeight n (graphW H) Xoff Xmem c

theorem arenaWeight_eq_markSet (n : ℕ) (H : SimpleGraph (Fin n)) (M : ℕ → ℕ) :
    arenaWeight n H M = wsum (graphW H) (RamDriverCluster.markSet n M) := rfl

/-! #### The weight of a set, calculated -/

theorem mem_wsumFinset {A : Set (Fin n)} {v : Fin n} :
    v ∈ (Set.toFinite A).toFinset ↔ v ∈ A := Set.Finite.mem_toFinset _

/-- The weight of a set as a sum over the whole carrier, which is the
form the double count of §4 runs in. -/
theorem wsum_eq_sum_indicator (f : Fin n → ℕ) (A : Set (Fin n)) :
    wsum f A = ∑ v : Fin n, Set.indicator A f v := by
  have h1 : ∀ v ∈ (Set.toFinite A).toFinset, f v = Set.indicator A f v := fun v hv =>
    (Set.indicator_of_mem (mem_wsumFinset.mp hv) f).symm
  rw [wsum, Finset.sum_congr rfl h1]
  exact Finset.sum_subset (Finset.subset_univ _) fun v _ hv =>
    Set.indicator_of_notMem (fun hA => hv (mem_wsumFinset.mpr hA)) f

theorem wsum_coe_finset (f : Fin n → ℕ) (s : Finset (Fin n)) :
    wsum f (↑s : Set (Fin n)) = ∑ v ∈ s, f v := by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext v
  rw [mem_wsumFinset]
  exact Finset.mem_coe

@[simp] theorem wsum_empty (f : Fin n → ℕ) : wsum f (∅ : Set (Fin n)) = 0 := by
  rw [wsum]
  exact Finset.sum_eq_zero fun v hv => absurd (mem_wsumFinset.mp hv) (Set.notMem_empty v)

/-- The image half of the descend clause: a sum over an image is never
larger than the sum over its source. (`Finset.sum_image` is the equality
under injectivity; this is the inequality without it, which is what a
block that may repeat a member needs.) -/
theorem sum_image_le_sum (s : Finset ℕ) (g : ℕ → Fin n) (f : Fin n → ℕ) :
    ∑ v ∈ s.image g, f v ≤ ∑ p ∈ s, f (g p) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (fun p hp => Finset.mem_image_of_mem g hp)
    (fun p => f (g p))]
  refine Finset.sum_le_sum fun v hv => ?_
  obtain ⟨p, hp, hgp⟩ := Finset.mem_image.mp hv
  calc f v = f (g p) := by rw [hgp]
    _ ≤ ∑ q ∈ s.filter (fun q => g q = v), f (g q) :=
        Finset.single_le_sum (f := fun q => f (g q)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_filter.mpr ⟨hp, hgp⟩)

theorem wsum_univ (f : Fin n → ℕ) : wsum f (Set.univ : Set (Fin n)) = ∑ v : Fin n, f v := by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext v
  simp

/-- **Weights are monotone in the set.** The descend clause of §3 is
this and one image count. -/
theorem wsum_mono (f : Fin n → ℕ) {A B : Set (Fin n)} (h : A ⊆ B) : wsum f A ≤ wsum f B := by
  rw [wsum, wsum]
  exact Finset.sum_le_sum_of_subset fun v hv =>
    mem_wsumFinset.mpr (h (mem_wsumFinset.mp hv))

/-- **Weights are monotone in the weight.** -/
theorem wsum_le_wsum_of_le {f g : Fin n → ℕ} (h : ∀ v, f v ≤ g v) (A : Set (Fin n)) :
    wsum f A ≤ wsum g A :=
  Finset.sum_le_sum fun v _ => h v

theorem wsum_congr {f g : Fin n → ℕ} (h : ∀ v, f v = g v) (A : Set (Fin n)) :
    wsum f A = wsum g A :=
  Finset.sum_congr rfl fun v _ => h v

/-- **A set is never heavier than the carrier.** -/
theorem wsum_le_total (f : Fin n → ℕ) (A : Set (Fin n)) : wsum f A ≤ ∑ v : Fin n, f v := by
  rw [← wsum_univ f]
  exact wsum_mono f (Set.subset_univ _)

/-- **Size under weight**: with every vertex weighing at least one, a
set's cardinality is under its weight. This is what turns the landed
`t ≤ m` antecedent (`ArenaBlock.cnum_le_arenaSize`) into the weighted
one the G2 level condition asks for. -/
theorem ncard_le_wsum {f : Fin n → ℕ} (hf : ∀ v, 1 ≤ f v) (A : Set (Fin n)) :
    A.ncard ≤ wsum f A := by
  calc A.ncard = (Set.toFinite A).toFinset.card := Set.ncard_eq_toFinset_card A (Set.toFinite A)
    _ = ∑ _v ∈ (Set.toFinite A).toFinset, 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ wsum f A := Finset.sum_le_sum fun v _ => hf v

/-- **The arena's size is under its weight** — the weighted `t ≤ w`
supply. -/
theorem arenaSize_le_arenaWeight (n : ℕ) (H : SimpleGraph (Fin n)) (M : ℕ → ℕ) :
    arenaSize n M ≤ arenaWeight n H M :=
  ncard_le_wsum (one_le_graphW H) _

/-! #### The weight of a block, calculated -/

theorem slotWeight_le_of_le {f g : Fin n → ℕ} (h : ∀ v, f v ≤ g v)
    (Xoff Xmem : ℕ → ℕ) (c : ℕ) :
    slotWeight n f Xoff Xmem c ≤ slotWeight n g Xoff Xmem c :=
  Finset.sum_le_sum fun p _ => by
    by_cases hp : Xmem p < n
    · rw [natW_val f hp, natW_val g hp]; exact h _
    · simp [natW, hp]

theorem slotWeight_congr {f g : Fin n → ℕ} (h : ∀ v, f v = g v) (Xoff Xmem : ℕ → ℕ) (c : ℕ) :
    slotWeight n f Xoff Xmem c = slotWeight n g Xoff Xmem c :=
  Finset.sum_congr rfl fun p _ => by
    by_cases hp : Xmem p < n
    · rw [natW_val f hp, natW_val g hp]; exact h _
    · simp [natW, hp]

/-- **A block's size is under its weight** — the slot-by-slot half of
`blockWeight_eq_add_degSum` (§5), and the fact a consumer holding a
size-shaped landed statement needs first. -/
theorem blockSize_le_slotWeight {f : Fin n → ℕ} (hf : ∀ v, 1 ≤ f v)
    (Xoff Xmem : ℕ → ℕ) {c : ℕ} (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    blockSize Xoff c ≤ slotWeight n f Xoff Xmem c := by
  calc blockSize Xoff c = (Finset.Ico (Xoff c) (Xoff (c + 1))).card := by
        rw [Nat.card_Ico, blockSize]
    _ = ∑ _p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ slotWeight n f Xoff Xmem c := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.mem_Ico] at hp
        rw [natW_val f (hmem p hp.1 hp.2)]
        exact hf _

theorem blockSize_le_blockWeight (H : SimpleGraph (Fin n)) (Xoff Xmem : ℕ → ℕ) {c : ℕ}
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    blockSize Xoff c ≤ blockWeight n H Xoff Xmem c :=
  blockSize_le_slotWeight (one_le_graphW H) Xoff Xmem hmem

/-- The member hypothesis of the two lemmas above, out of a cover
output: every slot of a block below the arena's length holds a vertex. -/
theorem mem_lt_of_coverOut (h : CoverOut G A₀ π ord r m Xoff Xmem asg) {c : ℕ} (hc : c < n)
    {p : ℕ} (_h1 : Xoff c ≤ p) (h2 : p < Xoff (c + 1)) : Xmem p < n :=
  h.mem_lt p (lt_of_lt_of_le h2 (MassMath.off_le h (by omega)))

/-! ### §2 The root reading: `arenaWeight = n + ns`

`RamDriver.arenaSize_of_all_alive` says the root's arena is the whole
carrier; its weighted twin says the root's *weight* is `n + ns`, the
number the probe's honesty controls (`G2CostProbe.decodeCost_le_weight`
and the rest) are all stated at. Two forms: at the graph's own degree
sum (`TgtCoupling.csrSlots`, the mathematical `ns`) and at the block
structure the driver is handed (`CsrGraph`, where the identity is a
telescoping and no degree occurs). -/

/-- The degree, at the graph's `SimpleGraph.degree` when that is
available — the bridge to `TgtCoupling.csrSlots`. -/
theorem vdeg_eq_degree (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (v : Fin n) :
    vdeg H v = H.degree v := by
  have hfin : (Set.toFinite {u : Fin n | H.Adj v u}).toFinset = H.neighborFinset v := by
    ext u
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, SimpleGraph.mem_neighborFinset]
  rw [vdeg, Set.ncard_eq_toFinset_card _ (Set.toFinite _), hfin, SimpleGraph.degree]

/-- **The root weight, mathematically**: at a mask that kills nothing
the arena weight is the carrier plus its degree sum. -/
theorem arenaWeight_of_all_alive [DecidableRel H.Adj] {M : ℕ → ℕ} (h : ∀ v < n, M v ≠ 0) :
    arenaWeight n H M = n + TgtCoupling.csrSlots H := by
  have hset : {v : Fin n | M (v : ℕ) ≠ 0} = (Set.univ : Set (Fin n)) :=
    Set.eq_univ_of_forall fun v => h (v : ℕ) v.isLt
  rw [arenaWeight, hset, wsum_univ]
  calc ∑ v : Fin n, graphW H v = ∑ v : Fin n, (1 + H.degree v) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [graphW, vdeg_eq_degree]
    _ = n + TgtCoupling.csrSlots H := by
        rw [Finset.sum_add_distrib, TgtCoupling.csrSlots_eq_sum_degree]
        simp

/-! #### The same off the block structure

`Csr.rowLen O v = O (v+1) - O v` is the row the machine reads, and the
rows tile the target array (`RamBfs.CsrGraph.sum_rowLen`). So the
machine's weight of the all-alive arena is `n + ns` by telescoping —
no degree, no `DecidableRel`, and it is this form the compaction scan
of the G2 prologue computes. -/

/-- **The root weight, mechanically**: `n + ns`. -/
theorem arenaWeight_of_all_alive_csr {ns : ℕ} {M : ℕ → ℕ} (hcsr : RamBfs.CsrGraph G ns O T)
    (h : ∀ v < n, M v ≠ 0) :
    wsum (csrW n O) {v : Fin n | M (v : ℕ) ≠ 0} = n + ns := by
  have hset : {v : Fin n | M (v : ℕ) ≠ 0} = (Set.univ : Set (Fin n)) :=
    Set.eq_univ_of_forall fun v => h (v : ℕ) v.isLt
  have hsum : ∑ i ∈ Finset.range n, Csr.rowLen O i = ns := by
    rw [hcsr.sum_rowLen le_rfl, hcsr.zero, hcsr.last]
    omega
  rw [hset, wsum_univ]
  calc ∑ v : Fin n, csrW n O v = ∑ v : Fin n, (1 + Csr.rowLen O (v : ℕ)) := rfl
    _ = n + ∑ i ∈ Finset.range n, Csr.rowLen O i := by
        rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range (fun i => Csr.rowLen O i) n]
        simp
    _ = n + ns := by rw [hsum]

/-- **The two readings agree** on a simple block structure: a row lists
each neighbour exactly once, so its length is the degree. The chain is
the landed one — `RamElim.card_liveSlots` at the all-alive mask, where
`masked G M` is `G` itself. -/
theorem rowLen_eq_vdeg {ns : ℕ} (hcsr : RamElim.CsrSimple G ns O T) {v : ℕ} (hv : v < n) :
    Csr.rowLen O v = vdeg G ⟨v, hv⟩ := by
  classical
  have hone : masked G (fun _ => 1) = G := by
    ext u w
    rw [RamBfs.masked_adj]
    simp
  have hlive : RamElim.liveSlots O T (fun _ => 1) v = Finset.Ico (O v) (O (v + 1)) := by
    ext p
    rw [RamElim.mem_liveSlots, Finset.mem_Ico]
    simp
  have hcard := RamElim.card_liveSlots (M := fun _ => 1) hcsr hv (by simp)
  rw [hlive, Nat.card_Ico, hone] at hcard
  have hfin : (Set.toFinite {u : Fin n | G.Adj ⟨v, hv⟩ u}).toFinset
      = Augmentation.nbrsIn G Finset.univ ⟨v, hv⟩ := by
    ext u
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Augmentation.mem_nbrsIn]
    exact ⟨fun h => ⟨Finset.mem_univ _, h.symm⟩, fun h => h.2.symm⟩
  rw [Csr.rowLen, hcard, vdeg, Set.ncard_eq_toFinset_card _ (Set.toFinite _), hfin]

/-- …so the machine's weight is the mathematical one. -/
theorem graphW_eq_csrW {ns : ℕ} (hcsr : RamElim.CsrSimple G ns O T) (v : Fin n) :
    graphW G v = csrW n O v := by
  rw [graphW, csrW, rowLen_eq_vdeg hcsr v.isLt]

/-- The arena weight, at either reading. -/
theorem arenaWeight_eq_csr {ns : ℕ} (hcsr : RamElim.CsrSimple G ns O T) (M : ℕ → ℕ) :
    arenaWeight n G M = wsum (csrW n O) {v : Fin n | M (v : ℕ) ≠ 0} :=
  wsum_congr (graphW_eq_csrW hcsr) _

/-- **The root weight of the driver's own arena**: `n + ns`, at the
graph reading, which is the instance
`RamDriverRoot.driverRoot_decides_sentence`'s root cost is restated at
(design doc §2.9, `Kl 0 (n + ns)`). -/
theorem arenaWeight_root {ns : ℕ} {M : ℕ → ℕ} (hcsr : RamElim.CsrSimple G ns O T)
    (h : ∀ v < n, M v ≠ 0) : arenaWeight n G M = n + ns := by
  rw [arenaWeight_eq_csr hcsr, arenaWeight_of_all_alive_csr hcsr.csr h]

/-! #### The arena's own graph against the level's

A nested level runs on `masked G M`, whose degrees are at most `G`'s, so
a weight granted at the parent's graph is granted at the child's. -/

theorem vdeg_masked_le (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (v : Fin n) :
    vdeg (masked G M) v ≤ vdeg G v := by
  refine Set.ncard_le_ncard (fun u hu => ?_) (Set.toFinite _)
  exact (RamBfs.masked_adj.mp hu).1

theorem graphW_masked_le (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (v : Fin n) :
    graphW (masked G M) v ≤ graphW G v := by
  simp only [graphW]
  exact Nat.add_le_add_left (vdeg_masked_le G M v) 1

/-- **The arena's own weight is under the carrier's reading of it.** -/
theorem arenaWeight_masked_le (n : ℕ) (G : SimpleGraph (Fin n)) (M M' : ℕ → ℕ) :
    arenaWeight n (masked G M) M' ≤ arenaWeight n G M' :=
  wsum_le_wsum_of_le (graphW_masked_le G M) _

/-! ### §3 The weighted descend clause (design doc §2.6)

`RamDriverCluster.DescendStep`'s §5.3 clause is
`arenaSize n Alv' ≤ blockSize Xoff cur`, proved by
`ArenaBlock.arenaSize_le_ncard` into `ncard_clusterAt_le_blockSize`.
Its weighted twin is proved the same way and is the statement E6 puts
in the clause's place: the sub-arena the turn hands down is inside the
turn's cluster, and a cluster's weight is under the weight of the block
that lists it — an image is never heavier than its source. **No
injectivity**: the `≤` direction needs none, exactly as the landed
size version needs none. -/

/-- **A cluster is no heavier than its block.** The weighted
`ArenaBlock.ncard_clusterAt_le_blockSize`. -/
theorem wsum_clusterAt_le_slotWeight (f : Fin n → ℕ)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) {c : ℕ} (hc : c < n) :
    wsum f (clusterAt G A₀ π ord r c) ≤ slotWeight n f Xoff Xmem c := by
  classical
  have hn : 0 < n := by omega
  have hlt : ∀ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), Xmem p < n := by
    intro p hp
    rw [Finset.mem_Ico] at hp
    exact mem_lt_of_coverOut h hc hp.1 hp.2
  set g : ℕ → Fin n := fun p => ⟨Xmem p % n, Nat.mod_lt _ hn⟩ with hg
  have hgval : ∀ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), ((g p : Fin n) : ℕ) = Xmem p :=
    fun p hp => Nat.mod_eq_of_lt (hlt p hp)
  have hsub : clusterAt G A₀ π ord r c ⊆ ↑((Finset.Ico (Xoff c) (Xoff (c + 1))).image g) := by
    intro z hz
    obtain ⟨p, hp1, hp2, hp3⟩ := (h.block c hc (z : ℕ)).mpr hz
    have hmem : p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)) := Finset.mem_Ico.mpr ⟨hp1, hp2⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p, hmem, Fin.ext (by rw [hgval p hmem, hp3])⟩)
  calc wsum f (clusterAt G A₀ π ord r c)
      ≤ wsum f ↑((Finset.Ico (Xoff c) (Xoff (c + 1))).image g) := wsum_mono f hsub
    _ = ∑ v ∈ (Finset.Ico (Xoff c) (Xoff (c + 1))).image g, f v := wsum_coe_finset _ _
    _ ≤ ∑ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), f (g p) := sum_image_le_sum _ _ _
    _ = slotWeight n f Xoff Xmem c := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [natW_val f (hlt p hp)]
        exact congrArg f (Fin.ext (hgval p hp))

/-- **The clause itself** (design doc §2.6, the weighted §5.3): the
arena the next depth is handed weighs no more than the block of the
centre the turn is processing. The hypothesis is the landed one —
`RamDriverDescend.descendStep` proves exactly `Alv'` marks only vertices
the cluster indicator marks — and the weight graph `H` is arbitrary, so
the clause holds at the level's graph, at the parent's, and at the
machine's `csrW` reading alike. -/
theorem wsum_le_slotWeight_of_sub (f : Fin n → ℕ)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) {c : ℕ} (hc : c < n) {Alv' : ℕ → ℕ}
    (hsub : ∀ v : Fin n, Alv' (v : ℕ) ≠ 0 → v ∈ clusterAt G A₀ π ord r c) :
    wsum f {v : Fin n | Alv' (v : ℕ) ≠ 0} ≤ slotWeight n f Xoff Xmem c :=
  le_trans (wsum_mono f fun v hv => hsub v hv) (wsum_clusterAt_le_slotWeight f h hc)

/-- The same at the named weight — the form E6 threads into
`DescendStep`. -/
theorem arenaWeight_le_blockWeight (H : SimpleGraph (Fin n))
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) {c : ℕ} (hc : c < n) {Alv' : ℕ → ℕ}
    (hsub : ∀ v : Fin n, Alv' (v : ℕ) ≠ 0 → v ∈ clusterAt G A₀ π ord r c) :
    arenaWeight n H Alv' ≤ blockWeight n H Xoff Xmem c :=
  wsum_le_slotWeight_of_sub (graphW H) h hc hsub

/-- And with the sub-arena's own graph on the left, which is the
reading the nested level's budget is granted at
(`arenaWeight_masked_le` composed). -/
theorem arenaWeight_masked_le_blockWeight (G : SimpleGraph (Fin n)) (M : ℕ → ℕ)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) {c : ℕ} (hc : c < n) {Alv' : ℕ → ℕ}
    (hsub : ∀ v : Fin n, Alv' (v : ℕ) ≠ 0 → v ∈ clusterAt G A₀ π ord r c) :
    arenaWeight n (masked G M) Alv' ≤ blockWeight n G Xoff Xmem c :=
  le_trans (arenaWeight_masked_le n G M Alv') (arenaWeight_le_blockWeight G h hc hsub)

/-! ### §4 The weighted mass

`MassAlive.aliveMass_le` bounds the total *size* of the live centres'
blocks by `d · (arenaSize + 1)`; its weighted twin bounds their total
*weight* by `d · (arenaWeight + 1)`, from the same hypotheses — the
cover pass's own postcondition, the block injectivity B3 landed, and
the cover-degree bound `hdeg`. Nothing new is asked of the program.

The engine is one double count, read with a weight instead of a `1`:
each vertex lies in at most `d` blocks, so its weight is counted at most
`d` times (`sum_wsum_le_mul_of_subset`, the weighted
`CoverDegree.sum_ncard_le_mul_of_subset`). -/

/-- **The weighted double count.** A family of sets inside `S`, no
vertex of which lies in more than `d` members, has total *weight* at
most `d · weight S`. At `f = 1` this is
`CoverDegree.sum_ncard_le_mul_of_subset`. -/
theorem sum_wsum_le_mul_of_subset (f : Fin n → ℕ) (X : Fin n → Set (Fin n)) (S : Set (Fin n))
    (d : ℕ) (hsub : ∀ u : Fin n, X u ⊆ S)
    (hfib : ∀ w : Fin n, {u : Fin n | w ∈ X u}.ncard ≤ d) :
    ∑ u : Fin n, wsum f (X u) ≤ d * wsum f S := by
  classical
  have hpoint : ∀ v : Fin n,
      ∑ u : Fin n, Set.indicator (X u) f v ≤ d * Set.indicator S f v := by
    intro v
    by_cases hv : v ∈ S
    · have hfib' : (Set.toFinite {u : Fin n | v ∈ X u}).toFinset.card ≤ d := by
        rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
        exact hfib v
      have hres : ∑ u : Fin n, Set.indicator (X u) f v
          = ∑ _u ∈ (Set.toFinite {u : Fin n | v ∈ X u}).toFinset, f v := by
        have h1 : ∑ u ∈ (Set.toFinite {u : Fin n | v ∈ X u}).toFinset,
              Set.indicator (X u) f v
            = ∑ u : Fin n, Set.indicator (X u) f v :=
          Finset.sum_subset (Finset.subset_univ _) fun u _ hu => by
            refine Set.indicator_of_notMem (fun hx => hu ?_) f
            exact mem_wsumFinset.mpr hx
        rw [← h1]
        refine Finset.sum_congr rfl fun u hu => ?_
        have hx : v ∈ X u := by
          have h2 := mem_wsumFinset.mp hu
          rwa [Set.mem_setOf_eq] at h2
        exact Set.indicator_of_mem hx f
      rw [hres, Finset.sum_const, smul_eq_mul, Set.indicator_of_mem hv f]
      exact Nat.mul_le_mul_right _ hfib'
    · have hzero : ∀ u : Fin n, Set.indicator (X u) f v = 0 := fun u =>
        Set.indicator_of_notMem (fun hx => hv (hsub u hx)) f
      rw [Finset.sum_congr rfl fun u _ => hzero u]
      simp
  calc ∑ u : Fin n, wsum f (X u) = ∑ u : Fin n, ∑ v : Fin n, Set.indicator (X u) f v :=
        Finset.sum_congr rfl fun u _ => wsum_eq_sum_indicator f (X u)
    _ = ∑ v : Fin n, ∑ u : Fin n, Set.indicator (X u) f v := Finset.sum_comm
    _ ≤ ∑ v : Fin n, d * Set.indicator S f v := Finset.sum_le_sum fun v _ => hpoint v
    _ = d * ∑ v : Fin n, Set.indicator S f v := by rw [Finset.mul_sum]
    _ = d * wsum f S := by rw [← wsum_eq_sum_indicator]

/-- **A block's weight is its cluster's weight** — the weighted
`MassMath.blockSize_eq_ncard`, and it needs the same clause: a block
that listed a vertex twice would weigh it twice. -/
theorem slotWeight_eq_wsum_clusterAt (f : Fin n → ℕ)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) (hinj : BlockInj n Xoff Xmem)
    {c : ℕ} (hc : c < n) :
    slotWeight n f Xoff Xmem c = wsum f (clusterAt G A₀ π ord r c) := by
  classical
  have hn : 0 < n := by omega
  have hlt : ∀ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), Xmem p < n := by
    intro p hp
    rw [Finset.mem_Ico] at hp
    exact mem_lt_of_coverOut h hc hp.1 hp.2
  set g : ℕ → Fin n := fun p => ⟨Xmem p % n, Nat.mod_lt _ hn⟩ with hg
  have hgval : ∀ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), ((g p : Fin n) : ℕ) = Xmem p :=
    fun p hp => Nat.mod_eq_of_lt (hlt p hp)
  have hginj : ∀ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)),
      ∀ q ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), g p = g q → p = q := by
    intro p hp q hq hpq
    have hp' := Finset.mem_Ico.mp hp
    have hq' := Finset.mem_Ico.mp hq
    have hval : Xmem p = Xmem q := by rw [← hgval p hp, ← hgval q hq, hpq]
    exact hinj c hc p q hp'.1 hp'.2 hq'.1 hq'.2 hval
  have himg : clusterAt G A₀ π ord r c
      = ↑((Finset.Ico (Xoff c) (Xoff (c + 1))).image g) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp1, hp2, hp3⟩ := (h.block c hc (z : ℕ)).mpr hz
      have hmem : p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)) := Finset.mem_Ico.mpr ⟨hp1, hp2⟩
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨p, hmem, Fin.ext (by rw [hgval p hmem, hp3])⟩)
    · intro hz
      obtain ⟨p, hmem, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
      have hmem' := Finset.mem_Ico.mp hmem
      show InCluster (masked G A₀) π r (ord c) ((g p : Fin n) : ℕ)
      rw [hgval p hmem]
      exact (h.block c hc (Xmem p)).mp ⟨p, hmem'.1, hmem'.2, rfl⟩
  rw [himg, wsum_coe_finset, Finset.sum_image hginj]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [natW_val f (hlt p hp)]
  exact congrArg f (Fin.ext (hgval p hp).symm)

/-- **The alive mass, weighted**: the total weight of the blocks of the
*live* centres — `MassAlive.aliveMass` with each member counted at its
weight. This is the quantity a level's turn loop spends under the G2
interface. -/
noncomputable def aliveMassW (n : ℕ) (f : Fin n → ℕ) (A₀ ord Xoff Xmem : ℕ → ℕ) : ℕ :=
  ∑ c ∈ range n, if A₀ (ord c) = 0 then 0 else slotWeight n f Xoff Xmem c

theorem aliveMassW_eq_sum_wsum (f : Fin n → ℕ) (h : CoverOut G A₀ π ord r m Xoff Xmem asg)
    (hinj : BlockInj n Xoff Xmem) :
    aliveMassW n f A₀ ord Xoff Xmem
      = ∑ c ∈ range n, wsum f
          (if A₀ (ord c) = 0 then (∅ : Set (Fin n)) else clusterAt G A₀ π ord r c) := by
  refine Finset.sum_congr rfl fun c hc => ?_
  by_cases hd : A₀ (ord c) = 0
  · rw [if_pos hd, if_pos hd, wsum_empty]
  · rw [if_neg hd, if_neg hd]
    exact slotWeight_eq_wsum_clusterAt f h hinj (mem_range.mp hc)

/-- Summing over the arena's positions is summing over the carrier's
vertices — `MassAlive.sum_famA_eq` at a weight. -/
theorem sum_famA_wsum_eq (f : Fin n → ℕ) (hord : OrdersBy n π ord) :
    ∑ c ∈ range n, wsum f
        (if A₀ (ord c) = 0 then (∅ : Set (Fin n)) else clusterAt G A₀ π ord r c)
      = ∑ u : Fin n, wsum f (MassAlive.famA G A₀ π r u) := by
  classical
  have hstep : ∀ i : Fin n,
      (if A₀ (ord (i : ℕ)) = 0 then (∅ : Set (Fin n)) else clusterAt G A₀ π ord r (i : ℕ))
        = MassAlive.famA G A₀ π r (π.symm i) := by
    intro i
    have hordi : ord (i : ℕ) = ((π.symm i : Fin n) : ℕ) := hord.eq_symm i.isLt
    rw [MassAlive.famA, hordi, MassMath.clusterAt_eq_coverFam (G := G) (A₀ := A₀) (r := r)
      hord i.isLt]
  calc ∑ c ∈ range n, wsum f
        (if A₀ (ord c) = 0 then (∅ : Set (Fin n)) else clusterAt G A₀ π ord r c)
      = ∑ i : Fin n, wsum f
        (if A₀ (ord (i : ℕ)) = 0 then (∅ : Set (Fin n))
          else clusterAt G A₀ π ord r (i : ℕ)) :=
        (Fin.sum_univ_eq_sum_range (fun c => wsum f
          (if A₀ (ord c) = 0 then (∅ : Set (Fin n)) else clusterAt G A₀ π ord r c)) n).symm
    _ = ∑ i : Fin n, wsum f (MassAlive.famA G A₀ π r (π.symm i)) :=
        Finset.sum_congr rfl fun i _ => by rw [hstep i]
    _ = ∑ u : Fin n, wsum f (MassAlive.famA G A₀ π r u) :=
        Equiv.sum_comp π.symm (fun u => wsum f (MassAlive.famA G A₀ π r u))

/-- **The weighted mass bound** — `MassAlive.aliveMass_le` at a weight.
Same hypotheses, same proof shape, `d · (weight + 1)` in place of
`d · (size + 1)`: the live centres' blocks weigh at most `d` times the
arena's weight. -/
theorem aliveMassW_le (f : Fin n → ℕ) (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) (hinj : BlockInj n Xoff Xmem)
    {d : ℕ} (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d) :
    aliveMassW n f A₀ ord Xoff Xmem
      ≤ d * (wsum f {v : Fin n | A₀ (v : ℕ) ≠ 0} + 1) := by
  classical
  have hsub : ∀ u : Fin n, MassAlive.famA G A₀ π r u ⊆ {v : Fin n | A₀ (v : ℕ) ≠ 0} := by
    intro u
    by_cases hd : A₀ (u : ℕ) = 0
    · rw [MassAlive.famA, if_pos hd]; exact Set.empty_subset _
    · rw [MassAlive.famA, if_neg hd]; exact MassAlive.coverFam_subset_alive hd
  have hfib : ∀ w : Fin n, {u : Fin n | w ∈ MassAlive.famA G A₀ π r u}.ncard ≤ d := by
    intro w
    refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (hk w)
    intro u hu
    by_cases hd : A₀ (u : ℕ) = 0
    · rw [Set.mem_setOf_eq, MassAlive.famA, if_pos hd] at hu
      exact absurd hu (Set.notMem_empty _)
    · rw [Set.mem_setOf_eq, MassAlive.famA, if_neg hd] at hu
      exact hu
  have hmain : aliveMassW n f A₀ ord Xoff Xmem ≤ d * wsum f {v : Fin n | A₀ (v : ℕ) ≠ 0} := by
    rw [aliveMassW_eq_sum_wsum f h hinj, sum_famA_wsum_eq (A₀ := A₀) (G := G) (r := r) f hord]
    exact sum_wsum_le_mul_of_subset f _ _ d hsub hfib
  exact le_trans hmain (Nat.mul_le_mul_left _ (by omega))

/-- The same at the named weight: `aliveMass ≤ D · (arenaWeight + 1)`,
the `hmass` shape of the G2 level condition
(`G2CostProbe.g2_exists`'s `∑ bs c ≤ D · (w + 1)` antecedent). -/
theorem aliveMassW_le_arenaWeight (H : SimpleGraph (Fin n)) (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) (hinj : BlockInj n Xoff Xmem)
    {d : ℕ} (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d) :
    aliveMassW n (graphW H) A₀ ord Xoff Xmem ≤ d * (arenaWeight n H A₀ + 1) :=
  aliveMassW_le (graphW H) hord h hinj hk

/-! #### The consumer's forms -/

/-- **Any set of live positions is under the bound** — the weighted
`MassAlive.sum_blockSize_le_aliveMass`. -/
theorem sum_slotWeight_le_aliveMassW (f : Fin n → ℕ) (S : Finset ℕ)
    (hS : ∀ c ∈ S, c < n ∧ A₀ (ord c) ≠ 0) :
    ∑ c ∈ S, slotWeight n f Xoff Xmem c ≤ aliveMassW n f A₀ ord Xoff Xmem := by
  classical
  have hsubset : S ⊆ range n := fun c hc => mem_range.mpr (hS c hc).1
  have hval : ∀ c ∈ S, slotWeight n f Xoff Xmem c
      = if A₀ (ord c) = 0 then 0 else slotWeight n f Xoff Xmem c :=
    fun c hc => (if_neg (hS c hc).2).symm
  rw [Finset.sum_congr rfl hval]
  exact Finset.sum_le_sum_of_subset hsubset

/-- **The compacted list, weighed** — the weighted
`MassAlive.sum_blockSize_cps_le_aliveMass`. -/
theorem sum_slotWeight_cps_le_aliveMassW (f : Fin n → ℕ) {cps : ℕ → ℕ} {cnum : ℕ}
    (hmono : ∀ k k' : ℕ, k < k' → k' < cnum → cps k < cps k')
    (hlt : ∀ k < cnum, cps k < n) (halv : ∀ k < cnum, A₀ (ord (cps k)) ≠ 0) :
    ∑ k ∈ range cnum, slotWeight n f Xoff Xmem (cps k)
      ≤ aliveMassW n f A₀ ord Xoff Xmem := by
  classical
  have hinj : Set.InjOn cps ↑(range cnum) := by
    intro k hk k' hk' he
    have hk₁ := mem_range.mp (Finset.mem_coe.mp hk)
    have hk₂ := mem_range.mp (Finset.mem_coe.mp hk')
    rcases Nat.lt_trichotomy k k' with hh | hh | hh
    · exact absurd he (by have := hmono k k' hh hk₂; omega)
    · exact hh
    · exact absurd he.symm (by have := hmono k' k hh hk₁; omega)
  rw [← Finset.sum_image (g := cps) (f := fun c => slotWeight n f Xoff Xmem c) hinj]
  refine sum_slotWeight_le_aliveMassW f _ fun c hc => ?_
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
  exact ⟨hlt k (mem_range.mp hk), halv k (mem_range.mp hk)⟩

/-- **The whole weighted cost supply of a level** — the weighted
`ArenaBlock.mass_of_alive_compaction`, which is exactly the pair
`RamDriverCluster.levelImplements` takes as its `hmass`, read at
weights: the turn count under the arena's weight (the `t ≤ w`
antecedent) and the turns' blocks weighing at most `d · (w + 1)`.

Its hypotheses are the landed ones and **nothing else**: the cover
pass's postcondition, the block injectivity of B3, the cover-degree
bound of B5, and `RamDriver.Compacted` — whose `alive` clause B8
landed. -/
theorem mass_of_alive_compaction_weight (H : SimpleGraph (Fin n)) {cps : ℕ → ℕ} {cnum d : ℕ}
    (hord : OrdersBy n π ord) (h : CoverOut G A₀ π ord r m Xoff Xmem asg)
    (hinj : BlockInj n Xoff Xmem)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hcomp : Compacted n cnum m A₀ ord Xoff cps) :
    cnum ≤ arenaWeight n H A₀ ∧
      (∑ k ∈ range cnum, blockWeight n H Xoff Xmem (cps k)) ≤ d * (arenaWeight n H A₀ + 1) :=
  ⟨le_trans (ArenaBlock.cnum_le_arenaSize hord hcomp.lt hcomp.mono hcomp.alive)
      (arenaSize_le_arenaWeight n H A₀),
    le_trans
      (sum_slotWeight_cps_le_aliveMassW (graphW H) hcomp.mono hcomp.lt hcomp.alive)
      (aliveMassW_le_arenaWeight H hord h hinj hk)⟩

/-! ### §5 The block's slot count (B4c/N-2)

`BlockLeaves.bexpK m d` charges the block-driven expansion at the
block's size **and** at `d = degSum`, the number of arena slots the
block's members own; B4c left `degSum ≤ ns` unproved and named it
`ArenaBlock`'s to extend. The weight settles it without a summation
argument of its own, because the weight *is* the two numbers added:

    blockWeight = blockSize + blockDegSum        (exactly)

so a turn budgeted at its block's weight has paid both currencies. The
`≤ ns` form is the landed `RamBfs.CsrGraph.sum_rowLen_le` at the block's
members, whose distinctness is `MassMath.BlockInj`. -/

/-- **The block's slot count**, mathematically: the total degree of its
members. -/
noncomputable def blockDegSum (n : ℕ) (H : SimpleGraph (Fin n)) (Xoff Xmem : ℕ → ℕ)
    (c : ℕ) : ℕ :=
  ∑ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), natW n (vdeg H) (Xmem p)

/-- The same off the block structure — the number `BlockLeaves.degSum`
computes. -/
def blockRowSum (O Xoff Xmem : ℕ → ℕ) (c : ℕ) : ℕ :=
  ∑ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)), Csr.rowLen O (Xmem p)

/-- **The bridge to the block-driven engines.** `BlockLeaves.degSum` is
`blockRowSum` at the list readings of the two arrays — definitionally,
so an engine export moves to the counting statements below by `rfl`. -/
theorem blockLeaves_degSum_eq (idx off : List ℕ) (a b : ℕ) :
    Refine.BlockLeaves.degSum idx off a b
      = ∑ q ∈ Finset.Ico a b, Csr.rowLen (fun i => off[i]!) (idx[q]!) := rfl

/-- **The weight is the two currencies added.** -/
theorem blockWeight_eq_add_degSum (H : SimpleGraph (Fin n)) (Xoff Xmem : ℕ → ℕ) {c : ℕ}
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    blockWeight n H Xoff Xmem c = blockSize Xoff c + blockDegSum n H Xoff Xmem c := by
  have hval : ∀ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)),
      natW n (graphW H) (Xmem p) = 1 + natW n (vdeg H) (Xmem p) := by
    intro p hp
    rw [Finset.mem_Ico] at hp
    rw [natW_val _ (hmem p hp.1 hp.2), natW_val _ (hmem p hp.1 hp.2), graphW]
  rw [blockWeight, slotWeight, Finset.sum_congr rfl hval, Finset.sum_add_distrib,
    blockDegSum, Finset.sum_const, smul_eq_mul, Nat.mul_one, Nat.card_Ico, blockSize]

/-- **B4c/N-2, the local half**: a turn's slot count is under its
block's weight, so a budget read at the weight pays `bexpK`'s second
currency. -/
theorem blockDegSum_le_blockWeight (H : SimpleGraph (Fin n)) (Xoff Xmem : ℕ → ℕ) {c : ℕ}
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    blockDegSum n H Xoff Xmem c ≤ blockWeight n H Xoff Xmem c := by
  rw [blockWeight_eq_add_degSum H Xoff Xmem hmem]
  omega

/-- The machine's reading of the same decomposition. -/
theorem slotWeight_csrW_eq (O Xoff Xmem : ℕ → ℕ) {c : ℕ}
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    slotWeight n (csrW n O) Xoff Xmem c = blockSize Xoff c + blockRowSum O Xoff Xmem c := by
  have hval : ∀ p ∈ Finset.Ico (Xoff c) (Xoff (c + 1)),
      natW n (csrW n O) (Xmem p) = 1 + Csr.rowLen O (Xmem p) := by
    intro p hp
    rw [Finset.mem_Ico] at hp
    rw [natW_val _ (hmem p hp.1 hp.2), csrW]
  rw [slotWeight, Finset.sum_congr rfl hval, Finset.sum_add_distrib, blockRowSum,
    Finset.sum_const, smul_eq_mul, Nat.mul_one, Nat.card_Ico, blockSize]

/-- **B4c/N-2, the global half**: a block's slot count is under the
target array's length. The members of a block are distinct
(`MassMath.BlockInj`) vertices, and the rows of distinct vertices tile
the array (`RamBfs.CsrGraph.sum_rowLen_le`). -/
theorem blockRowSum_le_ns {ns : ℕ} (hcsr : RamBfs.CsrGraph G ns O T)
    (hinj : BlockInj n Xoff Xmem) {c : ℕ} (hc : c < n)
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    blockRowSum O Xoff Xmem c ≤ ns := by
  classical
  have hginj : Set.InjOn Xmem ↑(Finset.Ico (Xoff c) (Xoff (c + 1))) := by
    intro p hp q hq hpq
    have hp' := Finset.mem_Ico.mp (Finset.mem_coe.mp hp)
    have hq' := Finset.mem_Ico.mp (Finset.mem_coe.mp hq)
    exact hinj c hc p q hp'.1 hp'.2 hq'.1 hq'.2 hpq
  rw [blockRowSum, ← Finset.sum_image (g := Xmem) (f := fun v => Csr.rowLen O v) hginj]
  refine hcsr.sum_rowLen_le fun v hv => ?_
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  have hp' := Finset.mem_Ico.mp hp
  exact hmem p hp'.1 hp'.2

/-- …and so is the block's degree sum, at the graph reading. -/
theorem blockDegSum_le_ns {ns : ℕ} (hcsrS : RamElim.CsrSimple G ns O T)
    (hinj : BlockInj n Xoff Xmem) {c : ℕ} (hc : c < n)
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    blockDegSum n G Xoff Xmem c ≤ ns := by
  refine le_trans (le_of_eq ?_) (blockRowSum_le_ns hcsrS.csr hinj hc hmem)
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_Ico] at hp
  rw [natW_val _ (hmem p hp.1 hp.2), rowLen_eq_vdeg hcsrS (hmem p hp.1 hp.2)]

/-! #### The plug against the probe's proposed forms

`G2CostProbe` states its budgets at two free variables: an arena weight
`w` and a block weight `s` (`orderCostA b R w`, `turnCostSizeA ct ksc s
Kin`), plus the turn-leaf honesty control `blockLeaves_le_weight s ds ≤
200 · (s + ds + 1)` at a block's members `s` and its slots `ds`. The
three lemmas below are the arithmetic that says this file's definitions
are those variables — stated here rather than against the probe so that
the record file stays terminal in the import graph.

* `w := arenaWeight n G M` — at the root, `n + ns` (`arenaWeight_root`),
  which is the reading `g2_root_close` and the honesty controls use, and
  at any nested mask it is under that (`arenaWeight_le_root`);
* `s := blockWeight n G Xoff Xmem c` — and the probe's two block
  variables add up to exactly it (`probe_turn_budget_eq`), so
  `200 · (s + ds + 1)` IS `ct · (blockWeight + 1)` at `ct = 200`, the
  slot `turnCostSizeA` reads. -/

/-- **No arena outweighs the root.** -/
theorem arenaWeight_le_root {ns : ℕ} (hcsr : RamElim.CsrSimple G ns O T)
    (M' : ℕ → ℕ) : arenaWeight n G M' ≤ n + ns := by
  have hroot : arenaWeight n G (fun _ => 1) = n + ns :=
    arenaWeight_root hcsr (fun _ _ => one_ne_zero)
  rw [← hroot, arenaWeight, arenaWeight]
  exact wsum_mono _ fun v _ => by simp

/-- **The probe's turn budget, at this file's variables**: the members
and the slots of a block are its weight, so the block-driven leaf
budget `200 · (s + ds + 1)` is the weight budget
`turnCostSizeA` reads at `ct = 200`. -/
theorem probe_turn_budget_eq (H : SimpleGraph (Fin n)) (Xoff Xmem : ℕ → ℕ) {c ct : ℕ}
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    ct * (blockSize Xoff c + blockDegSum n H Xoff Xmem c + 1)
      = ct * (blockWeight n H Xoff Xmem c + 1) := by
  rw [blockWeight_eq_add_degSum H Xoff Xmem hmem]

/-- The same at the machine's reading of the block. -/
theorem probe_turn_budget_eq_csr (O Xoff Xmem : ℕ → ℕ) {c ct : ℕ}
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n) :
    ct * (blockSize Xoff c + blockRowSum O Xoff Xmem c + 1)
      = ct * (slotWeight n (csrW n O) Xoff Xmem c + 1) := by
  rw [slotWeight_csrW_eq O Xoff Xmem hmem]

/-! ### §6 Falsification

Every inequality above was checked on data before it was proved. The
instances are the campaign's stock ones — the star `K₁,₄`, a path, and
the degenerate covers of `MassMath` (a block that repeats a member, an
empty block) — plus the **disjoint-star arena** on which the size
reading of the mass clause dies.

Three of the blocks below are refutations, and they are what says the
degree half of the weight is load-bearing rather than decorative:

* `turn_size_refuted` — **no** budget read at a block's SIZE bounds the
  landed block-driven leaf costs, at any coefficient;
* the `starCwt` guards — a cover whose blocks satisfy the landed size
  bound `∑ blockSize ≤ D·(size+1)` has block WEIGHTS above it, so the
  turn slot cannot be read at the arena's size;
* the repeated-member guards — `slotWeight_eq_wsum_clusterAt` cannot
  drop `BlockInj`, exactly as `MassMath.blockSize_eq_ncard` cannot. -/

section Falsification

/-! #### The arena of five disjoint `K₁,₄`s

Twenty-five vertices; every fifth one is a hub of degree four, the rest
are leaves of degree one. The radius-1 clusters are the closed
neighbourhoods, so every hub lies in five of them and every leaf in
two — a cover of degree `D = 5`. -/

/-- The degree of a vertex of the arena. -/
private def sDeg (v : ℕ) : ℕ := if v % 5 = 0 then 4 else 1

/-- Its weight, `1 + deg`. -/
private def sWt (v : ℕ) : ℕ := 1 + sDeg v

/-- The size of its cluster (the closed neighbourhood). -/
private def sCsize (v : ℕ) : ℕ := if v % 5 = 0 then 5 else 2

/-- And the weight of its cluster. -/
private def sCwt (v : ℕ) : ℕ := if v % 5 = 0 then 5 + 4 * 2 else 2 + 5

-- the arena's two numbers: twenty-five alive vertices, weight `65`
#guard (∑ v ∈ range 25, sWt v) = 65
#guard (∑ _v ∈ range 25, (1 : ℕ)) = 25

-- `arenaWeight_of_all_alive`, read on data: `w = n + ns` with
-- `ns = ∑ deg = 40` — and the same on the two stock instances, whose
-- weights agree because both have four edges
#guard (∑ v ∈ range 25, sWt v) = 25 + (∑ v ∈ range 25, sDeg v)
#guard (∑ v ∈ range 5, (1 + [4, 1, 1, 1, 1].getD v 0)) = 5 + 8      -- `K₁,₄`
#guard (∑ v ∈ range 5, (1 + [1, 2, 2, 2, 1].getD v 0)) = 5 + 8      -- the path `P₅`

-- the mass, both readings: the blocks' sizes and the blocks' weights
#guard (∑ v ∈ range 25, sCsize v) = 65
#guard (∑ v ∈ range 25, sCwt v) = 205

-- the landed SIZE bound holds at `D = 5` …
#guard (∑ v ∈ range 25, sCsize v) ≤ 5 * (25 + 1)

-- **Refuted**: the same bound read at the arena's SIZE does not carry
-- the blocks' weights, so a turn budget charged at the size cannot pay
-- the block-driven engines. This is the mass-clause half of the
-- design's "one size variable" decision.
#guard ¬ ((∑ v ∈ range 25, sCwt v) ≤ 5 * (25 + 1))

-- … while at the arena's WEIGHT it clears — `aliveMassW_le` on data.
#guard (∑ v ∈ range 25, sCwt v) ≤ 5 * ((∑ v ∈ range 25, sWt v) + 1)

-- the descend clause on data (`arenaWeight_le_blockWeight`): the hub's
-- sub-arena is inside the hub's block and weighs less …
#guard sWt 0 ≤ sCwt 0
#guard sCwt 0 = 13

-- **Refuted** without the subset hypothesis: an arena that is *not*
-- inside the turn's block is not bounded by it, so the clause cannot
-- drop `hsub`.
#guard ¬ ((∑ v ∈ range 25, sWt v) ≤ sCwt 1)

-- `blockWeight_eq_add_degSum` on the hub's block: five members owning
-- eight arena slots weigh thirteen.
#guard 5 + (4 + 4 * 1) = sCwt 0

-- **Refuted**: a block that lists vertex `0` three times weighs three
-- times its cluster, so `slotWeight_eq_wsum_clusterAt` cannot drop
-- `BlockInj` — the same finding `MassMath`'s falsification block
-- compiles for sizes.
#guard (∑ _p ∈ range 3, sWt 0) = 15
#guard ¬ ((∑ _p ∈ range 3, sWt 0) ≤ sWt 0)

-- an empty block weighs nothing, at either reading
#guard (∑ p ∈ Finset.Ico 7 7, sWt p) = 0
#guard blockSize (fun _ => 7) 3 = 0

/-! #### The negative control the design asks for: sizes cannot budget
the block-driven leaves

`G2CostProbe.blockLeaves_le_weight` fits the landed B4c exports —
`blockLoadK`, `bandK`, `bsubK`, `bexpK` — under `200 · (s + ds + 1)`,
the block's WEIGHT. Read at the block's SIZE alone the same costs fit
**no** coefficient: a star's centre block has one member and as many
arena slots as the centre has neighbours, and `bexpK`'s `30 · degSum`
grows with them while `ct · (size + 1)` does not. -/

/-- **The refutation, for every coefficient**: at a one-member block
owning `ct` slots the landed leaf costs exceed `ct · (size + 1)`. So
the turn slot of `G2CostProbe.turnCostSizeA` must be read at the block
weight; `blockSize` cannot serve. -/
theorem turn_size_refuted (ct : ℕ) :
    ¬ (BlockLeaves.blockLoadK 1 1 + BlockLeaves.bandK 1 + BlockLeaves.bsubK 1 +
        BlockLeaves.bexpK 1 ct ≤ ct * (1 + 1)) := by
  simp only [BlockLeaves.blockLoadK, BlockLeaves.bandK, BlockLeaves.bsubK,
    BlockLeaves.bexpK]
  omega

/-- **And the weight reading clears** at the probe's own coefficient —
`G2CostProbe.blockLeaves_le_weight` at `s = 1`, `ds` arbitrary, which is
the instance the refutation above is stated against. -/
theorem turn_weight_clears (ds : ℕ) :
    BlockLeaves.blockLoadK 1 1 + BlockLeaves.bandK 1 + BlockLeaves.bsubK 1 +
      BlockLeaves.bexpK 1 ds ≤ 200 * (1 + ds + 1) := by
  simp only [BlockLeaves.blockLoadK, BlockLeaves.bandK, BlockLeaves.bsubK,
    BlockLeaves.bexpK]
  omega

-- the two, at the star's centre with a hundred leaves: `3176` against
-- `400` (size) and `20400` (weight)
#guard BlockLeaves.blockLoadK 1 1 + BlockLeaves.bandK 1 + BlockLeaves.bsubK 1 +
  BlockLeaves.bexpK 1 100 = 3176
#guard ¬ (BlockLeaves.blockLoadK 1 1 + BlockLeaves.bandK 1 + BlockLeaves.bsubK 1 +
  BlockLeaves.bexpK 1 100 ≤ 200 * (1 + 1))
#guard BlockLeaves.blockLoadK 1 1 + BlockLeaves.bandK 1 + BlockLeaves.bsubK 1 +
  BlockLeaves.bexpK 1 100 ≤ 200 * (1 + 100 + 1)

end Falsification

/-! ### §7 Axioms -/

/-- info: 'Lax3Proofs.Refine.MassWeight.arenaWeight_root' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms arenaWeight_root

/-- info: 'Lax3Proofs.Refine.MassWeight.arenaWeight_le_blockWeight' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms arenaWeight_le_blockWeight

/-- info: 'Lax3Proofs.Refine.MassWeight.sum_wsum_le_mul_of_subset' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms sum_wsum_le_mul_of_subset

/-- info: 'Lax3Proofs.Refine.MassWeight.mass_of_alive_compaction_weight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mass_of_alive_compaction_weight

/-- info: 'Lax3Proofs.Refine.MassWeight.blockDegSum_le_ns' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms blockDegSum_le_ns

/-- info: 'Lax3Proofs.Refine.MassWeight.turn_size_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms turn_size_refuted

end Lax3Proofs.Refine.MassWeight
