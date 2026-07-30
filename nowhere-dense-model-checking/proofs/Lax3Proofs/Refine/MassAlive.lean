import Lax3Proofs.Refine.MassMath

/-!
**The alive mass of a level** — rebase B4 / R1.6, the mass half

`MassMath.mass_le_of_alive` (B6/ii) asks the cover pass for one clause:
*every cell of the cluster arena holds an alive vertex*,

    halive : ∀ p < m, Alv (Xmem p) ≠ 0

and from it derives the recursion's mass shape
`m ≤ Kmass · (arena + 1)`. This file reports, with a proof, that **that
clause is not a property a program can have** — it is refutable from
`CoverOut` alone as soon as one vertex of the carrier is dead — and
replaces it by the clause a block-driven pass does deliver.

# §0 Why the arena-wide clause is unsatisfiable

`RamBfs.masked` *isolates* the dead vertices rather than removing them,
so a dead vertex `v` is still a vertex of the arena, still occupies the
position `π v` of the ordering, and is still weakly `2r`-reachable from
itself by the nil walk. `RamCover.CoverOut.block` is an **iff**, so the
block of the centre at position `π v` is therefore obliged to list `v`:
`self_mem_wreach` is unconditional. `alive_carrier_of_alive_arena` is
that argument in six lines — `halive` forces *every* vertex of the
carrier alive — so at any nested depth, where the arena is a cluster and
the carrier is the whole graph, `mass_le_of_alive` has no instance.

The floor this leaves is exact and not an artifact of the proof:
`mass_eq_aliveMass_add_dead` says the arena's length is the alive mass
plus **one cell per dead centre**, because a dead centre's cluster is
its own singleton (`clusterAt_dead`). Emitting less would refute
`CoverOut.block`; the `n` in `m ≥ n` is the number of dead centres, and
no emission rule can remove it while the block clause is an iff.

# §1 What replaces it

The quantity the recursion actually spends is not the arena's length but
the mass **the driver descends into**, and the driver descends into
alive centres only: a dead centre's cluster is a single dead vertex, and
B3's compaction is what selects the centres a turn is spent on. So the
bound belongs on

    aliveMass A₀ ord Xoff n = ∑_{c < n, A₀ (ord c) ≠ 0} blockSize Xoff c

and `aliveMass_le` is `mass_le_of_alive`'s conclusion for it,

    aliveMass ≤ d · (|{v | A₀ v ≠ 0}| + 1)

from `CoverOut` and `BlockInj` and nothing else — **no program change,
no new clause on the pass**. The mathematics is `MassMath`'s own, run
against the family that is empty at dead centres; what makes it go
through is the one geometric fact the file proves first
(`alive_iff_of_wreach`): weak reachability inside a masked arena is
*alive-homogeneous*, because a masked walk out of a live vertex never
leaves the live set and a masked walk out of a dead one is nil.

`sum_blockSize_le_aliveMass` is the consumer's form: any set of alive
positions — B3's compacted list `cps`, in particular — has its blocks
summing below the bound.

# §1.1 A second reading of the same fact: the compaction never filters

`block_nonempty`: *no* block of a cover output is empty, since the centre
is in its own cluster. So B3's compaction predicate
`Xoff c < Xoff (c + 1)` is passed by every position, and
`cnum_eq_of_nonempty` reads `cnum = n` off `RamDriver.Compacted`'s own
three clauses. `cnum ≤ mm` is true and escapes nothing; the escape is the
predicate, not the counting.

# §2 What a consumer has to do differently

`compactCom`'s predicate. B3 compacts on *non-empty block*
(`Xoff c < Xoff (c+1)`), which every dead centre passes, so `cnum ≤ mm`
carries the dead floor into the turn count. Compacting on
`alv[ord c] ≠ 0` instead selects exactly the positions this file bounds
(`aliveMass`), and `sum_blockSize_le_aliveMass` is then the level
condition's supply. That is one predicate in one program (`RamDriver.compactCom`)
and one clause in `CompactInv`; it is reported to B2 rather than taken
here, because the invariant is the Σ-threading wave's.

# §3 Falsification

The refutation is a *theorem* (`alive_carrier_of_alive_arena`), which is
stronger than a check: it says the hypothesis implies the carrier is
alive, so any instance at a nested depth is vacuous. The `#guard` block
at the end pins the gap numerically on a star-shaped arena — one alive
centre among eight positions, `aliveMass = 1` against `mass = 8` — and
pins the two edge readings (an all-alive arena, where the two agree, and
the empty-block case).
-/

namespace Lax3Proofs.Refine.MassAlive

open Finset
open Lax12.ColoringNumbers (wreach)
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamCover
open Lax3Proofs.Refine.MassMath

variable {n : ℕ} {G : SimpleGraph (Fin n)} {A₀ ord Xoff Xmem asg : ℕ → ℕ}
  {π : Equiv.Perm (Fin n)} {r m : ℕ}

/-! ### §0 The arena-wide alive clause is refutable

`MassMath.mass_le_of_alive`'s hypothesis, run backwards. -/

/-- **The refutation.** If every cell of the cluster arena holds an alive
vertex, then every vertex of the *carrier* is alive: a dead vertex is
weakly `2r`-reachable from itself, so `CoverOut.block` — an iff — puts it
in the block of its own position, and that block is inside the arena.

So `MassMath.mass_le_of_alive` is instantiable only when the mask kills
nothing, which is exactly the case its conclusion is not needed in. -/
theorem alive_carrier_of_alive_arena (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg)
    (halive : ∀ p < m, A₀ (Xmem p) ≠ 0) : ∀ v : Fin n, A₀ (v : ℕ) ≠ 0 := by
  intro v
  have hcn : ((π v : Fin n) : ℕ) < n := (π v).isLt
  have hordc : ord ((π v : Fin n) : ℕ) = (v : ℕ) := hord v
  have hin : InCluster (masked G A₀) π r (ord ((π v : Fin n) : ℕ)) (v : ℕ) := by
    rw [hordc]
    exact ⟨v.isLt, v.isLt, by simpa using self_mem_wreach (masked G A₀) π (2 * r) v⟩
  obtain ⟨p, -, hp2, hp3⟩ := (h.block _ hcn (v : ℕ)).mpr hin
  have hpm : p < m := lt_of_lt_of_le hp2 (off_le h (by omega))
  have := halive p hpm
  rwa [hp3] at this

/-! ### §1 Weak reachability in a masked arena is alive-homogeneous -/

/-- **The isolation lemma.** A masked walk out of a live vertex stays
live (`RamCover.support_notMem_of_walk`, both ways round), so the two
ends of a weak-reachability witness are alive together or dead
together. -/
theorem alive_iff_of_wreach {ρ : ℕ} {a w : Fin n}
    (h : a ∈ wreach (masked G A₀) π ρ w) : A₀ (w : ℕ) ≠ 0 ↔ A₀ (a : ℕ) ≠ 0 := by
  obtain ⟨p, -, -⟩ := h
  constructor
  · intro hw
    exact support_notMem_of_walk (S := {u : Fin n | A₀ (u : ℕ) = 0}) p hw a p.end_mem_support
  · intro ha
    exact support_notMem_of_walk (S := {u : Fin n | A₀ (u : ℕ) = 0}) p.reverse ha w (by simp)

/-- The same, in the pass's own vocabulary. -/
theorem inCluster_alive_iff {a w : ℕ} (h : InCluster (masked G A₀) π r a w) :
    A₀ w ≠ 0 ↔ A₀ a ≠ 0 := by
  obtain ⟨ha, hw, hmem⟩ := h
  exact alive_iff_of_wreach (a := ⟨a, ha⟩) (w := ⟨w, hw⟩) hmem

/-- **A live centre's cluster is live.** This is what makes the alive
mass a bound *against the alive set* and not against the carrier. -/
theorem clusterAt_subset_alive {c : ℕ} (halv : A₀ (ord c) ≠ 0) :
    clusterAt G A₀ π ord r c ⊆ {v : Fin n | A₀ (v : ℕ) ≠ 0} :=
  fun _ hz => (inCluster_alive_iff hz).mpr halv

/-- …and the same for the family indexed by centre vertex. -/
theorem coverFam_subset_alive {u : Fin n} (halv : A₀ (u : ℕ) ≠ 0) :
    coverFam G A₀ π r u ⊆ {v : Fin n | A₀ (v : ℕ) ≠ 0} :=
  fun _ hw => (alive_iff_of_wreach hw).mpr halv

/-- **A dead centre's cluster is its own singleton.** A masked walk that
starts at a dead vertex cannot take a step — its first edge would ask
that vertex to be alive — so the only vertex the centre is weakly
reachable from is itself. This is the exact size of the floor §0
refutes. -/
theorem eq_of_walk_dead {u v : Fin n} (p : (masked G A₀).Walk u v)
    (hu : A₀ (u : ℕ) = 0) : u = v := by
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd (RamBfs.masked_adj.mp hadj).2.1 (by simpa using hu)

theorem clusterAt_dead {c : ℕ} (hc : c < n) (hord : OrdersBy n π ord)
    (hdead : A₀ (ord c) = 0) :
    clusterAt G A₀ π ord r c = {(⟨ord c, hord.lt hc⟩ : Fin n)} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, fun z hz => ?_⟩
  · show InCluster (masked G A₀) π r (ord c) (ord c)
    exact ⟨hord.lt hc, hord.lt hc, self_mem_wreach _ _ _ _⟩
  · have hzd : A₀ (z : ℕ) = 0 := by
      by_contra hne
      exact ((inCluster_alive_iff hz).mp hne) hdead
    obtain ⟨ha, hw, hmem⟩ := hz
    obtain ⟨p, -, -⟩ := hmem
    exact eq_of_walk_dead (u := (⟨(z : ℕ), hw⟩ : Fin n)) p hzd

/-! ### §2 The alive mass -/

/-- **The family that is empty at dead centres** — the cover family with
the dead centres' singletons dropped. -/
def famA (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (r : ℕ)
    (u : Fin n) : Set (Fin n) :=
  if A₀ (u : ℕ) = 0 then ∅ else coverFam G A₀ π r u

/-- **The alive mass**: the total size of the blocks of the *live*
centres. This is the quantity the driver's turn loop spends, since a
dead centre's block is a dead singleton nobody descends into. -/
def aliveMass (A₀ ord Xoff : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ c ∈ range n, if A₀ (ord c) = 0 then 0 else blockSize Xoff c

theorem aliveMass_le_mass (h : CoverOut G A₀ π ord r m Xoff Xmem asg) :
    aliveMass A₀ ord Xoff n ≤ m := by
  have h₁ : ∑ c ∈ range n, blockSize Xoff c = m := by rw [sum_blockSize h n le_rfl, h.last]
  rw [← h₁]
  exact Finset.sum_le_sum fun c _ => by
    by_cases hd : A₀ (ord c) = 0
    · rw [if_pos hd]; exact Nat.zero_le _
    · rw [if_neg hd]

/-- The alive mass, as a sum of cluster sizes. -/
theorem aliveMass_eq_sum_ncard (h : CoverOut G A₀ π ord r m Xoff Xmem asg)
    (hinj : BlockInj n Xoff Xmem) :
    aliveMass A₀ ord Xoff n
      = ∑ c ∈ range n,
          (if A₀ (ord c) = 0 then (∅ : Set (Fin n)) else clusterAt G A₀ π ord r c).ncard := by
  refine Finset.sum_congr rfl fun c hc => ?_
  by_cases hd : A₀ (ord c) = 0
  · rw [if_pos hd, if_pos hd, Set.ncard_empty]
  · rw [if_neg hd, if_neg hd]
    exact blockSize_eq_ncard h hinj (mem_range.mp hc)

/-- Summing over the arena's positions is summing over the carrier's
vertices, with the dead centres dropped on both sides. -/
theorem sum_famA_eq (hord : OrdersBy n π ord) :
    ∑ c ∈ range n,
        (if A₀ (ord c) = 0 then (∅ : Set (Fin n)) else clusterAt G A₀ π ord r c).ncard
      = ∑ u : Fin n, (famA G A₀ π r u).ncard := by
  classical
  have hstep : ∀ i : Fin n,
      (if A₀ (ord (i : ℕ)) = 0 then (∅ : Set (Fin n)) else clusterAt G A₀ π ord r (i : ℕ))
        = famA G A₀ π r (π.symm i) := by
    intro i
    have hordi : ord (i : ℕ) = ((π.symm i : Fin n) : ℕ) := hord.eq_symm i.isLt
    rw [famA, hordi, clusterAt_eq_coverFam (G := G) (A₀ := A₀) (r := r) hord i.isLt]
  calc ∑ c ∈ range n,
        (if A₀ (ord c) = 0 then (∅ : Set (Fin n)) else clusterAt G A₀ π ord r c).ncard
      = ∑ i : Fin n,
        (if A₀ (ord (i : ℕ)) = 0 then (∅ : Set (Fin n))
          else clusterAt G A₀ π ord r (i : ℕ)).ncard :=
        (Fin.sum_univ_eq_sum_range
          (fun c => (if A₀ (ord c) = 0 then (∅ : Set (Fin n))
            else clusterAt G A₀ π ord r c).ncard) n).symm
    _ = ∑ i : Fin n, (famA G A₀ π r (π.symm i)).ncard :=
        Finset.sum_congr rfl fun i _ => by rw [hstep i]
    _ = ∑ u : Fin n, (famA G A₀ π r u).ncard :=
        Equiv.sum_comp π.symm (fun u => (famA G A₀ π r u).ncard)

/-- **The mass bound R1.6 delivers** — `MassMath.mass_le_of_alive`'s
conclusion, for the quantity that can carry it. No hypothesis on the
program beyond what `RamCover.cover_spec` already proves: `CoverOut` and
the block injectivity B3 landed.

`S` is the arena — `{v | A₀ v ≠ 0}` is `RamDriverCluster.markSet n A₀`
unfolded, so the driver instantiates it by `rfl`, exactly as B6
designed. -/
theorem aliveMass_le (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) (hinj : BlockInj n Xoff Xmem)
    {d : ℕ} (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d) :
    aliveMass A₀ ord Xoff n
      ≤ d * (({v : Fin n | A₀ (v : ℕ) ≠ 0} : Set (Fin n)).ncard + 1) := by
  classical
  have hsub : ∀ u : Fin n, famA G A₀ π r u ⊆ {v : Fin n | A₀ (v : ℕ) ≠ 0} := by
    intro u
    by_cases hd : A₀ (u : ℕ) = 0
    · rw [famA, if_pos hd]; exact Set.empty_subset _
    · rw [famA, if_neg hd]; exact coverFam_subset_alive hd
  have hdeg : ∀ w : Fin n, {u : Fin n | w ∈ famA G A₀ π r u}.ncard ≤ d := by
    intro w
    refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (hk w)
    intro u hu
    by_cases hd : A₀ (u : ℕ) = 0
    · rw [Set.mem_setOf_eq, famA, if_pos hd] at hu
      exact absurd hu (Set.notMem_empty _)
    · rw [Set.mem_setOf_eq, famA, if_neg hd] at hu
      exact hu
  have hmain : aliveMass A₀ ord Xoff n
      ≤ ({v : Fin n | A₀ (v : ℕ) ≠ 0} : Set (Fin n)).ncard * d := by
    rw [aliveMass_eq_sum_ncard h hinj, sum_famA_eq (A₀ := A₀) (G := G) (r := r) hord]
    exact CoverDegree.sum_ncard_le_mul_of_subset _ _ d hsub hdeg
  calc aliveMass A₀ ord Xoff n
      ≤ ({v : Fin n | A₀ (v : ℕ) ≠ 0} : Set (Fin n)).ncard * d := hmain
    _ = d * ({v : Fin n | A₀ (v : ℕ) ≠ 0} : Set (Fin n)).ncard := Nat.mul_comm _ _
    _ ≤ d * (({v : Fin n | A₀ (v : ℕ) ≠ 0} : Set (Fin n)).ncard + 1) :=
        Nat.mul_le_mul_left _ (by omega)

/-! ### §3 The consumer's form -/

/-- **Any set of live positions is under the bound.** B3's compacted
position list, filtered on aliveness (§2 of the header), instantiates
this directly: the level condition of `CostRecurrence` asks for the sum
of the sub-arena sizes over the turns, and the turns are the listed
positions. -/
theorem sum_blockSize_le_aliveMass (S : Finset ℕ)
    (hS : ∀ c ∈ S, c < n ∧ A₀ (ord c) ≠ 0) :
    ∑ c ∈ S, blockSize Xoff c ≤ aliveMass A₀ ord Xoff n := by
  classical
  have hsubset : S ⊆ range n := fun c hc => mem_range.mpr (hS c hc).1
  have hval : ∀ c ∈ S, blockSize Xoff c
      = if A₀ (ord c) = 0 then 0 else blockSize Xoff c :=
    fun c hc => (if_neg (hS c hc).2).symm
  rw [Finset.sum_congr rfl hval]
  exact Finset.sum_le_sum_of_subset hsubset

/-- **The compacted list, summed** — `sum_blockSize_le_aliveMass` at
B3's own vocabulary. `CompactInv` carries the strict monotonicity and the
range clause verbatim; the aliveness clause is the one predicate change
§2 of the header asks `compactCom` for. -/
theorem sum_blockSize_cps_le_aliveMass {cps : ℕ → ℕ} {cnum : ℕ}
    (hmono : ∀ k k' : ℕ, k < k' → k' < cnum → cps k < cps k')
    (hlt : ∀ k < cnum, cps k < n) (halv : ∀ k < cnum, A₀ (ord (cps k)) ≠ 0) :
    ∑ k ∈ range cnum, blockSize Xoff (cps k) ≤ aliveMass A₀ ord Xoff n := by
  classical
  have hinj : Set.InjOn cps ↑(range cnum) := by
    intro k hk k' hk' he
    have hk₁ := mem_range.mp (Finset.mem_coe.mp hk)
    have hk₂ := mem_range.mp (Finset.mem_coe.mp hk')
    rcases Nat.lt_trichotomy k k' with h | h | h
    · exact absurd he (by have := hmono k k' h hk₂; omega)
    · exact h
    · exact absurd he.symm (by have := hmono k' k h hk₁; omega)
  rw [← Finset.sum_image (g := cps) (f := fun c => blockSize Xoff c) hinj]
  refine sum_blockSize_le_aliveMass _ fun c hc => ?_
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
  exact ⟨hlt k (mem_range.mp hk), halv k (mem_range.mp hk)⟩

/-- **The turn count, against the alive mass** — B3's floor escape
(`cnum ≤ mm`) with the dead centres out of the bound. Every listed
position owns a non-empty block, so the count is under the total, and the
total is `aliveMass_le`'s. -/
theorem cnum_le_aliveMass {cps : ℕ → ℕ} {cnum : ℕ}
    (hmono : ∀ k k' : ℕ, k < k' → k' < cnum → cps k < cps k')
    (hlt : ∀ k < cnum, cps k < n) (halv : ∀ k < cnum, A₀ (ord (cps k)) ≠ 0)
    (hne : ∀ k < cnum, Xoff (cps k) < Xoff (cps k + 1)) :
    cnum ≤ aliveMass A₀ ord Xoff n := by
  refine le_trans ?_ (sum_blockSize_cps_le_aliveMass hmono hlt halv)
  calc cnum = ∑ _k ∈ range cnum, 1 := by simp
    _ ≤ ∑ k ∈ range cnum, blockSize Xoff (cps k) :=
        Finset.sum_le_sum fun k hk => by
          have := hne k (mem_range.mp hk); rw [blockSize]; omega

/-! ### §3.1 Every block is non-empty, so the non-empty predicate is total

The same self-membership that refutes the arena-wide alive clause also
says that **no block of a cover output is empty**: the centre at position
`c` is weakly `2r`-reachable from itself, and `CoverOut.block` is an iff.

The consequence is B3's: a compaction that lists the positions with
`Xoff c < Xoff (c + 1)` lists **all `n` of them**, so `cnum = n`
identically and `cnum ≤ mm` — true as stated — escapes nothing. The
predicate has to be aliveness (§2 of the header); `cnum_eq_of_nonempty`
is the refutation, and it is a theorem, not a check. -/

/-- **No block is empty.** -/
theorem block_nonempty (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) {c : ℕ} (hc : c < n) :
    Xoff c < Xoff (c + 1) := by
  have hin : InCluster (masked G A₀) π r (ord c) (ord c) :=
    ⟨hord.lt hc, hord.lt hc, self_mem_wreach _ _ _ _⟩
  obtain ⟨p, hp1, hp2, -⟩ := (h.block c hc (ord c)).mpr hin
  omega

/-- **B3's compaction lists every position.** With the non-empty-block
predicate — which `block_nonempty` says every position passes — a list
that is strictly increasing, in range, and complete has exactly `n`
entries. So the turn count is the carrier's, and the floor escape is
nominal until the predicate changes. -/
theorem cnum_eq_of_nonempty (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) {cps : ℕ → ℕ} {cnum : ℕ}
    (hlt : ∀ k < cnum, cps k < n)
    (hmono : ∀ k k' : ℕ, k < k' → k' < cnum → cps k < cps k')
    (hcomplete : ∀ c < n, Xoff c < Xoff (c + 1) → ∃ k < cnum, cps k = c) :
    cnum = n := by
  classical
  have hinj : Set.InjOn cps ↑(range cnum) := by
    intro k hk k' hk' he
    have hk₁ := mem_range.mp (Finset.mem_coe.mp hk)
    have hk₂ := mem_range.mp (Finset.mem_coe.mp hk')
    rcases Nat.lt_trichotomy k k' with hh | hh | hh
    · exact absurd he (by have := hmono k k' hh hk₂; omega)
    · exact hh
    · exact absurd he.symm (by have := hmono k' k hh hk₁; omega)
  have hcard : ((range cnum).image cps).card = cnum := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : (range cnum).image cps ⊆ range n := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
    exact mem_range.mpr (hlt k (mem_range.mp hk))
  have hsup : range n ⊆ (range cnum).image cps := by
    intro c hc
    obtain ⟨k, hk, hkc⟩ :=
      hcomplete c (mem_range.mp hc) (block_nonempty hord h (mem_range.mp hc))
    exact Finset.mem_image.mpr ⟨k, mem_range.mpr hk, hkc⟩
  have h₁ : cnum ≤ n := by
    rw [← hcard, ← Finset.card_range n]; exact Finset.card_le_card hsub
  have h₂ : n ≤ cnum := by
    rw [← hcard, ← Finset.card_range n]; exact Finset.card_le_card hsup
  omega

/-! ### §3.2 The two lines the level condition cites

`MassMath.mass_le_of_alive`'s conclusion, at the two quantities the
Σ-shaped level condition of `CostRecurrence.exists_driverCostsSigma`
actually reads: the number of turns, and the total sub-arena size over
the turns. Both against `{v | A₀ v ≠ 0}` — `RamDriverCluster.markSet n A₀`
unfolded, so the instantiation is by `rfl`. -/

/-- **The turn count is under the mass shape.** -/
theorem cnum_le_mass_shape (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) (hinj : BlockInj n Xoff Xmem)
    {d : ℕ} (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    {cps : ℕ → ℕ} {cnum : ℕ}
    (hmono : ∀ k k' : ℕ, k < k' → k' < cnum → cps k < cps k')
    (hlt : ∀ k < cnum, cps k < n) (halv : ∀ k < cnum, A₀ (ord (cps k)) ≠ 0)
    (hne : ∀ k < cnum, Xoff (cps k) < Xoff (cps k + 1)) :
    cnum ≤ d * (({v : Fin n | A₀ (v : ℕ) ≠ 0} : Set (Fin n)).ncard + 1) :=
  le_trans (cnum_le_aliveMass hmono hlt halv hne) (aliveMass_le hord h hinj hk)

/-- **And so is the sum of the sub-arenas the turns descend into.** -/
theorem sum_blockSize_cps_le_mass_shape (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) (hinj : BlockInj n Xoff Xmem)
    {d : ℕ} (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    {cps : ℕ → ℕ} {cnum : ℕ}
    (hmono : ∀ k k' : ℕ, k < k' → k' < cnum → cps k < cps k')
    (hlt : ∀ k < cnum, cps k < n) (halv : ∀ k < cnum, A₀ (ord (cps k)) ≠ 0) :
    ∑ k ∈ range cnum, blockSize Xoff (cps k)
      ≤ d * (({v : Fin n | A₀ (v : ℕ) ≠ 0} : Set (Fin n)).ncard + 1) :=
  le_trans (sum_blockSize_cps_le_aliveMass hmono hlt halv) (aliveMass_le hord h hinj hk)

/-- **The floor, exactly.** The arena's length is the alive mass plus one
cell for every dead centre — the `m ≥ n` of B6's finding, quantified. -/
theorem mass_eq_aliveMass_add_dead (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) (hinj : BlockInj n Xoff Xmem) :
    m = aliveMass A₀ ord Xoff n + ((range n).filter (fun c => A₀ (ord c) = 0)).card := by
  classical
  have hdead : ∀ c ∈ (range n).filter (fun c => A₀ (ord c) = 0), blockSize Xoff c = 1 := by
    intro c hc
    obtain ⟨hcr, hcd⟩ := Finset.mem_filter.mp hc
    have hcn : c < n := mem_range.mp hcr
    rw [blockSize_eq_ncard h hinj hcn, clusterAt_dead hcn hord hcd, Set.ncard_singleton]
  have hsplit : ∑ c ∈ range n, blockSize Xoff c
      = ∑ c ∈ (range n).filter (fun c => A₀ (ord c) = 0), blockSize Xoff c
        + ∑ c ∈ (range n).filter (fun c => ¬ A₀ (ord c) = 0), blockSize Xoff c :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hm : ∑ c ∈ range n, blockSize Xoff c = m := by rw [sum_blockSize h n le_rfl, h.last]
  have halive : aliveMass A₀ ord Xoff n
      = ∑ c ∈ (range n).filter (fun c => ¬ A₀ (ord c) = 0), blockSize Xoff c := by
    rw [aliveMass, Finset.sum_filter]
    exact Finset.sum_congr rfl fun c _ => by
      by_cases hd : A₀ (ord c) = 0
      · rw [if_pos hd, if_neg (by simpa using hd)]
      · rw [if_neg hd, if_pos (by simpa using hd)]
  rw [halive, ← hm, hsplit, Finset.sum_congr rfl hdead, Finset.sum_const, smul_eq_mul,
    Nat.mul_one]
  omega

/-! ### §4 Falsification

The refutation of §0 is a theorem, not a check. What the checks pin is
the *size* of the gap the theorem explains, and the two edge readings. -/

section Falsification

/-- Eight positions, the identity ordering, every block a singleton. -/
private def dOrd : ℕ → ℕ := id

private def dXoff : ℕ → ℕ := fun c => c

/-- Only vertex `0` alive — the shape of a nested arena. -/
private def dAlv : ℕ → ℕ := fun v => if v = 0 then 1 else 0

/-- Every vertex alive — the root call. -/
private def dAll : ℕ → ℕ := fun _ => 1

-- **The gap.** The arena is eight cells long; seven of them are the dead
-- centres' own singletons, and the alive mass is `1`. This is `m ≥ n`
-- with `n = 8`, and it is what `alive_carrier_of_alive_arena` explains.
#guard (∑ c ∈ Finset.range 8, blockSize dXoff c) = 8
#guard aliveMass dAlv dOrd dXoff 8 = 1

-- **The two agree when nothing is dead**, which is the only case
-- `MassMath.mass_le_of_alive` has an instance in.
#guard aliveMass dAll dOrd dXoff 8 = 8

-- **The dead count is the difference** (`mass_eq_aliveMass_add_dead`,
-- read at this instance).
#guard ((Finset.range 8).filter (fun c => dAlv (dOrd c) = 0)).card = 7
#guard aliveMass dAlv dOrd dXoff 8
  + ((Finset.range 8).filter (fun c => dAlv (dOrd c) = 0)).card = 8

-- **Empty blocks contribute nothing on either side**: an arena whose
-- offsets never advance has alive mass zero however the mask reads.
private def eXoff : ℕ → ℕ := fun _ => 5

#guard aliveMass dAll dOrd eXoff 8 = 0
#guard aliveMass dAlv dOrd eXoff 8 = 0

-- **A negative control on the consumer's form.** A position list that
-- includes a *dead* centre is not bounded by the alive mass — which is
-- why `sum_blockSize_le_aliveMass` asks for aliveness and B3's
-- non-empty-block predicate is not enough.
#guard ¬ (∑ c ∈ Finset.range 8, blockSize dXoff c) ≤ aliveMass dAlv dOrd dXoff 8

end Falsification

/-! ### §5 Axioms -/

/-- info: 'Lax3Proofs.Refine.MassAlive.alive_carrier_of_alive_arena' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms alive_carrier_of_alive_arena

/-- info: 'Lax3Proofs.Refine.MassAlive.aliveMass_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms aliveMass_le

/-- info: 'Lax3Proofs.Refine.MassAlive.mass_eq_aliveMass_add_dead' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms mass_eq_aliveMass_add_dead

/-- info: 'Lax3Proofs.Refine.MassAlive.cnum_eq_of_nonempty' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms cnum_eq_of_nonempty

end Lax3Proofs.Refine.MassAlive
