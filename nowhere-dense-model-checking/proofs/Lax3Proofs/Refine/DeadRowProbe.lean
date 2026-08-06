import Lax3Proofs.TgtWidenProbe
import Lax3Proofs.Refine.DeadSweep
import Lax3Proofs.Refine.ArenaBlock
import Lax3Proofs.Refine.G2ExistsRevalidation

/-!
# R1.8-design — dead vertices' obligations without the carrier, compiled both ways

The design question left by `Refine.DeadSweep` §4b (finding R1.8/1) and
`Refine.G2CostProbe.hKd_gap`/`hKbase_gap`: once the member list is the
only thing a level walks, who pays for the DEAD vertices — the rows the
sweep writes (`RamDriver.DeadRows`), the carrier-wide table invariant
(`RamDriver.TableInv`), and the base's representative story
(`BotEval.sat_exU_bot_of_repr`'s `hW`)? The recorded intent was *"a
vertex's death-row write charges to the turn that killed it — its block
contains it."* This file is the probe; the design document is
`plans/nowhere-dense-model-checking/r18-design.md`. **Nothing here edits
a landed declaration.**

**The verdict, compiled.** The conjecture holds for exactly HALF the
dead set, and the other half needs no writes at all:

* The dead set at a child depth splits along the turn's cluster into
  the **kill set** (in the cluster, dead in the child mask — the batch)
  and the **outside class** (not in the cluster). `deadRows_split` is
  that partition of the landed obligation, generic in everything.
* **Kill set: block-contained, turn-charged.** The only dead rows the
  parent's readback ever consults are kills of its own turn
  (`readback_dead_read_is_kill` — every `asg`-visited vertex is alive
  at the parent depth and lies in the turn's cluster), and the
  kill-time write is compiled carrier-blind at
  `(3·t + 20)·kills + 6` (`killTurnCom`, §5 guards).
* **Outside class: colour-uniform, zero writes.** Every colour class of
  the child palette lives inside the cluster
  (`stepColoringP_subset` — the marker and old slots by construction,
  the profile slots because an out-of-cluster vertex is isolated in the
  cluster-restricted arena), so the whole outside class shares the
  EMPTY colour row, and one vertex answers for all of them: their table
  bits agree formula by formula (`sat_outside_uniform`), and the base's
  witness search closes over the cluster plus ONE outside
  representative (`sat_exU_bot_via_cluster`, at most `bs + 1`
  representatives — `cluster_repr_ncard` — found in `bs + 1` probes —
  `exists_outside_in_prefix`). Materializing the class's rows instead
  is a carrier walk wherever it runs (`no_coeff_pays_outsideRows`,
  `deadScanCom`'s compiled `Ω(n)`).
* **No resurrection.** Dead-ness DOES grow down the recursion at the
  landed interface: `dead_stays_dead` derives `M v = 0 → Alv' v = 0`
  from `RamDriverCluster.DescendStep`'s cluster-inclusion clause (the
  rebase G2/E6 export) plus alive-homogeneity — the pointwise clause
  whose absence finding B8/1
  (`Refine.DeadRow.descent_mask_not_pointwise_monotone`) recorded
  against `BatchData` alone. B8/1's consequence ("the dead-vertex path
  has to run at every level") is thereby superseded.
* **The base's `reprCom` is vestigial.** Every tabled formula is local
  (`tabled_isLocal`, off `FormulaTables.tableRank_of_mem_tablesAt`), so
  `botCom`'s `exU` case — the only reader of the representative table —
  is unreachable (`RamDriverBot` discharges it by `isLocal_exU`), and
  the landed `reprCost`'s carrier scan (`hKbase_gap`'s floor) guards a
  pass whose output is dead code. The dead-vertex representative story
  compiled here is the contingency the `exU` case would need, and the
  uniformity germ the E4 scatter fold does need.

Directions per the standing rule: existence (§4 splits + the landed
`sweepImplements` inhabits the weakened forms; `junkEnv` separates them;
`n = 0` flip gates), positive cost (§5, pinned constants, carrier-blind,
linear in kills, per-row size class), negative cost (§5, the dead-set
scan's compiled `Ω(n)` and the outside-class arithmetic), and the Σ
interface closed at the probed constants (§6,
`G2ExistsRevalidation.g2m_exists` consumed, not re-derived).
-/

namespace Lax3Proofs.Refine.DeadRowProbe

open Lax3.ColoredGraphs Lax3.DistFO
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3Proofs.FormulaTables
open Lax3Proofs.WalkDistance (mem_ball_self)
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamDriver (tabName colRead stepColoringP foldRange alvName cluName
  DeadRows TableInv)
open Lax3Proofs.RamDriverCluster (markSet eq_of_arrOf_eq)
open Lax3Proofs.Refine.MassMath (clusterAt)
open Lax3Proofs.Refine.MassAlive (clusterAt_subset_alive)
open Lax3Proofs.Refine.DeadRow (eq_of_walk_isolated)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## §1 No resurrection: dead-ness grows down the recursion

Finding B8/1 (`Refine.DeadRow.descent_mask_not_pointwise_monotone`)
showed the pointwise clause `M v = 0 → Alv' v = 0` is not derivable
from `BatchData`'s graph equation. It IS derivable from the clause the
G2/E6 restatement put into `RamDriverCluster.DescendStep`'s
postcondition — `∀ v, Alv' v ≠ 0 → v ∈ clusterAt …` — because a
cluster is alive-homogeneous and the compaction runs alive centres
only. So the incremental design has its monotonicity at the landed
interface, and B8/1's consequence is superseded. -/

/-- **Dead stays dead.** From the descent's cluster-inclusion clause
(`DescendStep`'s postcondition, rebase G2/E6) and the turn's own
alive-centre guard (`compactCom`'s filter): a vertex dead at the
parent depth is dead at the child depth. -/
theorem dead_stays_dead {n cap cur : ℕ} {G : SimpleGraph (Fin n)} {M Alv' : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {ord : ℕ → ℕ}
    (hclu : ∀ v : Fin n, Alv' (v : ℕ) ≠ 0 → v ∈ clusterAt G M π ord cap cur)
    (hcen : M (ord cur) ≠ 0) {v : Fin n} (hv : M (v : ℕ) = 0) : Alv' (v : ℕ) = 0 := by
  by_contra h
  exact clusterAt_subset_alive hcen (hclu v h) hv

/-- **Every vertex the readback visits lies in its own turn's
cluster** — `CoverOut.asg_cover` at the vertex's own ball. This is the
"its block contains it" half of the recorded intent, at the landed
cover output. -/
theorem readback_vertex_in_cluster {n r m : ℕ} {G : SimpleGraph (Fin n)} {A₀ : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {ord Xoff Xmem asg : ℕ → ℕ}
    (h : RamCover.CoverOut G A₀ π ord r m Xoff Xmem asg) {v : ℕ} (hv : v < n) :
    (⟨v, hv⟩ : Fin n) ∈ clusterAt G A₀ π ord r (asg v) :=
  h.asg_cover v hv (mem_ball_self _ _ _)

/-- **The dead rows the readback consults are the turn's own kills.**
A vertex the depth-`j` readback visits (`asg v = k`, the running
centre) is alive at depth `j` and lies in the turn's cluster; so if it
is dead at depth `j + 1`, it is a vertex THIS turn killed, and its row
is block-owned. The outside class is never consulted by the readback —
that consumer's whole dead-read domain is the kill set. -/
theorem readback_dead_read_is_kill {n r m : ℕ} {G : SimpleGraph (Fin n)} {M : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {ord Xoff Xmem asg : ℕ → ℕ}
    (h : RamCover.CoverOut G M π ord r m Xoff Xmem asg) {k : ℕ}
    (hcen : M (ord k) ≠ 0) {v : ℕ} (hv : v < n) (hasg : asg v = k)
    {Alv' : ℕ → ℕ} (hdead : Alv' v = 0) :
    M v ≠ 0 ∧ Alv' v = 0 ∧ (⟨v, hv⟩ : Fin n) ∈ clusterAt G M π ord r k := by
  have hin := readback_vertex_in_cluster h hv
  rw [hasg] at hin
  exact ⟨clusterAt_subset_alive hcen hin, hdead, hin⟩

/-! ## §2 The outside class is colour-uniform

The child palette `RamDriver.stepColoringP` has three slot families
(`Evaluator.isoColoring` over `Evaluator.relColoring`), and every one
of them lives inside the cluster: the relativized slots by
construction (`∩ X`, marker `X`), and the two profile families because
their distances are measured in the cluster-restricted arena
`deleteVerts A Xᶜ`, where an out-of-cluster vertex is isolated and a
walk out of it is nil (`Refine.DeadRow.eq_of_walk_isolated`). So every
vertex outside the cluster carries the EMPTY colour row. -/

/-- Every relativized colour class lives inside the cluster. -/
theorem relColoring_subset {n L : ℕ} (col : Coloring n L) (X : Set (Fin n)) :
    ∀ c, Lax3Proofs.Evaluator.relColoring col X c ⊆ X := by
  intro c
  induction c using Fin.lastCases with
  | last => rw [Lax3Proofs.Evaluator.relColoring_last]
  | cast c => rw [Lax3Proofs.Evaluator.relColoring_castSucc]; exact Set.inter_subset_right

/-- **An isolated vertex is in no class of the isolation palette**,
provided the incoming classes and the batch avoid it: the old slots by
the incoming subset, the two profile slots because a walk out of an
isolated vertex is nil. -/
theorem isoColoring_notMem_of_isolated {n L' m' cap : ℕ} {A : SimpleGraph (Fin n)}
    {col : Coloring n L'} {w : Fin m' → Fin n} {X : Set (Fin n)}
    (hcol : ∀ c, col c ⊆ X) (hw : ∀ i, w i ∈ X) {x : Fin n}
    (hiso : ∀ z, ¬ A.Adj x z) (hx : x ∉ X) :
    ∀ s, x ∉ Lax3Proofs.Evaluator.isoColoring (cap := cap) A col w s := by
  intro s
  cases s using Fin.addCases with
  | left c =>
    intro hmem
    simp only [Lax3Proofs.Evaluator.isoColoring, Fin.addCases_left] at hmem
    exact hx (hcol c hmem)
  | right i =>
    cases i using Fin.addCases with
    | left p =>
      intro hmem
      simp only [Lax3Proofs.Evaluator.isoColoring, Fin.addCases_right, Fin.addCases_left,
        Set.mem_setOf_eq] at hmem
      obtain ⟨q, -⟩ := hmem
      exact hx (eq_of_walk_isolated hiso q ▸ hw (finProdFinEquiv.symm p).1)
    | right p =>
      intro hmem
      simp only [Lax3Proofs.Evaluator.isoColoring, Fin.addCases_right,
        Set.mem_setOf_eq] at hmem
      obtain ⟨y, hy, q, -⟩ := hmem
      exact hx (eq_of_walk_isolated hiso q ▸ hcol _ hy)

/-- **Every class of the child palette lives inside the cluster.** The
out-of-cluster vertices carry the empty colour row at the child depth —
the one fact the whole outside-class story rides on. -/
theorem stepColoringP_subset {n L mb cap : ℕ} {A : SimpleGraph (Fin n)}
    {col : Coloring n L} {X : Set (Fin n)} {w : Fin mb → Fin n}
    (hw : ∀ i, w i ∈ X) :
    ∀ s, stepColoringP cap A col X w s ⊆ X := by
  intro s x hx
  by_contra hxX
  have hiso : ∀ z, ¬ (deleteVerts A Xᶜ).Adj x z := fun z hadj =>
    hxX (by simpa using hadj.2.1)
  exact isoColoring_notMem_of_isolated (relColoring_subset col X) hw hiso hxX s hx

/-! ## §3 One vertex answers for the whole outside class

Equal colour rows transfer satisfaction on the edgeless arena
(`BotEval.sat_perm_bot` at the swap), and a dead vertex's arena IS the
edgeless arena for local formulas (`Refine.DeadRow.sat_bot_of_dead₁`).
So two dead vertices with equal rows have equal table bits, formula by
formula — and by §2 the whole outside class has ONE row, the empty
one. This is the "default row" germ: the base's witness search needs
one outside representative, and the E4 scatter fold can carry the
outside class as a count times a default bit. -/

/-- Equal rows transfer satisfaction at a unary formula on the
edgeless arena — `BotEval.sat_exU_bot_swap`'s swap, at arity one. -/
theorem sat_bot_swap₁ {n L : ℕ} {col : Coloring n L} {u v : Fin n}
    (hrow : ∀ c, u ∈ col c ↔ v ∈ col c) (β : DistFO L 1) :
    Sat (⊥ : SimpleGraph (Fin n)) col (fun _ => u) β ↔
      Sat (⊥ : SimpleGraph (Fin n)) col (fun _ => v) β := by
  have hswap : ∀ (c : Fin L) (x : Fin n), x ∈ col c ↔ Equiv.swap u v x ∈ col c := by
    intro c x
    rcases eq_or_ne x u with rfl | hxu
    · rw [Equiv.swap_apply_left]; exact hrow c
    · rcases eq_or_ne x v with rfl | hxv
      · rw [Equiv.swap_apply_right]; exact (hrow c).symm
      · rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]
  have hcomp : (⇑(Equiv.swap u v)) ∘ (fun _ : Fin 1 => u) = fun _ => v := by
    funext i; simp
  rw [Lax3Proofs.BotEval.sat_perm_bot hswap β (fun _ => u), hcomp]

/-- **Two dead vertices with equal rows have equal bits**, at every
local formula, in the level's own arena. -/
theorem sat_dead_uniform {n L : ℕ} {G : SimpleGraph (Fin n)} {M : ℕ → ℕ}
    {col : Coloring n L} {u v : Fin n} (hu : M (u : ℕ) = 0) (hv : M (v : ℕ) = 0)
    (hrow : ∀ c, u ∈ col c ↔ v ∈ col c) {β : DistFO L 1} (hloc : IsLocal β) :
    (Sat (masked G M) col (fun _ => u) β ↔ Sat (masked G M) col (fun _ => v) β) :=
  (Refine.DeadRow.sat_bot_of_dead₁ hu hloc).trans
    ((sat_bot_swap₁ hrow β).trans (Refine.DeadRow.sat_bot_of_dead₁ hv hloc).symm)

/-- **The outside class has one bit per formula.** Two dead vertices
outside the cluster agree on every local formula in the child arena:
both rows are empty by §2. The whole class is a COUNT and a default
bit, not `n - bs` rows. -/
theorem sat_outside_uniform {n L mb cap : ℕ} {G A : SimpleGraph (Fin n)} {M : ℕ → ℕ}
    {col : Coloring n L} {X : Set (Fin n)} {w : Fin mb → Fin n} (hw : ∀ i, w i ∈ X)
    {u v : Fin n} (hu : M (u : ℕ) = 0) (hv : M (v : ℕ) = 0)
    (huX : u ∉ X) (hvX : v ∉ X)
    {β : DistFO (Lax3Proofs.Evaluator.isoPalette (L + 1) mb cap) 1} (hloc : IsLocal β) :
    (Sat (masked G M) (stepColoringP cap A col X w) (fun _ => u) β ↔
      Sat (masked G M) (stepColoringP cap A col X w) (fun _ => v) β) :=
  sat_dead_uniform hu hv
    (fun c => iff_of_false (fun h => huX (stepColoringP_subset hw c h))
      (fun h => hvX (stepColoringP_subset hw c h))) hloc

/-- **The representative system of the base, block-sized.** If every
colour class lives inside `X` and `z₀` is one off-tuple vertex outside
`X`, then `X ∪ {z₀}` is an off-tuple representative system for the
WHOLE carrier: an in-cluster vertex represents itself, and `z₀`
represents every outside vertex, their rows being equally empty. -/
theorem hW_of_outside_uniform {n L k : ℕ} (col : Coloring n L) (X : Set (Fin n))
    (hcol : ∀ c, col c ⊆ X) (m : Fin k → Fin n) (z₀ : Fin n) (hz₀X : z₀ ∉ X)
    (hz₀m : z₀ ∉ Set.range m) :
    ∀ v ∉ Set.range m, ∃ w ∈ X ∪ {z₀}, w ∉ Set.range m ∧
      ∀ c : Fin L, v ∈ col c ↔ w ∈ col c := by
  intro v hv
  by_cases hvX : v ∈ X
  · exact ⟨v, Or.inl hvX, hv, fun c => Iff.rfl⟩
  · exact ⟨z₀, Or.inr rfl, hz₀m, fun c =>
      iff_of_false (fun h => hvX (hcol c h)) (fun h => hz₀X (hcol c h))⟩

/-- **The base's witness search closes over the cluster plus one
vertex** — `BotEval.sat_exU_bot_of_repr`, consumed at the block-sized
system. This is the dead-vertex representative story the `exU` case
would need; `tabled_isLocal` below is why no landed consumer needs it
today. -/
theorem sat_exU_bot_via_cluster {n L k : ℕ} {col : Coloring n L} {m : Fin k → Fin n}
    (X : Set (Fin n)) (hcol : ∀ c, col c ⊆ X) (z₀ : Fin n) (hz₀X : z₀ ∉ X)
    (hz₀m : z₀ ∉ Set.range m) (φ : DistFO L (k + 1)) :
    Sat (⊥ : SimpleGraph (Fin n)) col m (.exU φ) ↔
      (∃ i, Sat (⊥ : SimpleGraph (Fin n)) col (Fin.snoc m (m i)) φ) ∨
        ∃ w ∈ X ∪ {z₀}, w ∉ Set.range m ∧
          Sat (⊥ : SimpleGraph (Fin n)) col (Fin.snoc m w) φ :=
  Lax3Proofs.BotEval.sat_exU_bot_of_repr φ (X ∪ {z₀})
    (hW_of_outside_uniform col X hcol m z₀ hz₀X hz₀m)

/-- The system is block-sized: at most the cluster plus one. -/
theorem cluster_repr_ncard {n : ℕ} (X : Set (Fin n)) (z₀ : Fin n) :
    (X ∪ {z₀}).ncard ≤ X.ncard + 1 := by
  calc (X ∪ {z₀}).ncard ≤ X.ncard + ({z₀} : Set (Fin n)).ncard :=
        Set.ncard_union_le X {z₀}
    _ = X.ncard + 1 := by rw [Set.ncard_singleton]

/-- **The outside representative is found in `bs + 1` probes.** Among
the first `X.ncard + 1` vertices, at least one is outside `X` — the
pigeonhole that makes `z₀`'s selection a block-charged scan, not a
carrier walk. -/
theorem exists_outside_in_prefix {n : ℕ} (X : Set (Fin n)) (hlt : X.ncard < n) :
    ∃ z : Fin n, (z : ℕ) ≤ X.ncard ∧ z ∉ X := by
  by_contra hcon
  push Not at hcon
  set f : Fin (X.ncard + 1) → Fin n :=
    fun i => ⟨(i : ℕ), lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt hlt)⟩ with hf
  have hinj : Function.Injective f := fun a b hab => by
    simpa [hf, Fin.ext_iff] using hab
  have hsub : Set.range f ⊆ X := by
    rintro z ⟨i, rfl⟩
    exact hcon _ (Nat.le_of_lt_succ i.isLt)
  have hr : (Set.range f).ncard = X.ncard + 1 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have := Set.ncard_le_ncard hsub X.toFinite
  omega

/-- **Every tabled formula is local** — so `botCom`'s `exU` case, the
only reader of `reprCom`'s table, is unreachable at every depth
(`RamDriverBot` discharges it by `SyntaxLemmas.isLocal_exU`), and the
base's landed `reprCost` carrier scan guards dead code. -/
theorem tabled_isLocal (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∀ β ∈ tablesAt q_top cap mb φ j, IsLocal β :=
  fun β hβ => (tableRank_of_mem_tablesAt j β hβ).1

/-! ## §4 The obligation, split at the cluster

`RamDriver.DeadRows` quantifies over the whole dead set. The split
below partitions it by the cluster indicator — the kill half is the
turn's, block-owned (§1); the outside half is the class §2/§3 pays
with a count and a default bit, and `outsideRows_forced_by_deadRows`
compiles that the LANDED statement really does force per-vertex rows
for it (the junk state satisfies the kill half and refutes the whole),
which is why the statement must weaken and not merely re-charge. -/

/-- The kill half of `DeadRows`: rows owed at the vertices of the
cluster the child mask killed. This is the whole dead-row obligation
the parent's readback consumes (`readback_dead_read_is_kill`). -/
def KillRows (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) {n : ℕ}
    (G : SimpleGraph (Fin n)) (j : ℕ) (Xa M : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (σ : Env) : Prop :=
  ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length) (Tb : ℕ → ℕ),
    σ.arrs (tabName j i) = arrOf n Tb →
    ∀ v : Fin n, Xa (v : ℕ) ≠ 0 → M (v : ℕ) = 0 →
      Tb (v : ℕ) ≤ 1 ∧
      (Tb (v : ℕ) ≠ 0 ↔ Sat (masked G M) (colRead n C (sigL cap mb j)) (fun _ => v)
        (tablesAt q_top cap mb φ j)[i])

/-- The outside half: rows at dead vertices out of the cluster. No
landed consumer reads them per-vertex once the sweep is gone; §3 is
the uniformity that replaces them. -/
def OutsideRows (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) {n : ℕ}
    (G : SimpleGraph (Fin n)) (j : ℕ) (Xa M : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (σ : Env) : Prop :=
  ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length) (Tb : ℕ → ℕ),
    σ.arrs (tabName j i) = arrOf n Tb →
    ∀ v : Fin n, Xa (v : ℕ) = 0 → M (v : ℕ) = 0 →
      Tb (v : ℕ) ≤ 1 ∧
      (Tb (v : ℕ) ≠ 0 ↔ Sat (masked G M) (colRead n C (sigL cap mb j)) (fun _ => v)
        (tablesAt q_top cap mb φ j)[i])

/-- **The landed obligation is exactly the two halves**, at any
indicator: the split is a partition of the quantifier domain and
nothing else. -/
theorem deadRows_split (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) {n : ℕ}
    (G : SimpleGraph (Fin n)) (j : ℕ) (Xa M : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (σ : Env) :
    DeadRows q_top cap mb φ G j M C σ ↔
      KillRows q_top cap mb φ G j Xa M C σ ∧ OutsideRows q_top cap mb φ G j Xa M C σ := by
  constructor
  · exact fun h => ⟨fun i hi Tb harr v _ hv => h i hi Tb harr v hv,
      fun i hi Tb harr v _ hv => h i hi Tb harr v hv⟩
  · rintro ⟨hk, ho⟩ i hi Tb harr v hv
    by_cases hX : Xa (v : ℕ) = 0
    · exact ho i hi Tb harr v hX hv
    · exact hk i hi Tb harr v hX hv

/-- The kill half is inhabited wherever the landed sweep ran:
weakening. Satisfiability of the new form is inherited from
`Refine.DeadSweep.sweepImplements`' discharge. -/
theorem killRows_of_deadRows {q_top cap mb : ℕ} {φ : Lax3.FirstOrder.FO 0} {n : ℕ}
    {G : SimpleGraph (Fin n)} {j : ℕ} {M C_ : _} (Xa : ℕ → ℕ) {σ : Env}
    (h : DeadRows q_top cap mb φ G j M C_ σ) :
    KillRows q_top cap mb φ G j Xa M C_ σ :=
  ((deadRows_split q_top cap mb φ G j Xa M C_ σ).mp h).1

/-- The flip gate: the kill half at the empty carrier. -/
theorem killRows_zero_carrier (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin 0)) (j : ℕ) (Xa M : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (σ : Env) :
    KillRows q_top cap mb φ G j Xa M C σ :=
  fun _ _ _ _ v => v.elim0

/-- The mostly-dead junk state: an arbitrary machine memory whose
table cells all read `7`. -/
def junkEnv : Env := { vars := fun _ => 0, arrs := fun _ => [7, 7], inp := [], out := [] }

/-- One alive vertex, one dead — dead OUTSIDE the (empty) kill set. -/
def junkMask : ℕ → ℕ := fun z => if z = 0 then 1 else 0

/-- **The outside half is what forces the carrier** — the separation
instance. The junk state satisfies the kill half of the obligation (its
kill set is empty: the mask never moved) and REFUTES the landed
`DeadRows` (the dead vertex's junk cell is not even a bit) — generic in
the formula, whenever the depth has any table at all. So dropping the
outside half is a genuine weakening, and it is exactly the weakening
§2/§3 pay for. -/
theorem outsideRows_forced_by_deadRows (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (hlen : 0 < (tablesAt q_top cap mb φ j).length) :
    KillRows q_top cap mb φ (G := (⊥ : SimpleGraph (Fin 2))) j junkMask junkMask
      (fun _ _ => 0) junkEnv ∧
    ¬ DeadRows q_top cap mb φ (G := (⊥ : SimpleGraph (Fin 2))) j junkMask
      (fun _ _ => 0) junkEnv := by
  constructor
  · intro i hi Tb harr v h1 h2
    fin_cases v
    · exact absurd h2 (by simp [junkMask])
    · exact absurd h1 (by simp [junkMask])
  · intro h
    have harr : junkEnv.arrs (tabName j 0) = arrOf 2 (fun _ => 7) := rfl
    have := (h 0 hlen (fun _ => 7) harr ⟨1, by omega⟩ (by simp [junkMask])).1
    omega

/-- `RamDriver.TableInv`, restricted to a domain: what a level owes on
`D` and nothing off it. `TableInv` is `TableInvOn` at the full carrier;
the incremental design states level posts at `alive ∪ kills`. -/
def TableInvOn (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) {n : ℕ}
    (G : SimpleGraph (Fin n)) (j : ℕ) (M : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (D : Set (Fin n))
    (σ : Env) : Prop :=
  ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length), ∃ Tb : ℕ → ℕ,
    σ.arrs (tabName j i) = arrOf n Tb ∧ (∀ v : Fin n, v ∈ D → Tb (v : ℕ) ≤ 1) ∧
    ∀ v : Fin n, v ∈ D → (Tb (v : ℕ) ≠ 0 ↔
      Sat (masked G M) (colRead n C (sigL cap mb j)) (fun _ => v)
        (tablesAt q_top cap mb φ j)[i])

/-- **The carrier-wide invariant is its two mask halves.** The alive
half is what the turns write; the dead half is `DeadRows`' content —
which splits further by `deadRows_split`. The reassembly uses only
that the two witnesses are the same array
(`RamDriverCluster.eq_of_arrOf_eq`). -/
theorem tableInv_iff_on_split (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) {n : ℕ}
    (G : SimpleGraph (Fin n)) (j : ℕ) (M : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (σ : Env) :
    TableInv q_top cap mb φ G j M C σ ↔
      (TableInvOn q_top cap mb φ G j M C {v : Fin n | M (v : ℕ) ≠ 0} σ ∧
       TableInvOn q_top cap mb φ G j M C {v : Fin n | M (v : ℕ) = 0} σ) := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩ <;>
    · obtain ⟨Tb, harr, hbit, hval⟩ := h i hi
      exact ⟨Tb, harr, fun v _ => hbit _ v.isLt, fun v _ => hval v⟩
  · rintro ⟨ha, hd⟩ i hi
    obtain ⟨Tb, harr, hbita, hvala⟩ := ha i hi
    obtain ⟨Tb', harr', hbitd, hvald⟩ := hd i hi
    have heq : ∀ v : Fin n, Tb (v : ℕ) = Tb' (v : ℕ) := fun v =>
      eq_of_arrOf_eq (harr.symm.trans harr') v.isLt
    refine ⟨Tb, harr, fun z hz => ?_, fun v => ?_⟩
    · by_cases hM : M z = 0
      · rw [show z = ((⟨z, hz⟩ : Fin n) : ℕ) from rfl, heq ⟨z, hz⟩]
        exact hbitd ⟨z, hz⟩ hM
      · exact hbita ⟨z, hz⟩ hM
    · by_cases hM : M (v : ℕ) = 0
      · rw [heq v]
        exact hvald v hM
      · exact hvala v hM

/-! ### The `hW` shapes, inhabited at a concrete instance

Four carrier vertices, cluster `{0, 1}`, one colour class `{0}` (inside
the cluster), outside representative `2`, empty environment: the
block-sized system covers the whole carrier, and the witness-search
`Iff` of `sat_exU_bot_via_cluster` closes on it. At `n = 0` the
quantifier is empty and the system is too. -/

def col4 : Coloring 4 1 := fun _ => {v | (v : ℕ) = 0}
def X4 : Set (Fin 4) := {v | (v : ℕ) < 2}

theorem col4_subset : ∀ c, col4 c ⊆ X4 := by
  intro c v hv
  simp only [col4, Set.mem_setOf_eq] at hv
  simp [X4, hv]

theorem hW4 : ∀ v ∉ Set.range (Fin.elim0 : Fin 0 → Fin 4),
    ∃ w ∈ X4 ∪ {(2 : Fin 4)}, w ∉ Set.range (Fin.elim0 : Fin 0 → Fin 4) ∧
      ∀ c : Fin 1, v ∈ col4 c ↔ w ∈ col4 c :=
  hW_of_outside_uniform col4 X4 col4_subset Fin.elim0 2 (by simp [X4])
    (by rintro ⟨i, -⟩; exact i.elim0)

example (φ : DistFO 1 1) :
    Sat (⊥ : SimpleGraph (Fin 4)) col4 Fin.elim0 (.exU φ) ↔
      (∃ i : Fin 0, Sat (⊥ : SimpleGraph (Fin 4)) col4 (Fin.snoc Fin.elim0 (Fin.elim0 i)) φ) ∨
        ∃ w ∈ X4 ∪ {(2 : Fin 4)}, w ∉ Set.range (Fin.elim0 : Fin 0 → Fin 4) ∧
          Sat (⊥ : SimpleGraph (Fin 4)) col4 (Fin.snoc Fin.elim0 w) φ :=
  sat_exU_bot_via_cluster X4 col4_subset 2 (by simp [X4])
    (by rintro ⟨i, -⟩; exact i.elim0) φ

-- the flip gate for the representative shape: at `n = 0` the carrier
-- quantifier is empty, so the system owes nothing
theorem hW_zero_carrier (col : Coloring 0 1) (X : Set (Fin 0)) :
    ∀ v ∉ Set.range (Fin.elim0 : Fin 0 → Fin 0), ∃ w ∈ X, w ∉ Set.range Fin.elim0 ∧
      ∀ c : Fin 1, v ∈ col c ↔ w ∈ col c :=
  fun v _ => v.elim0

/-! ## §5 The cost, both directions

The instrument is `TgtWidenProbe.execC`, as in `MemThreadProbe` §4.

**Positive**: `killTurnCom` is the kill-time write — walk the padded
batch buffer `wa` (the turn's own, `mb` entries), and at each entry
that is alive and in the cluster, write its child row (`t` table
stores, the stand-in for the depth-`(j+1)` `botCom` fold whose real
per-vertex constant is the landed `turnCost` — the same constant the
sweep pays per CARRIER vertex, `DeadSweep.sweepCost`). Its clock is
pinned `(3·t + 20)·kills + 6`: carrier-blind at carriers 100/200,
linear in the kill count, the row write at the row's own size class
`t`, and touched-only (the guard-dead run writes nothing).

**Negative**: `deadScanCom` — any per-level or per-entry pass over the
dead set — pays `15·t`-class per CARRIER vertex (`+1500` between the
same two carriers at `t = 2`), the program-level re-read of
`DeadSweep.no_memCoeff_pays_deadRows`; and `no_coeff_pays_outsideRows`
is the arithmetic that materializing the outside class's rows at kill
time is the same carrier walk in different clothes: the class has
`n - bs` members. -/

/-- The kill-time write pass: walk the batch buffer, guard on
alive-and-in-cluster, write the child row. -/
def killTurnCom (t mb : ℕ) : Com :=
  .seq (.assign "kk" (.lit 0))
    (.while (.lt (.var "kk") (.lit mb))
      (.seq (.assign "kv" (.get "wa" (.var "kk")))
        (.seq (.ite (.lt (.lit 0)
                (.mul (.get (alvName 0) (.var "kv")) (.get (cluName 0) (.var "kv"))))
              (foldRange (fun i => .store (tabName 1 i) (.var "kv") (.lit 1)) t)
              .skip)
          (.assign "kk" (.add (.var "kk") (.lit 1))))))

open Lax3Proofs.TgtWidenProbe (execC pB pF PSt)

/-- The turn context: batch entries `7, 91, 13` (padded to three), all
alive and in the cluster, tables at the carrier's length. -/
def killSt (n mb : ℕ) : PSt :=
  { vars := []
    arrs := [("wa", List.take mb [7, 91, 13] ++ List.replicate (3 - mb) 7),
             (alvName 0, (((List.replicate n 0).set 7 1).set 91 1).set 13 1),
             (cluName 0, (((List.replicate n 0).set 7 1).set 91 1).set 13 1),
             (tabName 1 0, List.replicate n 9), (tabName 1 1, List.replicate n 9)] }

/-- The same context with every batch entry dead: the guard skips. -/
def killStDead (n mb : ℕ) : PSt :=
  { vars := []
    arrs := [("wa", List.take mb [7, 91, 13] ++ List.replicate (3 - mb) 7),
             (alvName 0, List.replicate n 0),
             (cluName 0, (((List.replicate n 0).set 7 1).set 91 1).set 13 1),
             (tabName 1 0, List.replicate n 9), (tabName 1 1, List.replicate n 9)] }

def killClock (t n mb : ℕ) : ℕ := (execC pB pF (killTurnCom t mb) (killSt n mb)).2

-- the pass completes on every instance measured
#guard (execC pB pF (killTurnCom 2 3) (killSt 100 3)).1.isOk
#guard (execC pB pF (killTurnCom 2 3) (killSt 200 3)).1.isOk
#guard (execC pB pF (killTurnCom 2 3) (killStDead 100 3)).1.isOk

-- **carrier-blind**: equal clocks at carriers 100 and 200, at every
-- kill count — the write reads the batch, never the carrier
#guard killClock 2 100 0 = killClock 2 200 0
#guard killClock 2 100 2 = killClock 2 200 2
#guard killClock 2 100 3 = killClock 2 200 3

-- **linear in the kills, at the row's own size class**: the exact law
-- is `(3·t + 20)·kills + 6` — `3` per table cell of the row, `20` per
-- kill for the guard and the bookkeeping, `6` for the loop head
#guard killClock 2 100 0 = 6
#guard killClock 2 100 2 = (3 * 2 + 20) * 2 + 6
#guard killClock 2 100 3 = (3 * 2 + 20) * 3 + 6
#guard killClock 0 100 2 = (3 * 0 + 20) * 2 + 6
#guard killClock 0 100 3 = (3 * 0 + 20) * 3 + 6

-- **touched-only**: the killed rows are written, nothing else is —
-- and the guard-dead run writes nothing at all
#guard (execC pB pF (killTurnCom 2 3) (killSt 100 3)).1.cell (tabName 1 0) 7 = 1
#guard (execC pB pF (killTurnCom 2 3) (killSt 100 3)).1.cell (tabName 1 0) 91 = 1
#guard (execC pB pF (killTurnCom 2 3) (killSt 100 3)).1.cell (tabName 1 1) 13 = 1
#guard (execC pB pF (killTurnCom 2 3) (killSt 100 3)).1.cell (tabName 1 0) 0 = 9
#guard (execC pB pF (killTurnCom 2 3) (killSt 200 3)).1.cell (tabName 1 0) 199 = 9
#guard (execC pB pF (killTurnCom 2 3) (killStDead 100 3)).1.cell (tabName 1 0) 7 = 9

/-- **The negative control**: the dead-set pass as a carrier scan —
the landed `sweepCom`'s loop shape, whatever the body. Any per-level
(or worse, per-entry) walk of the dead set pays this. -/
def deadScanCom (t : ℕ) : Com :=
  .seq (.assign "z" (.lit 0))
    (.while (.lt (.var "z") (.var "n"))
      (.seq (foldRange (fun i => .store (tabName 1 i) (.var "z") (.lit 1)) t)
        (.assign "z" (.add (.var "z") (.lit 1)))))

def scanSt (n : ℕ) : PSt :=
  { vars := [("n", n)]
    arrs := [(tabName 1 0, List.replicate n 9), (tabName 1 1, List.replicate n 9)] }

def deadClock (t n : ℕ) : ℕ := (execC pB pF (deadScanCom t) (scanSt n)).2

#guard (execC pB pF (deadScanCom 2) (scanSt 100)).1.isOk
-- the clock GROWS with the carrier: `15` per carrier vertex at `t = 2`
-- — the `Ω(n)` shape of `no_memCoeff_pays_deadRows`, at the program
#guard deadClock 2 200 - deadClock 2 100 = 15 * 100
#guard deadClock 2 100 ≠ deadClock 2 200
-- while the kill-time write at the same arena is two orders below and
-- carrier-blind: the same three dead rows, `84` against `3006`
#guard killClock 2 200 3 = 84
#guard deadClock 2 200 = 3006

/-- **No coefficient pays the outside class per-vertex**: it has
`n - bs` members, so a budget read at the block is beaten by the
carrier — the reason the outside class must be paid by uniformity
(§2/§3: a count and a default bit), not by writes. Mirror of
`DeadSweep.no_memCoeff_pays_deadRows`, located at the kill-time
alternative. -/
theorem no_coeff_pays_outsideRows (coeff bs : ℕ) :
    ∃ n : ℕ, bs < n ∧ coeff * (bs + 1) < n - bs :=
  ⟨coeff * (bs + 1) + bs + 1, by omega, by omega⟩

/-! ## §6 The Σ interface closes at the probed constants

`G2ExistsRevalidation.g2m_exists`, consumed at the incremental charge:

* the order and cover slots at the measured M-class law `68·m + 12`
  (`OrderSigProbeM`, unchanged);
* the DEAD slot `Kd` at the CONSTANT `12` — the per-level dead-sweep
  pass is GONE; what remains per level is `O(1)` bookkeeping (the
  outside count and default bit ride the turn);
* the turn coefficient at `ct = 284 = 200 + 84`: BlockLeaves' measured
  `200` plus the measured kill-time write at the probe's instance
  (`killClock 2 · 3 = 84` — three kills, two tables), the kill charge
  riding INSIDE the turn's size-read slot `turnCostSizeA`;
* the base clause `Cb` generic — the base level is the member-list
  sweep plus the block-sized representative story (§3), both
  weight-linear; the landed `reprCost` floor (`hKbase_gap`) guards the
  vestigial pass `tabled_isLocal` retires.

The `#guard` pins the turn absorption at the empty block: the landed
leaf coefficient plus the whole measured kill write fit the slot's
`s = 0` reading. -/

#guard 200 + killClock 2 100 3 ≤ 284 * (0 + 1)

theorem deadRow_interface_closes (Cb : ℕ) :
    ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
      (∀ j w m, m ≤ w →
        Lax3Proofs.Refine.G2ExistsRevalidation.phaseMR 68 12 0 m ≤ Ko j w) ∧
      (∀ j w m, m ≤ w →
        Lax3Proofs.Refine.G2ExistsRevalidation.phaseMR 68 12 0 m ≤ Kc j w) ∧
      (∀ j w m, m ≤ w →
        Lax3Proofs.Refine.G2ExistsRevalidation.phaseMR 0 12 0 m ≤ Kd j w) ∧
      (∀ w, Cb * (w + 1) ≤ Kl 3 w) ∧
      (∀ j, Monotone (Kl j)) ∧
      (∀ j < 3, ∀ s : ℕ,
        Lax3Proofs.Refine.G2CostProbe.turnCostSizeA 284 (10 ^ 4) s (Kl (j + 1) s) ≤
          Ks j s) ∧
      (∀ j < 3, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
        (∑ c ∈ Finset.range t, bs c) ≤ 8 * (w + 1) →
        Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
          ≤ Kl j w) ∧
      (∀ w, Kl 0 w ≤
        (3 * Lax3Proofs.Refine.G2ExistsRevalidation.g2M 68 12 68 12 0 12 0 284 (10 ^ 4) 8 +
          Cb) * (8 + 1) ^ 3 * (w + 1)) :=
  Lax3Proofs.Refine.G2ExistsRevalidation.g2m_exists 3 8 Cb 0 68 12 68 12 0 12 284 (10 ^ 4)
    (fun _ => 10 ^ 4) (fun _ _ => le_rfl)

/-! ## §7 Axioms -/

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.dead_stays_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dead_stays_dead

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.readback_dead_read_is_kill' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readback_dead_read_is_kill

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.stepColoringP_subset' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms stepColoringP_subset

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.sat_outside_uniform' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms sat_outside_uniform

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.sat_exU_bot_via_cluster' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms sat_exU_bot_via_cluster

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.exists_outside_in_prefix' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms exists_outside_in_prefix

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.tabled_isLocal' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms tabled_isLocal

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.deadRows_split' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms deadRows_split

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.outsideRows_forced_by_deadRows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms outsideRows_forced_by_deadRows

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.tableInv_iff_on_split' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms tableInv_iff_on_split

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.killRows_zero_carrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms killRows_zero_carrier

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.no_coeff_pays_outsideRows' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms no_coeff_pays_outsideRows

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.deadRow_interface_closes' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms deadRow_interface_closes

end Lax3Proofs.Refine.DeadRowProbe
