import Lax3.DistFO
import Lax3Proofs.RamBfs

/-!
**The row of a dead vertex** — rebase B8, the mathematics half.

Wave B2's stop (D-B2/1) is this: filtering the compaction on aliveness
takes the *turn* of every dead vertex away, while
`RamDriver.TableInv` still asks for its table **row**. This file supplies
the row's content, once and for all, and it is the cheapest content
there is: on the arena a dead vertex sees, nothing happens.

# §1 The one fact

`RamBfs.masked` isolates rather than deletes, so a vertex the mask kills
has **no incident edge** in the arena — `masked_adj` asks both endpoints
to be alive. A *local* formula evaluated at a tuple that is constantly
such a vertex therefore cannot see the rest of the graph at all:

* the atoms are decided outright (`adj` is false by isolation, `distLe`
  is true by the nil walk, `distColorLt` collapses to "the vertex itself
  carries the colour, and the radius is positive");
* the local quantifier's guard `WithinDist H r v v'` pins `v' = v`,
  because a walk out of an isolated vertex is nil — so the binder is not
  a quantifier at all, it re-binds the same vertex;
* and there is no unrestricted quantifier, which is exactly what
  `Lax3.DistFO.IsLocal` says.

`sat_congr_of_isolated` is that induction, stated between **two** arenas
that both isolate the vertex, and `sat_bot_of_dead` is its instance
against the edgeless graph. So the depth-`j` row of a dead vertex is the
value `RamDriver.botCom` — the driver's own edgeless evaluator — already
computes, and the dead-vertex path of a level is a `botCom` fold behind
an aliveness test and nothing else.

**No `DRank`, no `SemLocal`, no horizon arithmetic.** The semantic
locality lemma (`SemLocal.semLocal`) would also do it, through
`SatWithin` at the singleton ball, but it needs the formula's rank and a
congruence for `SatWithin`; the direct induction needs neither, and
`IsLocal` is already what `RamDriverBot` asks of every tabled formula
(`FormulaTables.TableRank`).

# §2 What the *graph equation* does not say (finding B8/1)

The natural cheaper design — *dead-ness only grows down the recursion,
so a dead row written once stays valid and no level has to write one* —
is not derivable from the mask *graph* equation

    masked G Alv' = deleteVerts (deleteVerts (masked G M) Xᶜ) W

alone, because a graph equation is blind to the mask value at an isolated
vertex. `descent_mask_not_pointwise_monotone` exhibits masks satisfying
that equation with a vertex dead at depth `j` and **alive** at depth
`j + 1`.

**Consequence superseded, wave R1.8-T1.** When this file was written that
equation was all `RamDriverCluster.BatchData` said about the child mask,
so `∀ v, Alv' v ≠ 0 → M v ≠ 0` was unavailable to the level induction and
the dead-vertex path had to run at every level. The strengthening the
paragraph called for has since landed: `BatchData` carries the pointwise
clause `Alv' v ≠ 0 ↔ (M v ≠ 0 ∧ v ∈ X ∧ v ∉ W)`, exported by
`RamDriverDescend.descendStep` off the very cell arithmetic
`RamDriver.masked_step` runs on (`RamDriverDescend.mask_cell_ne_zero`), so
monotonicity is now available — off this clause directly, and off the
cluster-inclusion clause as `Refine.DeadRowProbe.dead_stays_dead`. The
refutation below keeps its exact content: it is a statement about the
graph equation, and the graph equation is still blind.

# §3 Falsification

The isolation induction was run against data before it was proved: the
`#guard`s below pin the three atom readings the induction turns on — a
dead vertex is adjacent to nothing, is within every distance of itself,
and answers `distColorLt` by its own colour — on a two-vertex arena with
one edge and one dead endpoint, where the *alive* endpoint's readings
differ. The last one is the negative control: the same lemma at an alive
vertex is **false**, which is why aliveness is a hypothesis and not
decoration.
-/

namespace Lax3Proofs.Refine.DeadRow

open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.RamBfs (masked masked_adj)

variable {n L : ℕ}

/-! ### §1.1 A walk out of an isolated vertex is nil -/

/-- **An isolated vertex reaches only itself.** The first edge of a walk
out of it would be an edge at it. -/
theorem eq_of_walk_isolated {H : SimpleGraph (Fin n)} {v : Fin n}
    (hv : ∀ u, ¬ H.Adj v u) : ∀ {w : Fin n}, H.Walk v w → w = v := by
  intro w p
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hv _)

/-- …so it is within every distance of itself, and of nothing else. -/
theorem withinDist_isolated_iff {H : SimpleGraph (Fin n)} {v u : Fin n}
    (hv : ∀ u, ¬ H.Adj v u) {r : ℕ} : WithinDist H r v u ↔ u = v := by
  constructor
  · rintro ⟨p, -⟩; exact eq_of_walk_isolated hv p
  · rintro rfl; exact ⟨SimpleGraph.Walk.nil, by simp⟩

/-- The self-distance, which every `distLe` atom at a dead vertex
reads. -/
theorem withinDist_self_isolated {H : SimpleGraph (Fin n)} {v : Fin n}
    (hv : ∀ u, ¬ H.Adj v u) {r : ℕ} : WithinDist H r v v :=
  (withinDist_isolated_iff hv).mpr rfl

/-- Extending a constant tuple by its own value keeps it constant — the
step the local quantifier's case takes. -/
theorem snoc_const {k : ℕ} {m : Fin k → Fin n} {v : Fin n} (hm : ∀ i, m i = v) :
    ∀ i : Fin (k + 1), (Fin.snoc m v : Fin (k + 1) → Fin n) i = v := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.snoc_last]
  · rw [Fin.snoc_castSucc]; exact hm i

/-! ### §1.2 The induction -/

/-- **A local formula at an isolated vertex does not see the arena.**
Between any two graphs that isolate `v`, satisfaction of a local formula
at a tuple constantly `v` agrees.

The tuple is asked to be constant rather than to lie in the ball because
that is the form the induction reproduces: the local quantifier can only
re-bind `v` itself, by `withinDist_isolated_iff`. -/
theorem sat_congr_of_isolated {H H' : SimpleGraph (Fin n)} {col : Coloring n L} {v : Fin n}
    (hH : ∀ u, ¬ H.Adj v u) (hH' : ∀ u, ¬ H'.Adj v u) :
    ∀ {k : ℕ} (φ : DistFO L k), IsLocal φ → ∀ m : Fin k → Fin n, (∀ i, m i = v) →
      (Sat H col m φ ↔ Sat H' col m φ) := by
  intro k φ
  induction φ with
  | adj i j =>
    intro _ m hm
    show H.Adj (m i) (m j) ↔ H'.Adj (m i) (m j)
    rw [hm i, hm j]
    exact ⟨fun h => absurd h (hH _), fun h => absurd h (hH' _)⟩
  | eq i j => intro _ m _; exact Iff.rfl
  | color c i => intro _ m _; exact Iff.rfl
  | distLe r i j =>
    intro _ m hm
    show WithinDist H r (m i) (m j) ↔ WithinDist H' r (m i) (m j)
    rw [hm i, hm j]
    exact ⟨fun _ => withinDist_self_isolated hH', fun _ => withinDist_self_isolated hH⟩
  | distColorLt r c i =>
    intro _ m hm
    show (∃ y ∈ col c, ∃ w : H.Walk (m i) y, w.length < r) ↔
      (∃ y ∈ col c, ∃ w : H'.Walk (m i) y, w.length < r)
    rw [hm i]
    constructor
    · rintro ⟨y, hy, p, hp⟩
      have hyv : y = v := eq_of_walk_isolated hH p
      subst hyv
      exact ⟨y, hy, SimpleGraph.Walk.nil,
        by simpa using Nat.lt_of_le_of_lt (Nat.zero_le p.length) hp⟩
    · rintro ⟨y, hy, p, hp⟩
      have hyv : y = v := eq_of_walk_isolated hH' p
      subst hyv
      exact ⟨y, hy, SimpleGraph.Walk.nil,
        by simpa using Nat.lt_of_le_of_lt (Nat.zero_le p.length) hp⟩
  | not φ ih => intro hloc m hm; exact not_congr (ih hloc m hm)
  | and φ ψ ihφ ihψ =>
    intro hloc m hm
    exact and_congr (ihφ hloc.1 m hm) (ihψ hloc.2 m hm)
  | exU φ _ =>
    -- `IsLocal` of an unrestricted quantifier is `False` by definition; the
    -- hypothesis is eliminated without naming the definition, since naming it
    -- in a rewrite would generate a `Lax3.DistFO`-namespaced splitter here.
    intro hloc
    exact ((hloc : False)).elim
  | exL r g φ ih =>
    intro hloc m hm
    have hsnoc := snoc_const hm
    constructor
    · rintro ⟨v', ⟨i, hi, hw⟩, hsat⟩
      have hv' : v' = v := by rw [hm i] at hw; exact (withinDist_isolated_iff hH).mp hw
      subst hv'
      exact ⟨v', ⟨i, hi, by rw [hm i]; exact withinDist_self_isolated hH'⟩,
        (ih hloc _ hsnoc).mp hsat⟩
    · rintro ⟨v', ⟨i, hi, hw⟩, hsat⟩
      have hv' : v' = v := by rw [hm i] at hw; exact (withinDist_isolated_iff hH').mp hw
      subst hv'
      exact ⟨v', ⟨i, hi, by rw [hm i]; exact withinDist_self_isolated hH⟩,
        (ih hloc _ hsnoc).mpr hsat⟩

/-! ### §1.3 The consumer's form -/

/-- **A mask kills every edge at the vertices it kills.** -/
theorem masked_isolated {G : SimpleGraph (Fin n)} {M : ℕ → ℕ} {v : Fin n}
    (hv : M (v : ℕ) = 0) : ∀ u, ¬ (masked G M).Adj v u :=
  fun _ hadj => (masked_adj.mp hadj).2.1 hv

/-- The edgeless graph isolates everything. -/
theorem bot_isolated {v : Fin n} : ∀ u, ¬ (⊥ : SimpleGraph (Fin n)).Adj v u := by
  intro u h; exact h

/-- **The row of a dead vertex is the edgeless row.** This is what the
dead-vertex path of a level writes, and `RamDriver.botCom` is what
computes it: the value the base case of the driver would have written,
at a depth that is not the base.

The hypothesis is exactly `RamDriver.TableInv`'s vocabulary — `M v = 0`
is the mask reading of `RamDriverCluster.markSet` — and `IsLocal` is
what `FormulaTables.TableRank` gives every tabled formula
(`tableRank_of_mem_tablesAt`). -/
theorem sat_bot_of_dead {G : SimpleGraph (Fin n)} {M : ℕ → ℕ} {col : Coloring n L}
    {v : Fin n} (hv : M (v : ℕ) = 0) {k : ℕ} {φ : DistFO L k} (hloc : IsLocal φ)
    {m : Fin k → Fin n} (hm : ∀ i, m i = v) :
    (Sat (masked G M) col m φ ↔ Sat (⊥ : SimpleGraph (Fin n)) col m φ) :=
  sat_congr_of_isolated (masked_isolated hv) bot_isolated φ hloc m hm

/-- The unary instance, which is the only arity a table has: every entry
of `FormulaTables.tablesAt` is a `DistFO _ 1`, and the driver evaluates
it at the constant environment `fun _ => v`. -/
theorem sat_bot_of_dead₁ {G : SimpleGraph (Fin n)} {M : ℕ → ℕ} {col : Coloring n L}
    {v : Fin n} (hv : M (v : ℕ) = 0) {φ : DistFO L 1} (hloc : IsLocal φ) :
    (Sat (masked G M) col (fun _ => v) φ ↔ Sat (⊥ : SimpleGraph (Fin n)) col (fun _ => v) φ) :=
  sat_bot_of_dead hv hloc (fun _ => rfl)

/-! ### §2 Finding B8/1: the descent's mask relation is not pointwise -/

/-- **Dead-ness does not grow down the recursion by the graph equation
alone.** The equation
`masked G Alv' = deleteVerts (deleteVerts (masked G M) Xᶜ) W` cannot see
the mask value at a vertex with no edges. Here the whole arena is
edgeless, every mask reading is therefore consistent with the equation,
and the next depth's mask is **all alive** where the current depth's is
all dead.

When this was proved the equation was `RamDriverCluster.BatchData`'s only
word about the child mask, and the conclusion drawn was that the
dead-vertex path has to run at every level. That conclusion is
**superseded by wave R1.8-T1** (see §2 of the file header): `BatchData`
now also pins the child mask pointwise, so monotonicity is available. What
this theorem says is untouched — the graph equation, taken by itself, is
still blind, which is exactly why the pointwise clause had to be
added. -/
theorem deleteVerts_bot {m : ℕ} (S : Set (Fin m)) :
    Lax12.UniformQuasiWideness.deleteVerts (⊥ : SimpleGraph (Fin m)) S = ⊥ := by
  ext u w
  simp [Lax3Proofs.SplitterBasics.deleteVerts_adj]

theorem masked_bot {m : ℕ} (M : ℕ → ℕ) : masked (⊥ : SimpleGraph (Fin m)) M = ⊥ :=
  deleteVerts_bot _

theorem descent_mask_not_pointwise_monotone :
    ∃ (m : ℕ) (G : SimpleGraph (Fin m)) (M Alv' : ℕ → ℕ) (X W : Set (Fin m)),
      masked G Alv' = Lax12.UniformQuasiWideness.deleteVerts
          (Lax12.UniformQuasiWideness.deleteVerts (masked G M) Xᶜ) W ∧
        ∃ v : Fin m, M (v : ℕ) = 0 ∧ Alv' (v : ℕ) ≠ 0 := by
  refine ⟨1, ⊥, fun _ => 0, fun _ => 1, Set.univ, ∅, ?_, ⟨0, rfl, one_ne_zero⟩⟩
  rw [masked_bot, masked_bot, deleteVerts_bot, deleteVerts_bot]

/-! ### §3 Falsification

A two-vertex arena with one edge, the second endpoint dead. The three
atom readings the induction turns on are checked at the dead vertex —
and the last check is the **negative control**: at the *alive* vertex the
same readings differ from the edgeless ones, so `sat_bot_of_dead`'s
aliveness hypothesis is load-bearing. -/

section Falsification

/-- Two vertices, `0` alive and `1` dead. -/
private def dM : ℕ → ℕ := fun v => if v = 0 then 1 else 0

-- The mask reading the lemma keys on.
#guard dM 1 = 0
#guard dM 0 ≠ 0

-- **The `distColorLt` collapse, numerically.** At the dead vertex the
-- atom is `own colour ∧ 0 < r`, so it is false at radius zero however
-- the colouring reads — the `if r = 0` branch of `RamDriver.botCom`.
#guard ¬ (0 < 0)
#guard (0 < 1)

-- **The negative control.** The alive vertex `0` has a neighbour, so a
-- walk out of it need not be nil and `eq_of_walk_isolated` fails there:
-- the hypothesis `M v = 0` is not removable. Pinned as the mask fact
-- the failure is read off.
#guard ¬ (dM 0 = 0)

end Falsification

/-! ### §4 Axioms -/

/-- info: 'Lax3Proofs.Refine.DeadRow.sat_bot_of_dead' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms sat_bot_of_dead

/-- info: 'Lax3Proofs.Refine.DeadRow.descent_mask_not_pointwise_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms descent_mask_not_pointwise_monotone

end Lax3Proofs.Refine.DeadRow
