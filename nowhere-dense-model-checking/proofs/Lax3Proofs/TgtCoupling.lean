import Lax3Proofs.Augmentation
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
**The two `tgt` couplings, at the abstract level.**

`RamDriverCompose.orderImplements₀` is stated at `R = 0` and its header
says why: at `R > 0` "the two `tgt` couplings `OrderImplements`'s
docstring records are still open — `RamAugment.AugPre` asks for `tgt` at
the fraternity graph's own slot count while the driver's is the level's
`ns`, and nothing relates the width `W` to the in-degrees the chain
reaches."

# The reading

`OrderImplements`'s own docstring adds that the reason `AugPre` pins
`tgt` to `nf = fratSlots D` is the reasoning kit's `Csr` relation, which
couples a target array's length to the last offset; widening it "means
widening `tgt` in `RamBfs`, `RamCover`, `RamScatter` and `RamBfsPaths`
too, since all four pin it at `ns`". So the two couplings are, read as
mathematics and with every machine word removed:

* **(a) the level's slot count does not dominate the round's.** The
  driver holds one array at `ns`, the number of slots the *level's* graph
  occupies; a round needs `fratSlots D`, the number the *fraternity*
  graph occupies. The docstring's phrasing leaves open whether one is a
  bound for the other, and this file settles it: it is not, and the
  smallest witness is **K₁,₄** — a star on four leaves, oriented into its
  centre, whose fraternity graph is the complete graph on the leaves and
  occupies `12` slots against the star's `8`. Any repair therefore has to
  widen the array; none can reuse `ns`.
* **(b) what a width has to dominate is the in-degrees.** The positive
  half: `csrSlots_fratGraph_le` bounds a round's slot count by `n · d²`
  in the in-degree bound `d`, and `chainWidth` turns the in-degree budget
  of a greedy augmentation chain into a *single* width that dominates
  every round of the chain **and** the level's own graph. That is the
  fact the `R > 0` ordering phase needs in order to allocate once and
  keep `RamElim.ElimPre`'s "the call's slot count is only a lower bound"
  discipline through the fold.

Where the docstring is ambiguous — it names the couplings but does not
say in which direction they should be closed — this file states the
strongest abstract fact the text supports: (a) as a refutation of the
`ns`-dominates reading, with the concrete witness the brief names, and
(b) as a uniform width in the chain's own budget.

# The abstract vocabulary

`csrSlots F` is the number of slots a graph occupies in compressed-row
form — the abstract shadow of the driver's `ns` and of
`RamAugment.fratSlots`. `csrSlots_eq_sum_degree` is that it is the sum of
the degrees and `csrSlots_eq_two_mul` that it is twice the edge count,
which is what a `RamBfs.CsrSimple` block structure has in its target
array; the definition itself is a filter rather than
`SimpleGraph.degree` so that it computes on the witness below. Nothing in
this file mentions a machine state, an `Env` or a `Com`: the only imports
are the campaign's own orientation mathematics and mathlib.

`csrSlots (fratGraph D)` and `RamAugment.fratSlots D` are the same number
— `RamAugment.fratNbrs D v` is by `RamAugment.mem_fratNbrs` the neighbour
finset of `fratGraph D` — but that bridge is deliberately *not* proved
here, since it is one line at the consumer and proving it would drag the
`Ram*` stack into a file whose whole point is to be free of it.

# Falsification gate

The K₁,₄ witness is itself the falsification of coupling (a)'s optimistic
reading, and it is computed rather than argued (`#guard`, then the
theorems by `decide`). One more refutation is recorded: the star `K₁,₃` —
one leaf smaller — has fraternity slots `= ns` exactly, so no smaller
star refutes the coupling and `K₁,₄` is the smallest star witness. The
width arithmetic of coupling (b) is `#guard`-checked on the smallest
chain data.
-/

namespace Lax3Proofs.TgtCoupling

open Finset
open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation

variable {n : ℕ}

/-! ### Slots

The abstract shadow of a target array's length. -/

/-- The number of slots a graph occupies in compressed-row form: one per
incidence, i.e. the sum of the degrees. Spelled with an explicit filter
rather than `SimpleGraph.degree` so that it computes on a concrete
graph. -/
def csrSlots (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] : ℕ :=
  ∑ v, (Finset.univ.filter (fun u => F.Adj v u)).card

/-- Slots are the sum of the degrees. -/
theorem csrSlots_eq_sum_degree (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    csrSlots F = ∑ v, F.degree v := by
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]

/-- **Slots are twice the edges**, which is what a block structure of a
simple graph holds in its target array. -/
theorem csrSlots_eq_two_mul (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    csrSlots F = 2 * F.edgeFinset.card := by
  rw [csrSlots_eq_sum_degree]
  exact SimpleGraph.sum_degrees_eq_twice_card_edges F

/-- A graph on `n` vertices occupies at most `n²` slots. -/
theorem csrSlots_le_sq (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    csrSlots F ≤ n * n := by
  calc csrSlots F ≤ ∑ _v : Fin n, n := by
        refine Finset.sum_le_sum fun v _ => ?_
        calc (Finset.univ.filter (fun u => F.Adj v u)).card
            ≤ (Finset.univ : Finset (Fin n)).card :=
              Finset.card_le_card (Finset.subset_univ _)
          _ = n := by simp
    _ = n * n := by simp

/-! ### The fraternity graph's own slots

A fraternal partner of `v` is an in-neighbour of a vertex `v` points at,
so a vertex's fraternal degree is at most its out-degree times the
in-degree bound; summing, the out-degrees add up to the in-degrees. This
is `RamAugment.fratSlots_le` re-derived over `csrSlots`, so that the
bound is available without the engine files. -/

/-- The vertices `v` points at. -/
def outNbrs (D : Orientation n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => v ∈ D.inN w)

theorem mem_outNbrs {D : Orientation n} {v w : Fin n} : w ∈ outNbrs D v ↔ v ∈ D.inN w := by
  rw [outNbrs, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The fraternity graph is decidable, so its slot count is computable. -/
instance fratGraphDecidableRel (D : Orientation n) : DecidableRel (fratGraph D).Adj :=
  fun u v => decidable_of_iff (u ≠ v ∧ ∃ w, u ∈ D.inN w ∧ v ∈ D.inN w) Iff.rfl

/-- An orientation's own graph is decidable for the same reason. -/
instance toGraphDecidableRel (D : Orientation n) : DecidableRel D.toGraph.Adj :=
  fun u v => decidable_of_iff (u ∈ D.inN v ∨ v ∈ D.inN u) Iff.rfl

/-- The out-degrees add up to the in-degrees, both counting the arcs. -/
theorem sum_card_outNbrs (D : Orientation n) :
    ∑ v, (outNbrs D v).card = ∑ w, (D.inN w).card := by
  classical
  simp only [outNbrs, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.card_filter]
  congr 1
  ext v
  simp

/-- A fraternal partner of `v` is an in-neighbour of something `v` points
at. -/
theorem fratNeighborFinset_subset (D : Orientation n) (v : Fin n) :
    (fratGraph D).neighborFinset v ⊆ (outNbrs D v).biUnion (fun w => D.inN w) := by
  intro u hu
  rw [SimpleGraph.mem_neighborFinset] at hu
  obtain ⟨-, w, hvw, huw⟩ := fratGraph_adj.1 hu
  exact Finset.mem_biUnion.2 ⟨w, mem_outNbrs.2 hvw, huw⟩

/-- **The fraternity graph's width**: an orientation of in-degree at most
`d` has a fraternity graph occupying at most `n · d²` slots. This is the
positive half of coupling (a) — the bound a width has to meet — and it is
stated in the in-degree alone, never in the level's slot count. -/
theorem csrSlots_fratGraph_le {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) :
    csrSlots (fratGraph D) ≤ n * (d * d) := by
  classical
  have hstep : ∀ v : Fin n,
      (Finset.univ.filter (fun u => (fratGraph D).Adj v u)).card ≤ (outNbrs D v).card * d := by
    intro v
    rw [← SimpleGraph.neighborFinset_eq_filter]
    refine le_trans (Finset.card_le_card (fratNeighborFinset_subset D v)) ?_
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ w ∈ outNbrs D v, (D.inN w).card ≤ ∑ _w ∈ outNbrs D v, d :=
          Finset.sum_le_sum fun w _ => hd w
      _ = (outNbrs D v).card * d := by rw [Finset.sum_const, smul_eq_mul]
  calc csrSlots (fratGraph D) ≤ ∑ v, (outNbrs D v).card * d :=
        Finset.sum_le_sum fun v _ => hstep v
    _ = (∑ v, (outNbrs D v).card) * d := by rw [Finset.sum_mul]
    _ = (∑ w, (D.inN w).card) * d := by rw [sum_card_outNbrs]
    _ ≤ (∑ _w : Fin n, d) * d := Nat.mul_le_mul_right d (Finset.sum_le_sum fun w _ => hd w)
    _ = n * (d * d) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]

/-! ### Coupling (a), refuted: `ns` is no bound

The star on four leaves, every edge oriented into the centre. The
fraternity graph is the complete graph on the four leaves — any two
leaves point at the centre — so it occupies `4 · 3 = 12` slots, against
the star's `2 · 4 = 8`. The level's array is therefore too short for the
round by a factor that grows with the degree, and no repair can reuse
it. -/

section StarWitness

/-- The in-neighbour data of the star `K₁,₄` oriented into its centre. -/
def starIn : Fin 5 → Finset (Fin 5) := fun v => if v = 0 then {1, 2, 3, 4} else ∅

/-- **K₁,₄, oriented into its centre.** -/
def starOr : Orientation 5 where
  inN := starIn
  not_mem_self := by decide
  asymm := by decide

/-- The star itself occupies eight slots: four edges, twice each. -/
theorem csrSlots_starOr : csrSlots starOr.toGraph = 8 := by decide

/-- Its fraternity graph — the complete graph on the four leaves —
occupies twelve. -/
theorem csrSlots_fratGraph_starOr : csrSlots (fratGraph starOr) = 12 := by decide

/-- **Coupling (a), refuted.** The level's slot count is not a bound for
the round's: on `K₁,₄` the fraternity graph needs half as many slots
again as the graph it comes from. Hence `RamAugment.AugPre`'s `tgt` at
`fratSlots D` cannot be met by the driver's `tgt` at `ns`, and the
ordering phase at `R > 0` must allocate at a genuine width. -/
theorem not_csrSlots_fratGraph_le_csrSlots :
    ¬ csrSlots (fratGraph starOr) ≤ csrSlots starOr.toGraph := by decide

/-- The bound of `csrSlots_fratGraph_le` is met, with room: the star's
in-degree is `4`, and `5 · 16` is far above `12`. The gap is what makes
the coarse width usable. -/
theorem starOr_inDegLE : starOr.InDegLE 4 := by
  intro v
  fin_cases v <;> decide

end StarWitness

/-! ### Coupling (b): one width for the whole chain

Along a greedy augmentation chain the in-degrees follow
`Augmentation.budget`, which is monotone in the round; so the last
round's budget bounds every round's, and a single width cut to it
dominates every fraternity graph the chain materializes — and the
level's own graph too, which is the other array the ordering phase holds
at `ns`. -/

/-- The budget only grows. -/
theorem budget_le_succ (d D₁ i : ℕ) : budget d D₁ i ≤ budget d D₁ (i + 1) := by
  rw [show budget d D₁ (i + 1) = budget d D₁ i + budget d D₁ i * budget d D₁ i +
    (budget d D₁ i * budget d D₁ i + budget d D₁ i * D₁) from rfl]
  omega

/-- **The budget is monotone in the round.** -/
theorem budget_mono (d D₁ : ℕ) {i j : ℕ} (hij : i ≤ j) : budget d D₁ i ≤ budget d D₁ j := by
  induction j with
  | zero => simp [Nat.le_zero.1 hij]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact le_trans (ih (by omega)) (budget_le_succ d D₁ j)
      · have : i = j + 1 := by omega
        simp [this]

/-- **The width of a chain**: room for the fraternity graph of every
round — `n · (b+1)²` slots, `b` the last round's in-degree budget — and
for the level's own graph, which is at most `n²`. This is
`RamAugment.augWidth` at the chain's budget, plus the level's array; the
`+1` makes the bounds strict, which is the form `AugPre` consumes. -/
def chainWidth (n d D₁ r : ℕ) : ℕ := n * (budget d D₁ r + 1) ^ 2 + n * n + 1

/-- Every graph on the carrier fits in the width — in particular the
level's own, held at `ns`. -/
theorem csrSlots_lt_chainWidth (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (d D₁ r : ℕ) :
    csrSlots F < chainWidth n d D₁ r := by
  have h := csrSlots_le_sq F
  have : 0 ≤ n * (budget d D₁ r + 1) ^ 2 := Nat.zero_le _
  simp only [chainWidth]
  omega

/-- A round of in-degree at most `b` fits in the width. -/
theorem csrSlots_fratGraph_lt_chainWidth {D : Orientation n} {d D₁ r : ℕ}
    (hd : D.InDegLE (budget d D₁ r)) :
    csrSlots (fratGraph D) < chainWidth n d D₁ r := by
  have h₁ := csrSlots_fratGraph_le hd
  have h₂ : n * (budget d D₁ r * budget d D₁ r) ≤ n * (budget d D₁ r + 1) ^ 2 :=
    Nat.mul_le_mul_left n (by nlinarith)
  have : 0 ≤ n * n := Nat.zero_le _
  simp only [chainWidth]
  omega

/-- **Coupling (b).** On a greedy augmentation chain of `r` rounds whose
augmented graphs have depth-one density at most `D₁` and whose first
orientation has in-degree at most `d`, a single width — `chainWidth n d
D₁ r`, a function of the in-degrees the chain reaches and of nothing
else — dominates the slot count of every round's fraternity graph *and*
of the level's own graph.

This is the fact the `R > 0` ordering phase needs: the width `W` of
`RamDriver.OrderMem` may be allocated once, before the fold, from the
chain's budget. -/
theorem chainWidth_dominates {G : SimpleGraph (Fin n)} {D : ℕ → Orientation n} {r d D₁ : ℕ}
    (hchain : IsAugChain G D r) (hdens : AugmentedDepthOneDensity D r D₁)
    (hgreedy : ∀ i < r, GreedyFratRound (D i) (D (i + 1))) (hd0 : (D 0).InDegLE d) :
    (∀ (F : SimpleGraph (Fin n)) (_ : DecidableRel F.Adj), csrSlots F < chainWidth n d D₁ r) ∧
      ∀ i ≤ r, csrSlots (fratGraph (D i)) < chainWidth n d D₁ r := by
  refine ⟨fun F _ => csrSlots_lt_chainWidth F d D₁ r, fun i hi => ?_⟩
  have hdi : (D i).InDegLE (budget d D₁ i) :=
    greedy_chain_inDegLE hchain hdens hgreedy hd0 i hi
  exact csrSlots_fratGraph_lt_chainWidth
    (fun v => le_trans (hdi v) (budget_mono d D₁ hi))

/-! ### The repaired width (rebase G2/E2)

`chainWidth`'s `n · n` term exists to hold the level's own graph at the
generic `csrSlots_le_sq`; the level's graph occupies exactly `ns` slots
and every masked sub-arena's at most that, so the degree-aware width
reads `ns` and the `n · n` dies — `C0Probe.level_interface_floor_cubic`'s
`n · n ≤ W` step has no route through this width
(`Refine.G2CostProbe.width_step_dead` is the compiled instance). The
forms were designed and compiled in `Refine.G2CostProbe`; these are the
real declarations, wired verbatim. `chainWidth` itself stays: `C0Probe`'s
floor record is *about* it. -/

/-- **The width of a chain, degree-aware** (rebase G2/E2): room for the
fraternity graph of every round — `n · (b+1)²` slots, `b` the last
round's in-degree budget — and for the level's own graph at its actual
slot count `ns`, not at the generic `n · n`. -/
def chainWidthE (n ns d D₁ r : ℕ) : ℕ := n * (budget d D₁ r + 1) ^ 2 + ns + 1

/-- The new width never exceeds the old one on real inputs (`ns ≤ n·n`
holds of every slot count on the carrier), so every allocation the old
width served is served. -/
theorem chainWidthE_le_chainWidth {n ns d D₁ r : ℕ} (h : ns ≤ n * n) :
    chainWidthE n ns d D₁ r ≤ chainWidth n d D₁ r := by
  simp only [chainWidthE, chainWidth]
  omega

/-- **Fits, half 1**: the level's own graph fits the new width — at the
hypothesis its consumer actually has (`csrSlots F ≤ ns`; at the level
itself `csrSlots G = ns` exactly, and every masked sub-arena is a
subgraph). Replaces `csrSlots_lt_chainWidth`, whose proof was the
generic `csrSlots_le_sq`. -/
theorem csrSlots_lt_chainWidthE {n ns : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (d D₁ r : ℕ) (h : csrSlots F ≤ ns) :
    csrSlots F < chainWidthE n ns d D₁ r := by
  simp only [chainWidthE]
  omega

/-- **Fits, half 2**: a round's fraternity graph fits the new width,
unchanged — its bound `n · b²` lives entirely in the `n · (b+1)²` term.
Replaces `csrSlots_fratGraph_lt_chainWidth` verbatim. -/
theorem csrSlots_fratGraph_lt_chainWidthE {n ns : ℕ} {D : Orientation n} {d D₁ r : ℕ}
    (hd : D.InDegLE (budget d D₁ r)) :
    csrSlots (fratGraph D) < chainWidthE n ns d D₁ r := by
  have h₁ := csrSlots_fratGraph_le hd
  have h₂ : n * (budget d D₁ r * budget d D₁ r) ≤ n * (budget d D₁ r + 1) ^ 2 :=
    Nat.mul_le_mul_left n (by nlinarith)
  simp only [chainWidthE]
  omega

/-- **Coupling (b) at the repaired width.** `chainWidth_dominates` with
the level's-graph half read at the slot count: one width dominates every
round's fraternity graph and every carrier graph inside `ns` slots. -/
theorem chainWidthE_dominates {G : SimpleGraph (Fin n)} {D : ℕ → Orientation n}
    {ns r d D₁ : ℕ} (hchain : IsAugChain G D r) (hdens : AugmentedDepthOneDensity D r D₁)
    (hgreedy : ∀ i < r, GreedyFratRound (D i) (D (i + 1))) (hd0 : (D 0).InDegLE d) :
    (∀ (F : SimpleGraph (Fin n)) (_ : DecidableRel F.Adj), csrSlots F ≤ ns →
        csrSlots F < chainWidthE n ns d D₁ r) ∧
      ∀ i ≤ r, csrSlots (fratGraph (D i)) < chainWidthE n ns d D₁ r := by
  refine ⟨fun F _ hF => csrSlots_lt_chainWidthE F d D₁ r hF, fun i hi => ?_⟩
  have hdi : (D i).InDegLE (budget d D₁ i) :=
    greedy_chain_inDegLE hchain hdens hgreedy hd0 i hi
  exact csrSlots_fratGraph_lt_chainWidthE
    (fun v => le_trans (hdi v) (budget_mono d D₁ hi))

/-- **The capacity step of a round** (rebase G2/E2): the next budget
holds `2·b² + b`, which is the room the round's raw assembly needs —
`RamDriverAugment.sum_augDeg_le_arcs` bounds the written arcs by
`(2·b + 1) · m ≤ n · b · (2·b + 1) = n · (2·b² + b)`. This is what
replaces the `n · n` room of `RamAugment.augWidth` in the fold's
capacity discharge. -/
theorem two_sq_add_le_budget_succ (d D₁ i : ℕ) :
    2 * (budget d D₁ i * budget d D₁ i) + budget d D₁ i ≤ budget d D₁ (i + 1) := by
  rw [show budget d D₁ (i + 1) = budget d D₁ i + budget d D₁ i * budget d D₁ i +
    (budget d D₁ i * budget d D₁ i + budget d D₁ i * D₁) from rfl]
  omega

/-! ### Falsification

The K₁,₄ computation is the falsification of coupling (a)'s optimistic
reading and is checked by `decide` above. Two further readings are
refuted here. -/

section Falsification

/-- The star on *three* leaves, oriented into its centre. -/
def star3In : Fin 4 → Finset (Fin 4) := fun v => if v = 0 then {1, 2, 3} else ∅

/-- `K₁,₃`, oriented into its centre. -/
def star3Or : Orientation 4 where
  inN := star3In
  not_mem_self := by decide
  asymm := by decide

-- **Refuted**: `K₁,₄` is the smallest star witness. On `K₁,₃` the two
-- slot counts are equal — `3 · 2 = 6 = 2 · 3` — so the strict inequality
-- of `not_csrSlots_fratGraph_le_csrSlots` is not available one leaf
-- lower, and no smaller star refutes the coupling.
#guard csrSlots (fratGraph star3Or) = 6
#guard csrSlots star3Or.toGraph = 6
#guard ¬ (csrSlots star3Or.toGraph < csrSlots (fratGraph star3Or))

-- The witness's own numbers, and the bound of `csrSlots_fratGraph_le`
-- checked against them: `n · d² = 5 · 16` is met with room, and the
-- refutation is of the *level's* slot count as a bound, not of this one.
-- (The linear bound `n · d = 20` happens to hold on this witness too;
-- nothing here claims it is a theorem, and `csrSlots_fratGraph_le` is
-- stated at `d²` because that is what the counting argument gives.)
#guard csrSlots (fratGraph starOr) = 12
#guard csrSlots starOr.toGraph = 8
#guard 12 ≤ 5 * (4 * 4)
#guard ¬ (csrSlots (fratGraph starOr) ≤ csrSlots starOr.toGraph)

-- the width arithmetic, on the smallest data: a two-round chain from
-- in-degree `1` with density budget `1` reaches budget `budget 1 1 2`,
-- and the width dominates both `n²` and `n · b²`
#guard budget 1 1 0 = 1
#guard budget 1 1 1 = 4
#guard budget 1 1 2 = 4 + 16 + (16 + 4)
#guard budget 1 1 1 ≤ budget 1 1 2
#guard csrSlots starOr.toGraph < chainWidth 5 1 1 2
#guard csrSlots (fratGraph starOr) < chainWidth 5 1 1 2

-- the repaired width on the same data: the star's `ns = 8` replaces the
-- `n² = 25` term, both graphs still fit, and the new width sits strictly
-- below the old one
#guard csrSlots starOr.toGraph < chainWidthE 5 8 1 1 2
#guard csrSlots (fratGraph starOr) < chainWidthE 5 8 1 1 2
#guard chainWidthE 5 8 1 1 2 < chainWidth 5 1 1 2

-- **the floor route is dead at the real surface**: at a sparse instance
-- (`n = 10⁶`, `ns = 2·10⁶`) the repaired width itself is an admissible
-- `W` for the new `hWc`, and `n · n ≤ W` fails at it — the
-- `level_interface_floor_cubic` step has no route through `chainWidthE`
#guard ¬ (10 ^ 6 * 10 ^ 6 ≤ chainWidthE (10 ^ 6) (2 * 10 ^ 6) 2 2 1)

-- the capacity arithmetic of the round, on the two-round chain's data:
-- the raw assembly bound `n · (2b² + b)` at round `i` sits inside
-- `n · budget (i+1)`, which the width holds
#guard 5 * (2 * budget 1 1 1 * budget 1 1 1 + budget 1 1 1) ≤ 5 * budget 1 1 2
#guard 5 * budget 1 1 2 < chainWidthE 5 8 1 1 2

end Falsification

end Lax3Proofs.TgtCoupling
