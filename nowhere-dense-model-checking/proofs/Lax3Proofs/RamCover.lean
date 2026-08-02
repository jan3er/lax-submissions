import Lax3Proofs.CoverConstruction
import Lax3Proofs.RamBfs
import Lax3Proofs.Refine.BfsBridge

/-!
The **cover pass** of Grohe–Kreutzer–Siebertz §6, as a word-RAM program
with its correctness — and, before it, the one lemma that makes it a
program at all.

### The lemma

`CoverConstruction` builds the neighborhood cover of an ordering out of
the *fibres of weak reachability*: the cluster of a vertex `u` is the
set of vertices from which `u` is weakly `2r`-reachable, that is, the
set of `w` carrying a walk `w → u` of length at most `2r` on whose
support `u` is `π`-minimal. That is a definition, not an algorithm: the
minimality quantifies over the support of a walk, which no search
looks at.

The lemma that turns it into one is

    v ∈ wreach A π ρ w   ↔   WithinDist (deleteVerts A {u | π u < π v}) ρ v w

— `mem_wreach_iff_withinDist_pred`. The two sides are the same
condition read in the two directions. "Every vertex `y` on the walk has
`π v ≤ π y`" and "the walk never meets `{u | π u < π v}`" are literally
each other's contrapositives, and a walk that avoids an isolated set
survives isolation, while a walk of an isolated graph *starting* at a
surviving vertex never meets the isolated set at all — the empty walk
included, since `v` is not a predecessor of itself. So the fibre over
`v` **is a ball**: the ball the search of `Lax3Proofs.RamBfs` computes
when the mask kills exactly the vertices before `v`.

Everything else about the pass follows from arranging for the mask to
say that, which the program does by walking the centres in the
ordering's own order and killing each one after it is done.

### The program

`coverCom r` takes the block structure of `G`, an ambient mask, and the
order array `ord` — `ord c` is the vertex at position `c` — and for
each position in turn: searches to depth `2r` from `ord c` in the
current mask, scans the vertices once, emitting into a compressed-row
cluster arena everything the search put within `2r` and recording `c`
as the assignment of everything it put within `r` that nothing has
claimed yet, and then kills `ord c`.

Two radii, one distance array. The wider test is the cluster; the
narrower one is the *catch*, and the assignment records **first**
catches. That ordering is the algorithm. A centre that catches `w` at
radius `r` lies in the `r`-ball of `w` — by the lemma again, at radius
`r` — so the first catcher is the `π`-minimum of the ball among
catchers; and the `π`-minimum of the whole ball is itself a catcher,
because cutting the connecting walk anywhere keeps the cut point in the
ball, where that minimum is minimal. The two minima therefore agree,
and the covering argument of Lemma 6.9 applies to the vertex the
program wrote down. Recording first catches at radius `2r` instead
would be *wrong*, and cheaply so: a centre within `2r` of `w` need not
be within `r` of it, and then `w`'s ball need not be in its cluster.

### What a driver supplies, and what it gets

In: `off`/`tgt`, a `RamBfs.CsrGraph` block structure for `G`; `alv`,
the ambient mask, whose arena `RamBfs.masked G A₀` is what the whole
specification is about; `ord`, the order array of an ordering `π`, tied
to it by `OrdersBy` — one equation, `ord (π v) = v`, which
`ordersBy_rankPerm` produces from `RamElim`'s rank array and its
inverse; `dist`, `q`, `asg` of length `n`, `xoff` of length `n + 1` and
`xmem` of length `n²`. The radius is a program parameter, not an input.
The pass *writes into the mask*, so a caller that still wants the arena
keeps a copy.

Out: `xoff`/`xmem`, the clusters in compressed-row form, block `c`
holding exactly the fibre of the centre at position `c`; `asg`, sending
each vertex to a *position* whose cluster contains that vertex's whole
`r`-ball; and `xp`, the length used. `CoverPost` is those facts;
`isNeighborhoodCover_of_out` assembles them, plus the ordering's own
weak-reachability bound — which a density argument supplies and no
program computes — into `Lax3.NeighborhoodCovers.IsNeighborhoodCover`.

### What is proved

The lemma, the covering argument, and the whole of the pass's loop:
`CoverInv` is the invariant, `CoverInv.init` starts it, `CoverInv.step`
is one turn — stated against the search's distance array, whose
hypothesis is the search specification's threshold postcondition
verbatim — and `CoverInv.out` reads `CoverOut` off the state the loop
exits in. `cover_spec` assembles the fill, the two commands that open
the cluster arena, and the loop rule, and is proved from a single named
obligation: `Implements`, the Hoare triple for *one turn* of the loop,
`centreStep r`. What that obligation still owes is symbolic execution
— the source load, the search, the emission scan and the kill — and
nothing mathematical. The program is exhibited, compiled and run: the
worked example checks its three answers on a five-vertex graph, at four
settings of the mask and the radius, against the hand computation.

### Ledger — the tower search underneath (rebase P1)

The search the pass embeds is no longer `RamBfs.bfsCom` but the
refinement tower's synthesized queue BFS, through
`Lax3Proofs.Refine.BfsBridge.bfsQCom` (bridges P1/B-a … P1/B-c are
recorded in that file). Two entries belong here.

* **P1/B-d — the `q` word clause.** `CoverState` and `cover_spec`'s
  precondition gain `∀ v ∈ σ.arrs "q", v < B`. The tower export's
  `Ir.StateBound` is state-global, so it asks the *entering* cells of
  both scratch arrays to be words, where the hand-walked baseline
  bounded only what its run evaluated. The clause is free at every
  caller: `RamDriver.LevelMem` has carried it all along, beside the
  `dist` clause the pass already required for its own emission scan.

* **P1/B-e — the cost surface does not move.** `centreCost` and
  `coverCost` are unchanged. The tower search costs `56n + 40ns + 33`
  against the baseline's `51n + 44ns + 30`, plus `32` for the setup
  block, and the per-centre budget `100n + 50ns + 100` — deliberately
  generous, the shape being what the campaign spends against — absorbs
  the difference with room to spare (`90n + 40ns + 84` all told). So
  nothing above `CoverImplements` sees a new constant; the sharp cost
  is `bfsQK`'s and enters the recurrence at P4.

The worked example is the differential test of the swap: the four
`#guard`ed answers are unchanged, cell for cell, and only the cycle
counts move (5636→5611, 4316→4554, 4257→3833, 5894→6201). A search
that decided a different arena, or the threshold in the other
direction, would show up there before any proof was attempted.
-/

namespace Lax3Proofs.RamCover

open Lax3.ColoredGraphs Lax3.NeighborhoodCovers
open Lax12.ColoringNumbers Lax12.UniformQuasiWideness
open Lax3Proofs.WalkDistance Lax3Proofs.CoverConstruction
open Lax3Proofs.RamBfs (masked masked_def)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n : ℕ} {A : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {ρ r : ℕ}

/-! ### The predecessor set -/

/-- The vertices the ordering puts strictly before `v`. -/
def pred (π : Equiv.Perm (Fin n)) (v : Fin n) : Set (Fin n) := {u | π u < π v}

theorem mem_pred {u v : Fin n} : u ∈ pred π v ↔ π u < π v := Iff.rfl

theorem notMem_pred_self (π : Equiv.Perm (Fin n)) (v : Fin n) : v ∉ pred π v :=
  fun h => lt_irrefl _ (mem_pred.1 h)

/-! ### Walks in an isolated graph -/

/-- A walk of an isolated graph whose first vertex survives isolation
never meets the isolated set: both ends of every surviving edge are
outside it, so the containment propagates along the walk. -/
theorem support_notMem_of_walk {V : Type*} {B : SimpleGraph V} {S : Set V} {u v : V}
    (p : (deleteVerts B S).Walk u v) (hu : u ∉ S) : ∀ y ∈ p.support, y ∉ S := by
  revert hu
  induction p with
  | nil =>
      intro hu y hy
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
      exact hy ▸ hu
  | @cons a b c hab p ih =>
      intro hu y hy
      rcases List.mem_cons.1 (by simpa using hy) with rfl | hy'
      · exact hu
      · exact ih hab.2.2 y hy'

/-- A walk of an isolated graph is a walk of the graph, of the same
length and on the same vertices. -/
theorem exists_walk_of_deleteVerts {V : Type*} {B : SimpleGraph V} {S : Set V} {u v : V}
    (p : (deleteVerts B S).Walk u v) :
    ∃ q : B.Walk u v, q.length = p.length ∧ q.support = p.support := by
  induction p with
  | nil => exact ⟨.nil, rfl, rfl⟩
  | @cons a b c hab p ih =>
      obtain ⟨q, hq, hs⟩ := ih
      exact ⟨.cons hab.1 q, by simp [hq], by simp [hs]⟩

/-! ### The bridge -/

/-- **The fibre bridge.** The vertex `v` is weakly `ρ`-reachable from
`w` exactly when `w` lies in the `ρ`-ball of `v` in the graph with
everything the ordering puts before `v` isolated.

# Proof strategy

Both directions are the same observation, read in the two directions:
*the support of a walk avoids the predecessors of `v`* and *`v` is
`π`-minimal on that support* are the same condition, since `π u ≤ π y`
is the negation of `π y < π u`. Left to right, the walk `w → v` whose
support `v` is minimal on therefore survives the isolation, and
reverses. Right to left, a walk of the isolated graph *starting* at `v`
— which is not a predecessor of itself, so the nil walk is covered too
— never meets the isolated set at all, so it is a walk of the original
graph on the same vertices, and reverses into a reachability walk. -/
theorem mem_wreach_iff_withinDist_pred (A : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (ρ : ℕ) (v w : Fin n) :
    v ∈ wreach A π ρ w ↔ WithinDist (deleteVerts A (pred π v)) ρ v w := by
  constructor
  · intro h
    obtain ⟨p, hp, hmin⟩ := mem_wreach_iff.mp h
    obtain ⟨q, hq⟩ := exists_walk_deleteVerts p fun x hx => not_lt.2 (hmin x hx)
    exact withinDist_symm ⟨q, hq ▸ hp⟩
  · rintro ⟨p, hp⟩
    obtain ⟨q, hq, hs⟩ := exists_walk_of_deleteVerts p
    have hall : ∀ y ∈ q.support, y ∉ pred π v := by
      rw [hs]; exact support_notMem_of_walk p (notMem_pred_self π v)
    refine mem_wreach_iff.mpr ⟨q.reverse, by rw [SimpleGraph.Walk.length_reverse, hq]; exact hp,
      fun y hy => not_lt.1 (hall y ?_)⟩
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hy
    exact hy

/-- The fibre of weak `ρ`-reachability over `v` *is* a ball: the one
the search of `Lax3Proofs.RamBfs` computes when the mask kills exactly
the predecessors of `v`. -/
theorem wreach_fibre_eq_ball (A : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (ρ : ℕ) (v : Fin n) :
    {w | v ∈ wreach A π ρ w} = ball (deleteVerts A (pred π v)) ρ v :=
  Set.ext fun w => mem_wreach_iff_withinDist_pred A π ρ v w

/-! ### Isolating twice -/

/-- Two isolations are one: an edge survives both exactly when neither
of its ends is killed by either. -/
theorem deleteVerts_deleteVerts {V : Type*} (B : SimpleGraph V) (S S' : Set V) :
    deleteVerts (deleteVerts B S) S' = deleteVerts B (S ∪ S') := by
  ext u v
  simp only [Lax3Proofs.SplitterBasics.deleteVerts_adj, Set.mem_union]
  tauto

/-! ### The covering argument -/

/-- Every vertex on a walk of length at most `ρ` is within distance `ρ`
of both endpoints: cutting the walk at that vertex splits its length. -/
private theorem withinDist_of_mem_support {V : Type*} {B : SimpleGraph V} {a b : V}
    {ρ : ℕ} (p : B.Walk a b) (hp : p.length ≤ ρ) {y : V} (hy : y ∈ p.support) :
    WithinDist B ρ a y ∧ WithinDist B ρ y b := by
  classical
  have hlen := congrArg SimpleGraph.Walk.length (p.take_spec hy)
  rw [SimpleGraph.Walk.length_append] at hlen
  exact ⟨⟨p.takeUntil y hy, by omega⟩, ⟨p.dropUntil y hy, by omega⟩⟩

/-- A vertex is weakly reachable from itself, at every radius: the nil
walk has one vertex on it and that vertex is the endpoint. -/
theorem self_mem_wreach (A : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (ρ : ℕ)
    (w : Fin n) : w ∈ wreach A π ρ w :=
  mem_wreach_iff.mpr ⟨.nil, by simp, by simp⟩

/-- A weakly `ρ`-reachable vertex lies in the `ρ`-ball: the minimality
clause is dropped. -/
theorem mem_ball_of_mem_wreach {v w : Fin n} (h : v ∈ wreach A π ρ w) : v ∈ ball A ρ w := by
  obtain ⟨p, hp, -⟩ := mem_wreach_iff.mp h
  exact mem_ball.mpr ⟨p, hp⟩

/-- **A ball minimum is weakly reachable.** Cutting the connecting walk
at any of its vertices puts that vertex in the ball, where the minimum
is minimal — so the walk witnessing membership already witnesses weak
reachability. -/
theorem mem_wreach_of_min {u w : Fin n} (hu : u ∈ ball A ρ w)
    (hmin : ∀ y ∈ ball A ρ w, π u ≤ π y) : u ∈ wreach A π ρ w := by
  obtain ⟨p, hp⟩ := mem_ball.mp hu
  exact mem_wreach_iff.mpr ⟨p, hp, fun y hy =>
    hmin y (mem_ball.mpr (withinDist_of_mem_support p hp hy).1)⟩

/-- **The covering step** (the one argument of Lemma 6.9 of
Grohe–Kreutzer–Siebertz). If `u` is a `π`-minimum of the `ρ`-ball of
`w`, the whole ball lies in the fibre of `u` at radius `2ρ`: any `z` in
the ball reaches `u` by going back to `w` and out again, a walk of
length at most `2ρ` whose support stays inside the ball. -/
theorem ball_subset_wreach_fibre {u w : Fin n} (hu : u ∈ ball A ρ w)
    (hmin : ∀ y ∈ ball A ρ w, π u ≤ π y) :
    ball A ρ w ⊆ {z | u ∈ wreach A π (2 * ρ) z} := by
  intro z hz
  obtain ⟨p, hp⟩ := mem_ball.mp hz
  obtain ⟨q, hq⟩ := mem_ball.mp hu
  have hpr : p.reverse.length ≤ ρ := by rw [SimpleGraph.Walk.length_reverse]; exact hp
  refine mem_wreach_iff.mpr ⟨p.reverse.append q, ?_, fun y hy => ?_⟩
  · rw [SimpleGraph.Walk.length_append]; omega
  · refine hmin y (mem_ball.mpr ?_)
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hy with hy | hy
    · exact withinDist_symm (withinDist_of_mem_support p.reverse hpr hy).2
    · exact (withinDist_of_mem_support q hq hy).1

/-- **The minimal catcher is a ball minimum.** The program never sees a
ball: it sees which centres catch a vertex, and takes the first. This
says that the two minima agree — a `π`-minimum of the ball is itself a
catcher, so a minimal catcher is at least as small, and it is in the
ball, so it is at least as large. -/
theorem min_ball_of_min_wreach {u w : Fin n}
    (hmin : ∀ u' ∈ wreach A π ρ w, π u ≤ π u') : ∀ y ∈ ball A ρ w, π u ≤ π y := by
  classical
  obtain ⟨z, hzF, hzmin⟩ :=
    Finset.exists_min_image (Set.toFinite (ball A ρ w)).toFinset (fun x => π x)
      ⟨w, (Set.Finite.mem_toFinset _).mpr (mem_ball_self A ρ w)⟩
  have hzmin' : ∀ y ∈ ball A ρ w, π z ≤ π y :=
    fun y hy => hzmin y ((Set.Finite.mem_toFinset _).mpr hy)
  have hz : z ∈ ball A ρ w := (Set.Finite.mem_toFinset _).mp hzF
  have huz := hmin z (mem_wreach_of_min hz hzmin')
  exact fun y hy => le_trans huz (hzmin' y hy)

/-- **What the program's assignment is worth.** A minimal catcher of
`w` has the whole `ρ`-ball of `w` in its fibre — which is the covering
condition of a neighborhood cover, with the cluster named by data the
program has. -/
theorem ball_subset_fibre_of_min_wreach {u w : Fin n} (hu : u ∈ wreach A π ρ w)
    (hmin : ∀ u' ∈ wreach A π ρ w, π u ≤ π u') :
    ball A ρ w ⊆ {z | u ∈ wreach A π (2 * ρ) z} :=
  ball_subset_wreach_fibre (mem_ball_of_mem_wreach hu) (min_ball_of_min_wreach hmin)

/-! ### The ordering, as the program has it

The pass never looks at an ordering: it looks at the array the
elimination engine leaves, and walks it. Two numbers name a vertex —
its *position* `rk` in the ordering, which is the engine's rank, and
the vertex itself — and the order array `ord` is the map back from the
first to the second. That one equation is everything the program needs
of the ordering, and everything the proof needs of the array. -/

/-- The position the ordering gives a vertex number, with `n` off the
carrier so that the notion is total on numbers. -/
def rk (n : ℕ) (π : Equiv.Perm (Fin n)) (u : ℕ) : ℕ :=
  if h : u < n then ((π ⟨u, h⟩ : Fin n) : ℕ) else n

theorem rk_of_lt {u : ℕ} (hu : u < n) : rk n π u = ((π ⟨u, hu⟩ : Fin n) : ℕ) := dif_pos hu

theorem rk_fin (u : Fin n) : rk n π (u : ℕ) = ((π u : Fin n) : ℕ) := rk_of_lt u.isLt

theorem rk_lt {u : ℕ} (hu : u < n) : rk n π u < n := by
  rw [rk_of_lt hu]; exact Fin.isLt _

theorem rk_inj {u v : ℕ} (hu : u < n) (hv : v < n) (h : rk n π u = rk n π v) : u = v := by
  rw [rk_of_lt hu, rk_of_lt hv] at h
  exact congrArg Fin.val (π.injective (Fin.ext h))

/-- `ord` orders by `π`: it sends the position a vertex occupies back
to the vertex. -/
def OrdersBy (n : ℕ) (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ) : Prop :=
  ∀ v : Fin n, ord ((π v : Fin n) : ℕ) = (v : ℕ)

namespace OrdersBy

variable {ord : ℕ → ℕ}

/-- Read the other way, the order array is the ordering's inverse. -/
theorem eq_symm (h : OrdersBy n π ord) {c : ℕ} (hc : c < n) :
    ord c = ((π.symm ⟨c, hc⟩ : Fin n) : ℕ) := by
  conv_lhs => rw [show c = ((π (π.symm ⟨c, hc⟩) : Fin n) : ℕ) by rw [Equiv.apply_symm_apply]]
  exact h _

/-- Every position names a vertex. -/
theorem lt (h : OrdersBy n π ord) {c : ℕ} (hc : c < n) : ord c < n := by
  rw [h.eq_symm hc]; exact Fin.isLt _

/-- And the vertex it names sits at that position. -/
theorem rk_ord (h : OrdersBy n π ord) {c : ℕ} (hc : c < n) : rk n π (ord c) = c := by
  rw [rk_of_lt (h.lt hc),
    show (⟨ord c, h.lt hc⟩ : Fin n) = π.symm ⟨c, hc⟩ from Fin.ext (h.eq_symm hc),
    Equiv.apply_symm_apply]

/-- The two maps are inverse on the carrier. -/
theorem ord_rk (h : OrdersBy n π ord) {u : ℕ} (hu : u < n) : ord (rk n π u) = u := by
  rw [rk_of_lt hu]; exact h _

end OrdersBy

/-- **What a rank array is worth.** An injective rank onto the
positions, with its inverse, is an ordering — this is the form the
elimination engine's output takes, and the one line a driver writes to
hand it to this pass. -/
def rankPerm (n : ℕ) (R ordv : ℕ → ℕ) (hR : ∀ v < n, R v < n) (hord : ∀ c < n, ordv c < n)
    (hRo : ∀ c < n, R (ordv c) = c) (hoR : ∀ v < n, ordv (R v) = v) : Equiv.Perm (Fin n) where
  toFun v := ⟨R (v : ℕ), hR _ v.isLt⟩
  invFun c := ⟨ordv (c : ℕ), hord _ c.isLt⟩
  left_inv v := Fin.ext (hoR _ v.isLt)
  right_inv c := Fin.ext (hRo _ c.isLt)

theorem ordersBy_rankPerm (n : ℕ) (R ordv : ℕ → ℕ) (hR : ∀ v < n, R v < n)
    (hord : ∀ c < n, ordv c < n) (hRo : ∀ c < n, R (ordv c) = c)
    (hoR : ∀ v < n, ordv (R v) = v) :
    OrdersBy n (rankPerm n R ordv hR hord hRo hoR) ordv :=
  fun v => hoR _ v.isLt

/-! ### Clusters and catches, on vertex numbers

Everything the program handles is a number, so the two notions the
specification speaks are restated on `ℕ` carrying their own range
conditions — `RamBfs`'s `MAdj`/`WD` pattern, one level up. -/

/-- The vertex numbered `w` is in the cluster of the centre numbered
`a`: the centre is weakly `2r`-reachable from it. -/
def InCluster (A : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r a w : ℕ) : Prop :=
  ∃ (ha : a < n) (hw : w < n), (⟨a, ha⟩ : Fin n) ∈ wreach A π (2 * r) ⟨w, hw⟩

/-- The centre numbered `a` **catches** the vertex numbered `w`: the
centre is weakly `r`-reachable from it, at half the cluster radius.
This is the relation the assignment array records, and the reason it
records the right thing. -/
def Catches (A : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r a w : ℕ) : Prop :=
  ∃ (ha : a < n) (hw : w < n), (⟨a, ha⟩ : Fin n) ∈ wreach A π r ⟨w, hw⟩

theorem inCluster_iff {r a w : ℕ} (ha : a < n) (hw : w < n) :
    InCluster A π r a w ↔ (⟨a, ha⟩ : Fin n) ∈ wreach A π (2 * r) ⟨w, hw⟩ :=
  ⟨fun h => h.2.2, fun h => ⟨ha, hw, h⟩⟩

theorem catches_iff {r a w : ℕ} (ha : a < n) (hw : w < n) :
    Catches A π r a w ↔ (⟨a, ha⟩ : Fin n) ∈ wreach A π r ⟨w, hw⟩ :=
  ⟨fun h => h.2.2, fun h => ⟨ha, hw, h⟩⟩

theorem InCluster.lt_centre {r a w : ℕ} (h : InCluster A π r a w) : a < n := h.1

theorem InCluster.lt_mem {r a w : ℕ} (h : InCluster A π r a w) : w < n := h.2.1

theorem Catches.lt_centre {r a w : ℕ} (h : Catches A π r a w) : a < n := h.1

theorem Catches.lt_mem {r a w : ℕ} (h : Catches A π r a w) : w < n := h.2.1

/-- **Every vertex catches itself**, which is why the pass leaves no
vertex unassigned. -/
theorem catches_self (A : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ) {w : ℕ}
    (hw : w < n) : Catches A π r w w :=
  ⟨hw, hw, self_mem_wreach A π r _⟩

/-- A cluster lies in the `2r`-ball of its centre: the radius condition
of a neighborhood cover, with the minimality clause dropped. -/
theorem inCluster_subset_ball (A : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) {r a : ℕ}
    (ha : a < n) : {z : Fin n | InCluster A π r a (z : ℕ)} ⊆ ball A (2 * r) ⟨a, ha⟩ :=
  fun z hz => mem_ball.mpr (withinDist_symm
    (mem_ball.mp (mem_ball_of_mem_wreach ((inCluster_iff ha z.isLt).mp (by simpa using hz)))))

/-! ### The arena of one turn

The pass runs the search in the ambient arena with the centres already
processed killed as well. Killing twice is killing once, so that arena
is the ambient one with the predecessors of the current centre
isolated — the graph the fibre bridge is stated over. -/

variable {G : SimpleGraph (Fin n)} {M A₀ ord Xoff Xmem asg : ℕ → ℕ} {c xp m : ℕ}

/-- **The arena of one turn of the pass.** -/
theorem masked_step (h : OrdersBy n π ord) (hc : c < n)
    (hmask : ∀ u < n, (M u = 0 ↔ (A₀ u = 0 ∨ rk n π u < c))) :
    masked G M = deleteVerts (masked G A₀) (pred π ⟨ord c, h.lt hc⟩) := by
  have hrc : ((π (⟨ord c, h.lt hc⟩ : Fin n) : Fin n) : ℕ) = c := by
    rw [← rk_of_lt (h.lt hc)]; exact h.rk_ord hc
  rw [masked_def G M, masked_def G A₀, deleteVerts_deleteVerts]
  refine congrArg (deleteVerts G) (Set.ext fun u => ?_)
  simp only [Set.mem_setOf_eq, Set.mem_union, mem_pred, Fin.lt_def, hrc]
  rw [hmask (u : ℕ) u.isLt, ← rk_fin u]

/-! ### The invariant of the pass

One structure, carrying what the four output arrays hold after the
first `c` centres have been processed, plus what the mask says. Its two
assignment clauses are the ones worth naming: a *recorded* assignment
is not merely some catcher of its vertex but the **minimal** one, and
an *unrecorded* one certifies that no catcher has been passed yet.
Together they say that the pass records first catches, and it is that
minimality — not the catching — that the covering argument consumes. -/

/-- What holds of the pass's arrays and its counter at the top of every
turn. -/
structure CoverInv {n : ℕ} (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ) (r c xp : ℕ) (Xoff Xmem asg M : ℕ → ℕ) : Prop where
  /-- The centres processed so far are an initial segment of the order. -/
  pos_le : c ≤ n
  /-- The cluster arena starts at its start. -/
  zero : Xoff 0 = 0
  /-- Its blocks are laid out in order. -/
  mono : ∀ c' < c, Xoff c' ≤ Xoff (c' + 1)
  /-- The write pointer stands at the end of the last block. -/
  ptr : Xoff c = xp
  /-- No centre has written more than the whole vertex set. -/
  ptr_le : xp ≤ c * n
  /-- Everything written into the arena is a vertex. -/
  mem_lt : ∀ p < xp, Xmem p < n
  /-- **Each block is a fibre**: the block of the centre at position
  `c'` lists exactly the vertices from which that centre is weakly
  `2r`-reachable. -/
  block : ∀ c' < c, ∀ w, (∃ p, Xoff c' ≤ p ∧ p < Xoff (c' + 1) ∧ Xmem p = w) ↔
    InCluster (masked G A₀) π r (ord c') w
  /-- **And it lists each of them once.** The emission scan appends the
  carrier in increasing order, so a block holds no vertex twice — which
  is what turns "the blocks cover the arena" into "the blocks *count*
  it", and so is what the cover-degree mass bound of the cost half
  stands on (rebase B6/D1). -/
  block_inj : ∀ c' < c, ∀ p q, Xoff c' ≤ p → p < Xoff (c' + 1) → Xoff c' ≤ q →
    q < Xoff (c' + 1) → Xmem p = Xmem q → p = q
  /-- The mask kills the ambient dead vertices and the centres already
  processed, and nothing else. -/
  mask : ∀ u < n, (M u = 0 ↔ (A₀ u = 0 ∨ rk n π u < c))
  /-- The assignment array holds a position or the sentinel `n`. -/
  asg_le : ∀ w < n, asg w ≤ n
  /-- **A recorded assignment is the minimal catcher**, and it has been
  passed. -/
  asg_set : ∀ w < n, asg w < n → asg w < c ∧ Catches (masked G A₀) π r (ord (asg w)) w ∧
    ∀ a, Catches (masked G A₀) π r a w → asg w ≤ rk n π a
  /-- And an unrecorded one has no catcher among the centres passed. -/
  asg_unset : ∀ w < n, asg w = n → ∀ a, Catches (masked G A₀) π r a w → c ≤ rk n π a

namespace CoverInv

/-- The blocks are laid out in order all the way up. -/
theorem mono' (hI : CoverInv G A₀ π ord r c xp Xoff Xmem asg M) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ c) : Xoff i ≤ Xoff j := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact le_rfl
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact le_trans (ih (by omega) (by omega)) (hI.mono j (by omega))
      · have : i = j + 1 := by omega
        subst this; exact le_rfl

/-- **The state the pass starts in**: nothing emitted, nothing killed
beyond the ambient mask, nothing assigned. -/
theorem init (hA : ∀ u < n, M u = A₀ u) (hoff : Xoff 0 = 0) (hasg : ∀ w < n, asg w = n) :
    CoverInv G A₀ π ord r 0 0 Xoff Xmem asg M where
  pos_le := Nat.zero_le _
  zero := hoff
  mono := fun _ h => absurd h (by omega)
  ptr := hoff
  ptr_le := by omega
  mem_lt := fun _ h => absurd h (by omega)
  block := fun _ h => absurd h (by omega)
  block_inj := fun _ h => absurd h (by omega)
  mask := fun u hu => by rw [hA u hu]; constructor
                         · exact fun h => Or.inl h
                         · rintro (h | h); · exact h
                           · omega
  asg_le := fun w hw => le_of_eq (hasg w hw)
  asg_set := fun w hw h => absurd (hasg w hw) (by omega)
  asg_unset := fun _ _ _ _ _ => Nat.zero_le _

end CoverInv

/-! ### One turn

The step is stated against what the turn *did* rather than against the
program that did it: the search's distance array, and the four arrays
as the emission, the assignment and the kill leave them. Nothing here
knows about the machine, and the walk below owes exactly these
hypotheses. -/

/-- **One centre.** The search from the centre at position `c` in the
current mask, the block it emits, the assignment it records for the
vertices it is the first to catch, and its own death, carry the
invariant one position on.

# Proof strategy

The whole turn rests on two readings of the one distance array, at the
two radii the pass uses. By `masked_step` the search ran in the ambient
arena with the predecessors of the centre isolated, so by the fibre
bridge `D w ≤ 2r` says exactly that the centre is weakly
`2r`-reachable from `w` — the emitted block is the fibre — and
`D w ≤ r` says exactly that the centre *catches* `w`.

The block clauses are then bookkeeping: the earlier blocks lie below
the old write pointer and are untouched, and the new one is the range
the emission filled. The mask clause is the rank of the centre being
`c`, so that "killed" grows from `rk < c` to `rk < c + 1`. And the two
assignment clauses swap roles exactly once per vertex: a vertex with no
catcher passed either finds one now, in which case the centre's rank
`c` is minimal among all catchers because none below `c` catches it, or
does not, in which case the only new candidate rank — `c` itself, since
ranks are injective — has just been ruled out. -/
theorem CoverInv.step (hord : OrdersBy n π ord)
    (hI : CoverInv G A₀ π ord r c xp Xoff Xmem asg M) (hc : c < n)
    {D Xoff' Xmem' asg' M' : ℕ → ℕ} {xp' : ℕ}
    (hD : ∀ (w : Fin n) (k : ℕ), k ≤ 2 * r →
      (D (w : ℕ) ≤ k ↔ WithinDist (masked G M) k ⟨ord c, hord.lt hc⟩ w))
    (hoff : ∀ c' ≤ c, Xoff' c' = Xoff c') (hoff' : Xoff' (c + 1) = xp')
    (hkeep : ∀ p < xp, Xmem' p = Xmem p)
    (hblock : ∀ w, (∃ p, xp ≤ p ∧ p < xp' ∧ Xmem' p = w) ↔ (w < n ∧ D w ≤ 2 * r))
    (hxp : xp ≤ xp') (hxpn : xp' ≤ xp + n)
    (hbinj : ∀ p q, xp ≤ p → p < xp' → xp ≤ q → q < xp' → Xmem' p = Xmem' q → p = q)
    (hasg : ∀ w < n, asg' w = if asg w < n then asg w else if D w ≤ r then c else n)
    (hM : ∀ u < n, M' u = if u = ord c then 0 else M u) :
    CoverInv G A₀ π ord r (c + 1) xp' Xoff' Xmem' asg' M' := by
  have hv : ord c < n := hord.lt hc
  have hrkv : rk n π (ord c) = c := hord.rk_ord hc
  have hmg : masked G M = deleteVerts (masked G A₀) (pred π ⟨ord c, hv⟩) :=
    masked_step hord hc hI.mask
  -- the two readings of the distance array
  have hclus : ∀ (w : ℕ) (hw : w < n), D w ≤ 2 * r ↔ InCluster (masked G A₀) π r (ord c) w := by
    intro w hw
    rw [hD ⟨w, hw⟩ (2 * r) le_rfl, hmg, ← mem_wreach_iff_withinDist_pred, inCluster_iff hv hw]
  have hcatch : ∀ (w : ℕ) (hw : w < n), D w ≤ r ↔ Catches (masked G A₀) π r (ord c) w := by
    intro w hw
    rw [hD ⟨w, hw⟩ r (by omega), hmg, ← mem_wreach_iff_withinDist_pred, catches_iff hv hw]
  have hoffc : Xoff' c = xp := by rw [hoff c le_rfl, hI.ptr]
  refine ⟨by omega, ?_, ?_, hoff', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hoff 0 (by omega)]; exact hI.zero
  · intro c' hc'
    rcases Nat.lt_or_ge c' c with hlt | hge
    · rw [hoff c' (by omega), hoff (c' + 1) (by omega)]; exact hI.mono c' hlt
    · have : c' = c := by omega
      subst this; rw [hoffc, hoff']; exact hxp
  · have h₁ := hI.ptr_le
    have h₂ : (c + 1) * n = c * n + n := by ring
    omega
  · intro p hp
    rcases Nat.lt_or_ge p xp with hlt | hge
    · rw [hkeep p hlt]; exact hI.mem_lt p hlt
    · exact ((hblock (Xmem' p)).mp ⟨p, hge, hp, rfl⟩).1
  · intro c' hc' w
    rcases Nat.lt_or_ge c' c with hlt | hge
    · have hbnd : ∀ p, p < Xoff (c' + 1) → p < xp := by
        intro p hp
        have h₁ := hI.mono' (i := c' + 1) (j := c) (by omega) le_rfl
        have h₂ := hI.ptr
        omega
      rw [← hI.block c' hlt w, hoff c' (by omega), hoff (c' + 1) (by omega)]
      exact ⟨fun ⟨p, h₁, h₂, h₃⟩ => ⟨p, h₁, h₂, by rw [← h₃, hkeep p (hbnd p h₂)]⟩,
        fun ⟨p, h₁, h₂, h₃⟩ => ⟨p, h₁, h₂, by rw [hkeep p (hbnd p h₂)]; exact h₃⟩⟩
    · have hce : c' = c := by omega
      subst hce
      rw [hoffc, hoff', hblock w]
      exact ⟨fun h => (hclus w h.1).mp h.2, fun h => ⟨h.lt_mem, (hclus w h.lt_mem).mpr h⟩⟩
  · -- the blocks list each vertex once: the earlier ones are untouched, the new
    -- one is what the emission scan just filled
    intro c' hc' p q hp₁ hp₂ hq₁ hq₂ he
    rcases Nat.lt_or_ge c' c with hlt | hge
    · have hbnd : ∀ p, p < Xoff (c' + 1) → p < xp := by
        intro p hp
        have h₁ := hI.mono' (i := c' + 1) (j := c) (by omega) le_rfl
        have h₂ := hI.ptr
        omega
      rw [hoff c' (by omega)] at hp₁ hq₁
      rw [hoff (c' + 1) (by omega)] at hp₂ hq₂
      refine hI.block_inj c' hlt p q hp₁ hp₂ hq₁ hq₂ ?_
      rw [← hkeep p (hbnd p hp₂), ← hkeep q (hbnd q hq₂)]
      exact he
    · have hce : c' = c := by omega
      subst hce
      rw [hoffc] at hp₁ hq₁
      rw [hoff'] at hp₂ hq₂
      exact hbinj p q hp₁ hp₂ hq₁ hq₂ he
  · intro u hu
    rw [hM u hu]
    by_cases hue : u = ord c
    · subst hue
      rw [if_pos rfl]
      exact ⟨fun _ => Or.inr (by omega), fun _ => rfl⟩
    · rw [if_neg hue, hI.mask u hu]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (by omega)
      · rintro (h | h)
        · exact Or.inl h
        · refine Or.inr ?_
          rcases Nat.lt_or_ge (rk n π u) c with h' | h'
          · exact h'
          · exact absurd (rk_inj (π := π) hu hv (by omega)) hue
  · intro w hw
    rw [hasg w hw]
    by_cases h : asg w < n
    · rw [if_pos h]; omega
    · rw [if_neg h]
      by_cases h' : D w ≤ r
      · rw [if_pos h']; omega
      · rw [if_neg h']
  · intro w hw hlt
    rw [hasg w hw] at hlt ⊢
    by_cases h : asg w < n
    · rw [if_pos h] at hlt ⊢
      obtain ⟨h₁, h₂, h₃⟩ := hI.asg_set w hw h
      exact ⟨by omega, h₂, h₃⟩
    · rw [if_neg h] at hlt ⊢
      have hwn : asg w = n := by have := hI.asg_le w hw; omega
      by_cases h' : D w ≤ r
      · rw [if_pos h'] at hlt ⊢
        exact ⟨by omega, (hcatch w hw).mp h', fun a ha => hI.asg_unset w hw hwn a ha⟩
      · rw [if_neg h'] at hlt; omega
  · intro w hw he a ha
    rw [hasg w hw] at he
    by_cases h : asg w < n
    · rw [if_pos h] at he; omega
    · rw [if_neg h] at he
      have hwn : asg w = n := by have := hI.asg_le w hw; omega
      have h' : ¬ D w ≤ r := by intro hd; rw [if_pos hd] at he; omega
      have hac := hI.asg_unset w hw hwn a ha
      rcases Nat.lt_or_ge c (rk n π a) with hlt | hge
      · omega
      · have hae : rk n π a = c := by omega
        have : a = ord c := rk_inj ha.lt_centre hv (by rw [hae, hrkv])
        exact absurd ((hcatch w hw).mpr (this ▸ ha)) h'

/-! ### What the pass leaves -/

/-- **The three answers.** The cluster arena, block by block; the
assignment array; and the one fact that makes the pair a neighborhood
cover — every `r`-ball is inside the cluster the assignment names. -/
structure CoverOut {n : ℕ} (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ) (r m : ℕ) (Xoff Xmem asg : ℕ → ℕ) : Prop where
  /-- The arena starts at its start. -/
  zero : Xoff 0 = 0
  /-- And ends where the pass says it ends. -/
  last : Xoff n = m
  /-- The blocks are laid out in order. -/
  mono : ∀ c < n, Xoff c ≤ Xoff (c + 1)
  /-- Everything in the arena is a vertex. -/
  mem_lt : ∀ p < m, Xmem p < n
  /-- **Each block is a fibre.** -/
  block : ∀ c < n, ∀ w, (∃ p, Xoff c ≤ p ∧ p < Xoff (c + 1) ∧ Xmem p = w) ↔
    InCluster (masked G A₀) π r (ord c) w
  /-- **And lists it once**: no block names a vertex twice, so the
  arena's length *counts* the fibres (rebase B6/D1). -/
  block_inj : ∀ c < n, ∀ p q, Xoff c ≤ p → p < Xoff (c + 1) → Xoff c ≤ q →
    q < Xoff (c + 1) → Xmem p = Xmem q → p = q
  /-- Every vertex has been assigned a centre position. -/
  asg_lt : ∀ w < n, asg w < n
  /-- **And the cluster of that centre holds the vertex's whole
  `r`-ball.** -/
  asg_cover : ∀ (w : ℕ) (hw : w < n), ball (masked G A₀) r ⟨w, hw⟩ ⊆
    {z : Fin n | InCluster (masked G A₀) π r (ord (asg w)) (z : ℕ)}

/-- **The exit reading.** Once every centre has been processed the
invariant is the answer. Totality of the assignment is the observation
that a vertex catches itself, so the sentinel cannot survive; and the
covering fact is the covering argument, applied to the minimal catcher
the invariant carries. -/
theorem CoverInv.out (hord : OrdersBy n π ord)
    (hI : CoverInv G A₀ π ord r n xp Xoff Xmem asg M) :
    CoverOut G A₀ π ord r xp Xoff Xmem asg := by
  have hlt : ∀ w < n, asg w < n := by
    intro w hw
    rcases lt_or_eq_of_le (hI.asg_le w hw) with h | h
    · exact h
    · exact absurd (hI.asg_unset w hw h w (catches_self _ _ _ hw)) (by
        have := rk_lt (π := π) hw; omega)
  refine ⟨hI.zero, hI.ptr, hI.mono, hI.mem_lt, hI.block, hI.block_inj, hlt, fun w hw => ?_⟩
  obtain ⟨-, hcat, hmin⟩ := hI.asg_set w hw (hlt w hw)
  have hu : ord (asg w) < n := hord.lt (hlt w hw)
  have hrku : rk n π (ord (asg w)) = asg w := hord.rk_ord (hlt w hw)
  refine subset_trans (ball_subset_fibre_of_min_wreach
    ((catches_iff hu hw).mp hcat) (fun u' hu' => ?_)) (fun z hz => ?_)
  · have : Catches (masked G A₀) π r ((u' : Fin n) : ℕ) w :=
      (catches_iff u'.isLt hw).mpr (by simpa using hu')
    have hle := hmin _ this
    rw [Fin.le_def, ← rk_of_lt hu, ← rk_fin u', hrku]
    exact hle
  · exact (inCluster_iff hu z.isLt).mpr (by simpa using hz)

/-- **The pass builds a neighborhood cover.** The two conditions the
program is responsible for come off `CoverOut` directly — the covering
one with the cluster named by the assignment array, not by an abstract
minimum — and the third, the degree, is the ordering's own weak
reachability bound, which a density argument supplies and no program
computes. -/
theorem isNeighborhoodCover_of_out (hord : OrdersBy n π ord)
    (h : CoverOut G A₀ π ord r m Xoff Xmem asg) {k : ℕ}
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ k) :
    IsNeighborhoodCover (masked G A₀) r
      (fun u : Fin n => {w : Fin n | u ∈ wreach (masked G A₀) π (2 * r) w}) k := by
  refine ⟨fun v => ⟨⟨ord (asg (v : ℕ)), hord.lt (h.asg_lt _ v.isLt)⟩, fun z hz => ?_⟩,
    fun u w hw => ?_, hk⟩
  · have := h.asg_cover (v : ℕ) v.isLt (by simpa using hz)
    exact (inCluster_iff (hord.lt (h.asg_lt _ v.isLt)) z.isLt).mp this
  · exact mem_ball.mpr (withinDist_symm (mem_ball.mp (mem_ball_of_mem_wreach hw)))

/-! ### The program

Six phases, of which one is a whole other program: the search of
`Lax3Proofs.RamBfs`, run once per centre in the mask the pass has
whittled down so far. Everything else is a flat pass.

The two radii the emission tests against are literals, as the search's
cap is: a radius in this submission comes from the formula and not from
the input, so `coverCom` is a family of programs, one per radius, and
nothing downstream passes a radius at run time. The *order* is input,
and it arrives as one array — `ord c` is the vertex the ordering puts
at position `c`. The rank array the elimination engine also produces is
not read at all; it enters only the proof, as the ordering `π`. -/

/-- Mark every vertex unassigned: the assignment array gets the
sentinel `n`, which is the one value that is not a position. -/
def initAsg : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.var "n")) (Fill.put "asg" "i" (.var "n")))

/-- One vertex of the emission scan, and the whole of what the pass
does with the search's answer. A vertex within `2r` of the centre goes
into the centre's block. A vertex within `r` of it — the sharper test,
made on the same distance — is *caught*, and if nothing has caught it
yet the centre's position is recorded as its assignment. The order of
the two tests is the algorithm: the assignment records **first**
catches, and it is that, not the catching, that the covering argument
needs. -/
def emitSlot (r : ℕ) : Com :=
  .seq (.assign "dz" (.get "dist" (.var "z")))
    (.seq (.ite (.lt (.var "dz") (.lit (2 * r + 1)))
            (.seq (.store "xmem" (.var "xp") (.var "z"))
              (.seq (.assign "xp" (.add (.var "xp") (.lit 1)))
                (.ite (.lt (.var "dz") (.lit (r + 1)))
                  (.ite (.lt (.get "asg" (.var "z")) (.var "n"))
                    .skip
                    (.store "asg" (.var "z") (.var "c")))
                  .skip)))
            .skip)
      (.assign "z" (.add (.var "z") (.lit 1))))

/-- The emission scan: every vertex of the arena, read off the one
distance array. -/
def emitLoop (r : ℕ) : Com :=
  .seq (.assign "z" (.lit 0)) (.while (.lt (.var "z") (.var "n")) (emitSlot r))

/-- One centre: search from it to depth `2r` in the current mask, emit
what the search found, and then **kill it**. Killing only the centre is
the whole reason the emitted block is a weak-reachability fibre: the
set of dead vertices grows by one at a time in the order of the
ordering, so the arena of the turn at position `c` isolates exactly the
vertices the ordering puts before the centre. -/
def centreStep (r : ℕ) : Com :=
  .seq (.assign "src" (.get "ord" (.var "c")))
    (.seq (Refine.BfsBridge.bfsQCom (2 * r))
      (.seq (emitLoop r)
        (.seq (.store "alv" (.var "src") (.lit 0))
          (.seq (.assign "c" (.add (.var "c") (.lit 1)))
            (.store "xoff" (.var "c") (.var "xp"))))))

/-- **The cover pass.** Clear the assignments, open the cluster arena,
and walk the centres in the order's own order. -/
def coverCom (r : ℕ) : Com :=
  .seq initAsg
    (.seq (.assign "xp" (.lit 0))
      (.seq (.store "xoff" (.lit 0) (.lit 0))
        (.seq (.assign "c" (.lit 0))
          (.while (.lt (.var "c") (.var "n")) (centreStep r)))))

/-! ### The specification

Four arrays in, three arrays out, and one scalar. The block structure
and the ambient mask are the arena; the order array is the ordering the
elimination engine computed, and the *rank* array it also computed is
not read at all — it enters only as the permutation `π` of the proof,
tied to the order array by `OrdersBy`.

The pass writes into the ambient mask, killing each centre as it goes,
so a caller that still wants the arena afterwards keeps its own copy.
That is the one destructive thing it does. -/

variable {ns : ℕ} {O T : ℕ → ℕ}

/-- **What the pass is handed.** -/
def CoverPre (n ns : ℕ) (O T A₀ ord : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧
  σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
  σ.arrs "alv" = arrOf n A₀ ∧ σ.arrs "ord" = arrOf n ord ∧
  (∃ g, σ.arrs "dist" = arrOf n g) ∧ (∃ g, σ.arrs "q" = arrOf n g) ∧
  (∃ g, σ.arrs "asg" = arrOf n g) ∧
  (∃ g, σ.arrs "xoff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "xmem" = arrOf (n * n) g)

/-- **The same surface with the target array widened** (rebase F-c-3):
the block structure's targets are materialized at a caller-chosen width
`nt`, the call's slot count `ns` being only a lower bound.
`RamElim.ElimPreW` is the precedent and the reason is the same one — a
caller that runs several passes on graphs it materializes itself
allocates `tgt` once and cannot re-allocate it, an IMP+ run being unable
to change the length of an array. Everything this pass *addresses* is
still below `O n = ns`: the search scans rows, and a row ends at an
offset.

The slot count is carried as a parameter and constrains no clause here
— it is `ImplementsW` that asks `ns ≤ nt` — so that a caller reads the
two widths of one surface off one parameter list. `CoverPre` is the
case `nt = ns`, clause for clause. -/
def CoverPreW (n _ns nt : ℕ) (O T A₀ ord : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧
  σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
  σ.arrs "alv" = arrOf n A₀ ∧ σ.arrs "ord" = arrOf n ord ∧
  (∃ g, σ.arrs "dist" = arrOf n g) ∧ (∃ g, σ.arrs "q" = arrOf n g) ∧
  (∃ g, σ.arrs "asg" = arrOf n g) ∧
  (∃ g, σ.arrs "xoff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "xmem" = arrOf (n * n) g)

/-- The pinned surface is the widened one at `nt = ns` — on the nose,
which is what makes the widening a hypothesis generalization and not a
second pass. -/
theorem coverPreW_of_coverPre {σ : Env} (h : CoverPre n ns O T A₀ ord σ) :
    CoverPreW n ns ns O T A₀ ord σ := h

/-- And back. -/
theorem coverPre_of_coverPreW {σ : Env} (h : CoverPreW n ns ns O T A₀ ord σ) :
    CoverPre n ns O T A₀ ord σ := h

/-- **The state the loop runs against**: the invariant of the pass,
carried by the four arrays it writes, with the arrays it only reads
frozen and the two scratch arrays of the search at their lengths. The
counter and the write pointer are read off the environment, so that the
loop rule owns them.

**The three word clauses.** The bounded semantics has no value for a
cell at or above the word bound, and the pass reads three arrays whose
cells nothing else here pins: the mask `alv`, whose first read is the
search's own `.get "alv" (.var "src")` — `CoverInv.mask` says only which
of its cells are *zero* — the distance array `dist`, read at every
vertex by the emission scan while the search characterizes it only below
the cap, and (ledger P1/B-d) the search's other scratch array `q`, whose
*entering* cells the tower export asks to be words because `Ir.StateBound`
is state-global. Without the first `Implements` below is refuted by the
state whose mask holds `B` at its single vertex, which `CoverInv`
tolerates and the semantics does not. All three are preserved by any
bounded run, so carrying them costs a line per turn — and every caller
has them: at the driver they are `RamDriver.LevelMem`'s own conjuncts. -/
def CoverState (B : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (ns : ℕ) (O T ord : ℕ → ℕ) (r : ℕ) (σ : Env) : Prop :=
  ∃ Xoff Xmem asg M : ℕ → ℕ,
    σ.vars "n" = n ∧
    σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
    σ.arrs "ord" = arrOf n ord ∧ σ.arrs "alv" = arrOf n M ∧
    (∃ g, σ.arrs "dist" = arrOf n g) ∧ (∃ g, σ.arrs "q" = arrOf n g) ∧
    σ.arrs "asg" = arrOf n asg ∧
    σ.arrs "xoff" = arrOf (n + 1) Xoff ∧ σ.arrs "xmem" = arrOf (n * n) Xmem ∧
    (∀ v ∈ σ.arrs "alv", v < B) ∧ (∀ v ∈ σ.arrs "dist", v < B) ∧
    (∀ v ∈ σ.arrs "q", v < B) ∧
    CoverInv G A₀ π ord r (σ.vars "c") (σ.vars "xp") Xoff Xmem asg M

/-- **The same loop state at the widened target array** (rebase F-c-3),
`CoverPreW`'s clause for `CoverPre`'s. The slot count is a parameter and
constrains no clause; `CoverState` is the case `nt = ns`, clause for
clause, and every accessor below is stated once, on this one. -/
def CoverStateW (B : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (_ns nt : ℕ) (O T ord : ℕ → ℕ) (r : ℕ) (σ : Env) : Prop :=
  ∃ Xoff Xmem asg M : ℕ → ℕ,
    σ.vars "n" = n ∧
    σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
    σ.arrs "ord" = arrOf n ord ∧ σ.arrs "alv" = arrOf n M ∧
    (∃ g, σ.arrs "dist" = arrOf n g) ∧ (∃ g, σ.arrs "q" = arrOf n g) ∧
    σ.arrs "asg" = arrOf n asg ∧
    σ.arrs "xoff" = arrOf (n + 1) Xoff ∧ σ.arrs "xmem" = arrOf (n * n) Xmem ∧
    (∀ v ∈ σ.arrs "alv", v < B) ∧ (∀ v ∈ σ.arrs "dist", v < B) ∧
    (∀ v ∈ σ.arrs "q", v < B) ∧
    CoverInv G A₀ π ord r (σ.vars "c") (σ.vars "xp") Xoff Xmem asg M

/-- The pinned state is the widened one at `nt = ns`. -/
theorem coverStateW_of_coverState {B : ℕ} {σ : Env}
    (h : CoverState B G A₀ π ns O T ord r σ) : CoverStateW B G A₀ π ns ns O T ord r σ := h

/-- And back. -/
theorem coverState_of_coverStateW {B : ℕ} {σ : Env}
    (h : CoverStateW B G A₀ π ns ns O T ord r σ) : CoverState B G A₀ π ns O T ord r σ := h

/-- **What the pass leaves**: the cluster arena in compressed-row form,
the assignment array, and the two facts that make the pair a
neighborhood cover — each block is a weak-`2r`-reachability fibre, and
every vertex's `r`-ball is inside the block its assignment names. -/
def CoverPost {n : ℕ} (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (ord : ℕ → ℕ) (r : ℕ) (_σ σ' : Env) : Prop :=
  ∃ (Xoff Xmem asg : ℕ → ℕ) (m : ℕ),
    σ'.arrs "xoff" = arrOf (n + 1) Xoff ∧ σ'.arrs "xmem" = arrOf (n * n) Xmem ∧
    σ'.arrs "asg" = arrOf n asg ∧ σ'.vars "xp" = m ∧ m ≤ n * n ∧
    CoverOut G A₀ π ord r m Xoff Xmem asg

theorem CoverStateW.n_eq {B nt : ℕ} {σ : Env} (h : CoverStateW B G A₀ π ns nt O T ord r σ) :
    σ.vars "n" = n := by
  obtain ⟨-, -, -, -, hn, -⟩ := h
  exact hn

theorem CoverStateW.c_le {B nt : ℕ} {σ : Env} (h : CoverStateW B G A₀ π ns nt O T ord r σ) :
    σ.vars "c" ≤ n := by
  obtain ⟨Xoff, Xmem, asg, M, -, -, -, -, -, -, -, -, -, -, -, -, -, hI⟩ := h
  exact hI.pos_le

/-- The mask's cells are words, which is what the search's own `hMB`
asks of the arena a turn runs against. -/
theorem CoverStateW.alv_lt {B nt : ℕ} {σ : Env} (h : CoverStateW B G A₀ π ns nt O T ord r σ) :
    ∀ v ∈ σ.arrs "alv", v < B := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, halv, -⟩ := h
  exact halv

/-- And so are the distance array's, which the emission scan reads at
every vertex. -/
theorem CoverStateW.dist_lt {B nt : ℕ} {σ : Env} (h : CoverStateW B G A₀ π ns nt O T ord r σ) :
    ∀ v ∈ σ.arrs "dist", v < B := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd, -⟩ := h
  exact hd

/-- And so are the search's other scratch array's, which the tower
export asks of the state it starts in (ledger P1/B-d). -/
theorem CoverStateW.q_lt {B nt : ℕ} {σ : Env} (h : CoverStateW B G A₀ π ns nt O T ord r σ) :
    ∀ v ∈ σ.arrs "q", v < B := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hq, -⟩ := h
  exact hq

theorem CoverState.n_eq {B : ℕ} {σ : Env} (h : CoverState B G A₀ π ns O T ord r σ) :
    σ.vars "n" = n := CoverStateW.n_eq (ns := ns) (nt := ns) h

theorem CoverState.c_le {B : ℕ} {σ : Env} (h : CoverState B G A₀ π ns O T ord r σ) :
    σ.vars "c" ≤ n := CoverStateW.c_le (ns := ns) (nt := ns) h

theorem CoverState.alv_lt {B : ℕ} {σ : Env} (h : CoverState B G A₀ π ns O T ord r σ) :
    ∀ v ∈ σ.arrs "alv", v < B := CoverStateW.alv_lt (ns := ns) (nt := ns) h

theorem CoverState.dist_lt {B : ℕ} {σ : Env} (h : CoverState B G A₀ π ns O T ord r σ) :
    ∀ v ∈ σ.arrs "dist", v < B := CoverStateW.dist_lt (ns := ns) (nt := ns) h

theorem CoverState.q_lt {B : ℕ} {σ : Env} (h : CoverState B G A₀ π ns O T ord r σ) :
    ∀ v ∈ σ.arrs "q", v < B := CoverStateW.q_lt (ns := ns) (nt := ns) h

/-- **The specification comes off the invariant.** Nothing in this
proof knows about the program: it is `CoverInv.out`, read once, at the
state the loop exits in — and it never mentions the target array, so
the widening does not reach it. -/
theorem coverPost_of_stateW {B nt : ℕ} (hord : OrdersBy n π ord) {σ σ' : Env}
    (h : CoverStateW B G A₀ π ns nt O T ord r σ') (hc : σ'.vars "c" = n) :
    CoverPost G A₀ π ord r σ σ' := by
  obtain ⟨Xoff, Xmem, asg, M, -, -, -, -, -, -, -, hasg, hxoff, hxmem, -, -, -, hI⟩ := h
  rw [hc] at hI
  exact ⟨Xoff, Xmem, asg, σ'.vars "xp", hxoff, hxmem, hasg, rfl, hI.ptr_le, hI.out hord⟩

theorem coverPost_of_state {B : ℕ} (hord : OrdersBy n π ord) {σ σ' : Env}
    (h : CoverState B G A₀ π ns O T ord r σ') (hc : σ'.vars "c" = n) :
    CoverPost G A₀ π ord r σ σ' := coverPost_of_stateW (ns := ns) (nt := ns) hord h hc

/-- The cost of one centre: one search over the block structure and one
flat scan of the vertices. -/
def centreCost (n ns : ℕ) : ℕ := 100 * n + 50 * ns + 100

/-- The cost of the pass: one centre per vertex, plus the scan that
clears the assignments. The constants are generous — the shape is what
the campaign's budget is spent against, and the sharp charging of the
emitted blocks, `Σ |X_v| ≤ n ^ (1 + δ)`, is the analysis's business and
not the program's. -/
def coverCost (n ns : ℕ) : ℕ := 100 * n * n + 50 * n * ns + 200 * n + 100

/-- **What the walk of the program owes**: the Hoare triple for *one
turn*, `centreStep r`, stated over the program text, the state the loop
carries, and the per-centre cost.

Everything that triple's postcondition *means* is proved above,
unconditionally. `CoverInv.step` is the turn's mathematics — and its
hypothesis `hD` is the search specification's threshold postcondition
verbatim, at the source `ord c` and the cap `2r`, so the composition
against the search is an application and not an argument. What is left
inside this triple is symbolic execution: the source load, the search
(`Refine.BfsBridge.bfsQCom_spec`), the emission scan (`Spec.forRangeZero` over the
vertices, its body the three-way conditional of `emitSlot`), the kill,
and the two commands that close the block. The bounds they need are the
array lengths of `CoverState` and the word bound; the cluster arena
never overflows because the write pointer is at most `c * n` after `c`
centres, which is a clause of the invariant. -/
def Implements (B n ns : ℕ) (G : SimpleGraph (Fin n)) (A₀ O T ord : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (r : ℕ) : Prop :=
  RamBfs.CsrGraph G ns O T → OrdersBy n π ord → n * n + ns + 2 * r + 2 < B →
    (∀ z < n, A₀ z < B) →
    Spec B (fun σ => CoverState B G A₀ π ns O T ord r σ ∧ σ.vars "c" < n) (centreStep r)
      (fun σ σ' => CoverState B G A₀ π ns O T ord r σ' ∧ σ'.vars "c" = σ.vars "c" + 1)
      (centreCost n ns)

/-- **The same obligation at the widened target array** (rebase F-c-3).
Two hypotheses join the four: `hnt : ns ≤ nt`, and the padding clause
`hpad` — every slot of the array above the structure's own holds a
vertex. `hpad` is **not** an artefact of this file: it is the residual
of the tower's F-a decoupling, whose `BfsQ.Shape` keeps its range
clause over the whole physical array because `Ir.StateBound` is
state-global (`Refine.BfsBridge.csr_of_csrGraphW` carries the note).
The pass reads the target array only through the search, so this is the
only place the padding is seen.

`Implements` is the case `nt = ns`, where `hpad` is vacuous.

**The padding clause is guarded by `0 < n`** (rebase F-c-4). A level's
target array is `W` cells with a *zero* tail, not a tail of vertices,
because the range form is unsatisfiable at `n = 0` — `RamDriver.LevelPre`
records the refutation. Zero yields `T j < n` exactly when `n` is
positive, and a turn always has `σ.vars "c" < n` and so does; the guard
is where that reading is taken. Nothing else moves: the clause is
consumed at one place, the search inside the turn. -/
def ImplementsW (B n ns nt : ℕ) (G : SimpleGraph (Fin n)) (A₀ O T ord : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (r : ℕ) : Prop :=
  RamBfs.CsrGraph G ns O T → OrdersBy n π ord → n * n + ns + 2 * r + 2 < B →
    (∀ z < n, A₀ z < B) → ns ≤ nt → (0 < n → ∀ j, ns ≤ j → j < nt → T j < n) →
    Spec B (fun σ => CoverStateW B G A₀ π ns nt O T ord r σ ∧ σ.vars "c" < n) (centreStep r)
      (fun σ σ' => CoverStateW B G A₀ π ns nt O T ord r σ' ∧ σ'.vars "c" = σ.vars "c" + 1)
      (centreCost n ns)

/-- The pinned obligation is the widened one at `nt = ns` — the walk is
written once, at `ImplementsW`, and read off here. -/
theorem implements_of_implementsW {B : ℕ} (h : ImplementsW B n ns ns G A₀ O T ord π r) :
    Implements B n ns G A₀ O T ord π r :=
  fun hcsr hord hB hA => h hcsr hord hB hA le_rfl (fun _ _ h₁ h₂ => absurd h₁ (by omega))

/-- **The cover pass of Grohe–Kreutzer–Siebertz §6.** Handed a block
structure for `G`, an ambient mask, and the order array of an ordering
`π`, `coverCom r` leaves in `xoff`/`xmem` the fibres of weak
`2r`-reachability under `π`, one block per centre in the order's own
order, and in `asg` a map sending every vertex to a block whose cluster
contains its whole `r`-ball. Those are the covering and the radius
conditions of an `r`-neighborhood cover of radius `2r`; the third, the
degree, is the ordering's own weak reachability bound, which
`isNeighborhoodCover_of_out` takes as input and no program computes.

# Proof strategy

The loop is `Spec.forRangeZero` over the positions of the order, run
against `CoverStateW`; `CoverInv.init` is what the three commands before
it establish, `ImplementsW` is one turn, and `CoverInv.out` — through
`coverPost_of_stateW` — is what the exit `c = n` gives. The fill that
clears the assignments is the kit's array pass with the sentinel `n` as
its cell function, and the two commands that open the cluster arena are
walked in place.

**Rebase F-c-3: the walk is written at the widened width.** Nothing in
it reads the target array — the search does, and it enters through the
turn obligation — so `nt` travels from the precondition to the loop
state and nowhere else. `cover_spec` is this at `nt = ns`.

**Rebase E-mem/W1: the turn arrives as a `Spec`, not as `ImplementsW`.**
The assembly reads exactly two things off the value bound — `n < B`, for
the loop's own counter comparison, and the turn triple — and nothing
else in it mentions the arena. Taking the triple as a parameter is what
lets the same assembly be run at the landed carrier bound
(`cover_specW`, below, unchanged) and at
`RamDriver.WordBoundK`'s arena bound
(`Refine.CoverWidth.coverPass_specKW`), with the walk written once. -/
theorem cover_specOfW {B nt : ℕ} (hord : OrdersBy n π ord) (hnB : n < B)
    (hA : ∀ z < n, A₀ z < B)
    (hturn : Spec B (fun σ => CoverStateW B G A₀ π ns nt O T ord r σ ∧ σ.vars "c" < n)
      (centreStep r)
      (fun σ σ' => CoverStateW B G A₀ π ns nt O T ord r σ' ∧ σ'.vars "c" = σ.vars "c" + 1)
      (centreCost n ns)) :
    Spec B (fun σ => CoverPreW n ns nt O T A₀ ord σ ∧ (∀ v ∈ σ.arrs "dist", v < B) ∧
        (∀ v ∈ σ.arrs "q", v < B))
      (coverCom r) (CoverPost G A₀ π ord r)
      (coverCost n ns) := by
  -- what the fill may touch, read off its syntax: the counter and `asg`
  have hwv : ∀ y, y ≠ "i" → y ∉ initAsg.wvars := by
    intro y hy; simp [initAsg, Fill.put, Com.wvars, hy]
  have hwa : ∀ a, a ≠ "asg" → a ∉ initAsg.warrs := by
    intro a ha; simp [initAsg, Fill.put, Com.warrs, ha]
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hn, hoff, htgt, halv, hordarr, hdist, hq, ⟨ga, hasg⟩, ⟨gx, hxoff⟩, ⟨gm, hxmem⟩⟩,
    hdw, hqw⟩ := hσ
  -- the two word clauses at entry: the mask's from `hA`, the search's from the caller
  have halvw : ∀ v ∈ σ.arrs "alv", v < B := fun v hv => by
    rw [halv] at hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv
    exact hA k (List.mem_range.1 hk)
  -- the fill: the kit's array pass, with the sentinel as the cell function
  obtain ⟨σ₁, hrun₁, ⟨⟨g₁, hasg₁, hg₁⟩, -⟩, hfv, hfa, -, -⟩ :=
    ((Fill.loop_spec B n "asg" "i" "n" (.var "n") (fun _ => n) (by decide) hnB
      (fun τ _ hm _ => by
        have hev := evalB_var (B := B) (x := "n") (σ := τ) (by rw [hm]; omega)
        rwa [hm] at hev)).frame).run (σ := σ) ⟨⟨ga, hasg⟩, hn⟩
  -- the write pointer, and the first offset
  have hrun₂ : Run B (.assign "xp" (.lit 0)) σ₁ (σ₁.setVar "xp" 0) (1 + (Expr.lit 0).size) :=
    Run.assign (evalB_lit (by omega))
  have hxoff₂ : (σ₁.setVar "xp" 0).arrs "xoff" = arrOf (n + 1) gx := by
    rw [arrs_setVar, hfa "xoff" (hwa _ (by decide))]; exact hxoff
  have hrun₃ : Run B (.store "xoff" (.lit 0) (.lit 0)) (σ₁.setVar "xp" 0)
      ((σ₁.setVar "xp" 0).setArr "xoff" 0 0) (1 + (Expr.lit 0).size + (Expr.lit 0).size) :=
    Run.store (evalB_lit (by omega)) (evalB_lit (by omega))
      (by rw [hxoff₂, length_arrOf]; omega)
  -- the three commands before the loop are exactly `CoverInv.init`
  have hstart : CoverStateW B G A₀ π ns nt O T ord r
      (((σ₁.setVar "xp" 0).setArr "xoff" 0 0).setVar "c" 0) := by
    obtain ⟨gd, hgd⟩ := hdist
    obtain ⟨gq, hgq⟩ := hq
    refine ⟨upd gx 0 0, gm, g₁, A₀,
      by simp [hfv "n" (hwv _ (by decide)), hn],
      by simp [hfa "off" (hwa _ (by decide)), hoff],
      by simp [hfa "tgt" (hwa _ (by decide)), htgt],
      by simp [hfa "ord" (hwa _ (by decide)), hordarr],
      by simp [hfa "alv" (hwa _ (by decide)), halv],
      ⟨gd, by simp [hfa "dist" (hwa _ (by decide)), hgd]⟩,
      ⟨gq, by simp [hfa "q" (hwa _ (by decide)), hgq]⟩,
      by simp [hasg₁],
      by simp [hxoff₂, set_arrOf_eq_upd],
      by simp [hfa "xmem" (hwa _ (by decide)), hxmem],
      by
        have he : (((σ₁.setVar "xp" 0).setArr "xoff" 0 0).setVar "c" 0).arrs "alv"
            = σ.arrs "alv" := by simp [hfa "alv" (hwa _ (by decide))]
        rw [he]; exact halvw,
      by
        have he : (((σ₁.setVar "xp" 0).setArr "xoff" 0 0).setVar "c" 0).arrs "dist"
            = σ.arrs "dist" := by simp [hfa "dist" (hwa _ (by decide))]
        rw [he]; exact hdw,
      by
        have he : (((σ₁.setVar "xp" 0).setArr "xoff" 0 0).setVar "c" 0).arrs "q"
            = σ.arrs "q" := by simp [hfa "q" (hwa _ (by decide))]
        rw [he]; exact hqw, ?_⟩
    simp only [vars_setVar, vars_setArr]
    exact CoverInv.init (fun _ _ => rfl) (upd_self gx 0 0) hg₁
  -- the loop, against the invariant of the pass
  obtain ⟨σ₄, hrun₄, hst, hcn⟩ :=
    (Spec.forRangeZero (B := B) "c" "n" (CoverStateW B G A₀ π ns nt O T ord r) n
      (centreCost n ns) hnB (fun _ hτ => CoverStateW.c_le hτ) (fun _ hτ => CoverStateW.n_eq hτ)
      hturn).run
      (σ := (σ₁.setVar "xp" 0).setArr "xoff" 0 0) hstart
  have hcost : (10 + (Expr.var "n").size) * n + 6 +
      ((1 + (Expr.lit 0).size) + ((1 + (Expr.lit 0).size + (Expr.lit 0).size) +
        ((centreCost n ns + 4) * n + 6))) ≤ coverCost n ns := by
    simp only [size_lit, size_var, centreCost, coverCost]
    have e₁ : (100 * n + 50 * ns + 100 + 4) * n = 100 * (n * n) + 50 * (n * ns) + 104 * n := by
      ring
    have e₂ : 100 * n * n = 100 * (n * n) := by ring
    have e₃ : 50 * n * ns = 50 * (n * ns) := by ring
    omega
  exact ⟨σ₄, _, (hrun₁.seq (hrun₂.seq (hrun₃.seq hrun₄))).mono hcost, le_rfl,
    coverPost_of_stateW hord hst hcn⟩

/-- **The cover pass of Grohe–Kreutzer–Siebertz §6, at a widened target
array** (rebase F-c-3) — the frozen export, statement for statement what
it was: `cover_specOfW` with the turn supplied by `ImplementsW` at the
carrier value bound. -/
theorem cover_specW {B nt : ℕ} (h : ImplementsW B n ns nt G A₀ O T ord π r)
    (hcsr : RamBfs.CsrGraph G ns O T) (hord : OrdersBy n π ord)
    (hB : n * n + ns + 2 * r + 2 < B) (hA : ∀ z < n, A₀ z < B) (hnt : ns ≤ nt)
    (hpad : 0 < n → ∀ j, ns ≤ j → j < nt → T j < n) :
    Spec B (fun σ => CoverPreW n ns nt O T A₀ ord σ ∧ (∀ v ∈ σ.arrs "dist", v < B) ∧
        (∀ v ∈ σ.arrs "q", v < B))
      (coverCom r) (CoverPost G A₀ π ord r)
      (coverCost n ns) :=
  cover_specOfW hord
    (by
      have hnn : n ≤ n * n := by
        rcases Nat.eq_zero_or_pos n with h₀ | h₀
        · simp [h₀]
        · calc n = n * 1 := by ring
            _ ≤ n * n := Nat.mul_le_mul_left n h₀
      omega)
    hA (h hcsr hord hB hA hnt hpad)

/-- **The cover pass of Grohe–Kreutzer–Siebertz §6, at the pinned
width.** The widened walk at `nt = ns`, where the padding hypothesis is
vacuous — the frozen export, byte for byte what it was. -/
theorem cover_spec {B : ℕ} (h : Implements B n ns G A₀ O T ord π r)
    (hcsr : RamBfs.CsrGraph G ns O T) (hord : OrdersBy n π ord)
    (hB : n * n + ns + 2 * r + 2 < B) (hA : ∀ z < n, A₀ z < B) :
    Spec B (fun σ => CoverPre n ns O T A₀ ord σ ∧ (∀ v ∈ σ.arrs "dist", v < B) ∧
        (∀ v ∈ σ.arrs "q", v < B))
      (coverCom r) (CoverPost G A₀ π ord r)
      (coverCost n ns) :=
  cover_specW (nt := ns) (fun hc ho hb ha _ _ => h hc ho hb ha) hcsr hord hB hA le_rfl
    (fun _ _ h₁ h₂ => absurd h₁ (by omega))

/-! ### The worked example

House discipline: what the specification says is also *seen*. The graph
is the path `0—1—2—3` with an isolated vertex `4`, the ordering is the
identity, the ambient mask is all-alive, and the radius is `1`, so the
clusters are the fibres of weak `2`-reachability.

Hand computation: the centre `0` reaches back two steps, so its fibre
is `{0, 1, 2}`; the centre `1` is `π`-minimal on a walk from `2` or `3`
but not from `0`, so its fibre is `{1, 2, 3}`; likewise `{2, 3}` and
`{3}`; and the isolated `4` has `{4}`. The assignment records first
catches at radius `1`, so `0` and `1` are claimed by centre `0`, `2` by
centre `1`, `3` by centre `2`, and `4` by centre `4` — and each
vertex's whole `1`-ball is inside the cluster it names, which is what
the specification promises. -/

namespace Demo

/-- The offsets of the path `0—1—2—3` with an isolated vertex `4`. -/
def demoOff : Com :=
  .seq (.store "off" (.lit 0) (.lit 0))
    (.seq (.store "off" (.lit 1) (.lit 1))
      (.seq (.store "off" (.lit 2) (.lit 3))
        (.seq (.store "off" (.lit 3) (.lit 5))
          (.seq (.store "off" (.lit 4) (.lit 6))
            (.store "off" (.lit 5) (.lit 6))))))

/-- Its targets: `1 | 0 2 | 1 3 | 2 |`. -/
def demoTgt : Com :=
  .seq (.store "tgt" (.lit 0) (.lit 1))
    (.seq (.store "tgt" (.lit 1) (.lit 0))
      (.seq (.store "tgt" (.lit 2) (.lit 2))
        (.seq (.store "tgt" (.lit 3) (.lit 1))
          (.seq (.store "tgt" (.lit 4) (.lit 3))
            (.store "tgt" (.lit 5) (.lit 2))))))

/-- The ambient mask, with the bit of vertex `2` left open. -/
def demoAlv (a2 : ℕ) : Com :=
  .seq (.store "alv" (.lit 0) (.lit 1))
    (.seq (.store "alv" (.lit 1) (.lit 1))
      (.seq (.store "alv" (.lit 2) (.lit a2))
        (.seq (.store "alv" (.lit 3) (.lit 1))
          (.store "alv" (.lit 4) (.lit 1)))))

/-- The order: the identity, so the ordering is the vertex numbering. -/
def demoOrd : Com :=
  .seq (.store "ord" (.lit 0) (.lit 0))
    (.seq (.store "ord" (.lit 1) (.lit 1))
      (.seq (.store "ord" (.lit 2) (.lit 2))
        (.seq (.store "ord" (.lit 3) (.lit 3))
          (.store "ord" (.lit 4) (.lit 4)))))

/-- Five vertices, six slots. -/
def demoSetup (a2 : ℕ) : Com :=
  .seq (.assign "n" (.lit 5))
    (.seq demoOff (.seq demoTgt (.seq (demoAlv a2) demoOrd)))

/-- The six block offsets, the ten arena cells, the five assignments. -/
def demoReport : Com :=
  .seq (.write (.get "xoff" (.lit 0)))
    (.seq (.write (.get "xoff" (.lit 1)))
      (.seq (.write (.get "xoff" (.lit 2)))
        (.seq (.write (.get "xoff" (.lit 3)))
          (.seq (.write (.get "xoff" (.lit 4)))
            (.seq (.write (.get "xoff" (.lit 5)))
              (.seq (.write (.get "xmem" (.lit 0)))
                (.seq (.write (.get "xmem" (.lit 1)))
                  (.seq (.write (.get "xmem" (.lit 2)))
                    (.seq (.write (.get "xmem" (.lit 3)))
                      (.seq (.write (.get "xmem" (.lit 4)))
                        (.seq (.write (.get "xmem" (.lit 5)))
                          (.seq (.write (.get "xmem" (.lit 6)))
                            (.seq (.write (.get "xmem" (.lit 7)))
                              (.seq (.write (.get "xmem" (.lit 8)))
                                (.seq (.write (.get "xmem" (.lit 9)))
                                  (.seq (.write (.get "asg" (.lit 0)))
                                    (.seq (.write (.get "asg" (.lit 1)))
                                      (.seq (.write (.get "asg" (.lit 2)))
                                        (.seq (.write (.get "asg" (.lit 3)))
                                          (.write (.get "asg" (.lit 4)))
                                          )))))))))))))))))))

/-- Build the structure, run the pass, report. -/
def demoWatched (a2 r : ℕ) : Com := .seq (demoSetup a2) (.seq (coverCom r) demoReport)

/-- Twenty-two scalars, nine arrays, four temporaries. The scalar list
is the tower search's own eighteen cells — the four parameters, the
constant, and the thirteen junk cells — plus the pass's `c`, `xp` and
the emission scan's `z`, `dz`. -/
def demoLayout : Lax13Proofs.Compile.Layout :=
  ⟨["n", "src", "sent", "d", "one", "i", "head", "a", "tl", "v", "dv", "dv1", "k0",
    "v1", "kend", "u", "au", "du", "c", "xp", "z", "dz"],
   ["off", "tgt", "alv", "dist", "q", "ord", "xoff", "xmem", "asg"], 4⟩

/-- The machine program. -/
def demoProg (a2 r : ℕ) : Lax13.Ram.Program :=
  Lax13Proofs.Compile.compileProgram demoLayout (demoWatched a2 r)

/-- The layout covers the block, so the compilation is the one the
simulation theorem is about and not an accident. -/
theorem demoWatched_ok (a2 r : ℕ) :
    Lax13Proofs.Compile.Com.Ok demoLayout (demoWatched a2 r) := by
  simp [demoWatched, demoSetup, demoOff, demoTgt, demoAlv, demoOrd, demoReport, coverCom,
    -- `Codegen.embed` is *not* unfolded here: its nine `@[simp]` equations do the
    -- work, and unfolding it would leak `embed.match_1.splitter` into the tower's
    -- namespace, which only the root `lax` audit catches
    initAsg, centreStep, emitLoop, emitSlot, Refine.BfsBridge.bfsQCom,
    Refine.BfsBridge.bfsSetup, Lax13Proofs.Refine.BfsQSynth.bfsQSynth_impl,
    Fill.put, demoLayout,
    Lax13Proofs.Compile.Com.Ok, Lax13Proofs.Compile.Cond.Ok,
    Lax13Proofs.Compile.condExpr, Lax13Proofs.Compile.Expr.Ok]

/-- Run it at a word length that holds every number this graph
produces. -/
def demoRun (a2 r : ℕ) : Option (List ℕ × ℕ) :=
  runOut 16 400000 (demoProg a2 r) (Lax13.Ram.initState []) 0

-- radius `1`: the fibres `{0,1,2} | {1,2,3} | {2,3} | {3} | {4}`, and the
-- first catches `0 0 1 2 4`
#guard demoRun 1 1 =
  some ([0, 3, 6, 8, 9, 10, 0, 1, 2, 1, 2, 3, 2, 3, 3, 4, 0, 0, 1, 2, 4], 5611)
-- with vertex `2` dead the arena is the edge `0—1` and three isolated
-- vertices, so every cluster but the first is a singleton
#guard demoRun 0 1 =
  some ([0, 2, 3, 4, 5, 6, 0, 1, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 2, 3, 4], 4554)
-- at radius `0` weak reachability is equality, so every cluster is its
-- own centre and every vertex claims itself
#guard demoRun 1 0 =
  some ([0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4], 3833)
-- and at radius `2` the first cluster swallows the whole path, which
-- three of the four path vertices then claim
#guard demoRun 1 2 =
  some ([0, 4, 7, 9, 10, 11, 0, 1, 2, 3, 1, 2, 3, 2, 3, 3, 0, 0, 0, 1, 4], 6201)

/-! ### The widening, differentially (rebase F-c-3)

`cover_specW` claims that materializing the target array wider than the
block structure occupies changes nothing the pass computes. That is a
claim about *runs*, so it is checked on runs: the same graph, the same
ordering, the same radii — and two more slots written past the
structure's six, holding vertices the structure never names.

The check is the F-a pattern: the padded run's answers are compared to
the exact run's cell by cell, at all four settings of the worked
example. Only the clock moves, by the two extra stores. -/

/-- The demo's targets, in an array materialized two slots wider: the
padding names vertices `0` and `4`, which is `csr_of_csrGraphW`'s
`hpad`. -/
def demoTgtPad : Com :=
  .seq demoTgt (.seq (.store "tgt" (.lit 6) (.lit 0)) (.store "tgt" (.lit 7) (.lit 4)))

/-- The same setup at the widened array. -/
def demoSetupPad (a2 : ℕ) : Com :=
  .seq (.assign "n" (.lit 5))
    (.seq demoOff (.seq demoTgtPad (.seq (demoAlv a2) demoOrd)))

def demoWatchedPad (a2 r : ℕ) : Com :=
  .seq (demoSetupPad a2) (.seq (coverCom r) demoReport)

def demoProgPad (a2 r : ℕ) : Lax13.Ram.Program :=
  Lax13Proofs.Compile.compileProgram demoLayout (demoWatchedPad a2 r)

theorem demoWatchedPad_ok (a2 r : ℕ) :
    Lax13Proofs.Compile.Com.Ok demoLayout (demoWatchedPad a2 r) := by
  simp [demoWatchedPad, demoSetupPad, demoOff, demoTgtPad, demoTgt, demoAlv, demoOrd,
    demoReport, coverCom, initAsg, centreStep, emitLoop, emitSlot,
    Refine.BfsBridge.bfsQCom, Refine.BfsBridge.bfsSetup,
    Lax13Proofs.Refine.BfsQSynth.bfsQSynth_impl, Fill.put, demoLayout,
    Lax13Proofs.Compile.Com.Ok, Lax13Proofs.Compile.Cond.Ok,
    Lax13Proofs.Compile.condExpr, Lax13Proofs.Compile.Expr.Ok]

def demoRunPad (a2 r : ℕ) : Option (List ℕ × ℕ) :=
  runOut 16 400000 (demoProgPad a2 r) (Lax13.Ram.initState []) 0

-- **The widening is invisible**: padded and exact agree on every
-- reported cell, at every setting of the worked example.
#guard (demoRunPad 1 1).map Prod.fst = (demoRun 1 1).map Prod.fst
#guard (demoRunPad 0 1).map Prod.fst = (demoRun 0 1).map Prod.fst
#guard (demoRunPad 1 0).map Prod.fst = (demoRun 1 0).map Prod.fst
#guard (demoRunPad 1 2).map Prod.fst = (demoRun 1 2).map Prod.fst

-- … and the check has teeth: the two runs are not the same run, they
-- only compute the same thing. The padded one pays for its two stores.
#guard (demoRunPad 1 1).map Prod.snd ≠ (demoRun 1 1).map Prod.snd

/-! **Refuted: the padding hypothesis is not redundant.** `hpad` is not
implied by the block structure — `RamBfs.CsrGraph G ns O T` constrains
`T` only below the slot count `ns = 6`, so a target function agreeing
with the demo's there and holding a non-vertex above it satisfies every
clause of `CsrGraph` and none of `hpad`. That is why
`csr_of_csrGraphW` asks for it separately, and it is F-a's own residual
(`BfsQ.Shape`'s range clause runs over the whole physical array). -/

private def demoT : ℕ → ℕ := fun j => [1, 0, 2, 1, 3, 2].getD j 9

-- below the slot count it is the structure's own target array …
#guard (List.range 6).all fun j => demoT j < 5
-- … and above it there is nothing to say, so `hpad` is a real
-- hypothesis and not a consequence
#guard ! ((List.range 8).all fun j => demoT j < 5)

end Demo

end Lax3Proofs.RamCover
