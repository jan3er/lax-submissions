import Lax13Proofs.Refine.NREST.BackwardsReasoning
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
The P1 acceptance program: masked depth-capped breadth-first search,
specified and refined abstract-to-abstract, with the cost riding the
refinement ordering.

This is the exit criterion of P1 of the refinement-tower campaign
(`plans/word-ram/refinement-tower-plan.md`, "P1 — NREST core"): *the
masked depth-capped BFS algorithm (RamBfs's content) specified and
refined abstract-to-abstract, cost riding the ordering, in textbook
shape*. Nothing of the tower is exercised here that is not the ported
NREST core: the specification is one `NRest.spec`, the algorithm is
built from `bindT` / `consume` / `MIf` / `assert` / `whileIET`, and the
refinement proof is `gwp_specifies_I` followed by `refine_vcg` with the
loop rule reading the invariant and the energy off the term.

## What is specified

Given a graph `G` on `Fin n`, a mask `M : Fin n → Bool`, a source `s`
and a cap `d`, the algorithm computes `D : Fin n → ℕ` with

  `∀ v, ∀ k ≤ d, (D v ≤ k ↔ WD G M k s v)`,

one threshold at a time, where `WD G M k u v` is "some walk of the
masked graph from `u` to `v` has length at most `k`" and the masked
graph is `G` with an edge surviving iff **both** of its endpoints are
alive. Nothing is assumed of the source: a dead source is at distance
`0` from itself and from nothing else (`WD.of_dead`), which is what the
masked graph says too, so the single threshold-iff covers the
degenerate case without a clause of its own.

## The package constraint (design.md §10.4, adjusted)

`Lax13Proofs` depends on the `Lax13` concepts and mathlib, and on
nothing else; it cannot import the ND-MC packages, so it cannot name
`Lax3.ColoredGraphs.WithinDist` or `Lax3Proofs.RamBfs.masked`. The
vocabulary here is therefore mathlib's — `SimpleGraph (Fin n)`,
`SimpleGraph.Walk`, a `Bool` mask — and `masked`/`WD` are defined
locally with exactly the shape those two have. The bridge is one line
on the consumer's side at P7:
`Lax3Proofs.RamBfs.masked G M' = masked G (fun v => M' v ≠ 0)` and
`WD ↔ WithinDist (masked …)`, both `rfl`-adjacent, since
`deleteVerts G {v | M v = 0}` has exactly the adjacency `masked` has.
The postcondition shape is `bfs_spec`'s postcondition shape verbatim
(`∀ v k, k ≤ d → (D v ≤ k ↔ …)`), which is what makes P7 a consumer of
this file rather than a rewrite of it.

## Provenance

The abstract program is the textbook level-synchronous BFS, in the
shape of `Refine_Monadic`'s `Breadth_First_Search` example (the source
distribution's own tutorial algorithm), with the currencies of
design.md F4 attached to each step. The invariant is the classical
frontier invariant with the mask folded in, and it is the abstract
counterpart of `Lax3Proofs.RamBfs.Frontier`: written distances are
correct and final up to the current level, the frontier is the current
level, everything undiscovered reads the sentinel `d + 1`. The exit
argument is the abstract counterpart of `Frontier.complete`.

## Deviations, each flagged

* **E1 — the frontier is a `List (Fin n)` carrying a `Nodup` clause,
  and the next level is produced by a `SPEC`, not by an inner loop.**
  The source's abstract BFS chooses the next level with a set-valued
  `SPEC` and refines the order away later; ours fixes the carrier to a
  duplicate-free list already at the abstract level, because the cost
  is charged per frontier element and the honest accounting needs the
  elements to be distinct. The nondeterminism the source has — *which*
  order the level is enumerated in — is exactly what the `SPEC` still
  leaves open. Refining the `SPEC` into a `FOREACH` over the frontier
  is P2/P6 work and changes no statement here.
* **E2 — one local `progress` rule.** The loop rule's side condition
  `progress (C s)` is discharged by `progress_consume`, the `consume`
  instance of the source's `progress_bind`, which
  `BackwardsReasoning.lean` deliberately did not port ("the progress
  suite … `progress_bind` … not ported"). It is proved here in five
  lines and belongs beside `progress_consume_returnT` the next time
  that file thaws.
* **E3 — one local `wfR2` rule.** `NRest.wfR2_cost` covers a single
  currency; the energy annotation is a sum of two, so `wfR2_add` and
  `wfR2_zero` are proved locally. They belong in `TimeRefinement.lean`
  next to `wfR2_cost`.
* **E4 — the `''if''` currency is part of the advertised budget.** The
  source's `MIf` always charges `cost ''if'' 1`, and the seed of this
  algorithm branches on whether the source is alive (`RamBfs` branches
  in the same place), so the budget names that unit explicitly rather
  than hiding it inside another currency.

None of these touches a ported judgment, a rule statement or the
calculus.

## The currencies (design.md F4)

Four, all named after what the concrete program will do, and priced
later by an exchange rate at P5:

| currency | charged | total over a run |
|---|---|---|
| `bfs.init` | filling the distance array and seeding the source | `n + 1` |
| `if` | the one branch of the seed (`MIf`'s own currency) | `1` |
| `bfs.level` | one unit per level processed | at most `d` |
| `bfs.expand` | one unit per adjacency slot scanned, plus one per frontier vertex | at most `∑ v alive, (deg v + 1) ≤ 2‖E‖ + n` |

The `bfs.expand` total is the touched-only count, not `n` per level:
every vertex enters at most one frontier, so the levels partition what
is scanned (`remWeight_step`). Charging per level would be the `n²`
mistake of the ND-MC record in a new costume, and the energy
annotation is what rules it out — the budget is provable only because
the frontier weights telescope.

## The D4 gate (ledger D4)

`WD` is given a `Decidable` instance through `Reach`, its
level-by-level unfolding, *proved* equivalent (`reach_iff_WD`); so the
`#guard`s and the Plausible `#test` below check the specification's own
postcondition — `Post` — against a naive reachability decider, on the
executable twin's output. The twin is a genuine resolution of the
algorithm's nondeterminism: `nextLevelE_spec` proves that the level it
picks satisfies the `SPEC` the abstract program leaves open, so a
`#guard` about the twin is a `#guard` about a run of `bfsAlg`.

This matters for a second reason. `bfsAlg_correct` is a `⊑`, and a `⊑`
is also satisfied by a program with no results at all (`SUCCEEDT`); the
gate is what says this one has results and that they are the distances
the specification describes. A proof of non-vacuity — `nofailT` and a
witnessed `inresT` through the `whileT` fixed point — is a termination
argument the tower does not need yet and is not attempted here.

**Refutation record: none.** No authored statement in this file was
falsified — the gate ran on the drafts as written (`Post` on the four
named samples, the two Plausible properties) and found no
counterexample, and no statement had to be repaired. The three negative
controls are there to show the harness discriminates: an off-by-one
array, an all-zero array, and the *right* array read against the
*wrong* mask are all rejected by the same decision procedure that
accepts the twin's output.

The clause of `Inv` most at risk of being wrong is `settled`
(`∀ v, D v ≤ l ∨ D v = d + 1`): without it, "undiscovered" cannot be
identified with the sentinel once the cap sits below the diameter, and
`front_eq` does not propagate across an iteration. That is why the
`d = 1` sample on a graph of diameter `3` is in the gate.
-/

namespace Lax13Proofs.Refine

namespace Bfs

variable {n : ℕ} {G : SimpleGraph (Fin n)} {M : Fin n → Bool} {s : Fin n} {d : ℕ}

/-! ## The masked graph and its distances

The graph-theory side, proved locally: these are the lemmas the
abstract proof consumes, and in a consumer campaign they would live in
that campaign's graph library (`Lax3Proofs.RamBfs`'s `WD` section is
exactly this list). -/

/-- The masked graph: an edge of `G` survives iff **both** of its
endpoints are alive. -/
def masked (G : SimpleGraph (Fin n)) (M : Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ M u = true ∧ M v = true
  symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

@[simp] theorem masked_adj {u v : Fin n} :
    (masked G M).Adj u v ↔ G.Adj u v ∧ M u = true ∧ M v = true := Iff.rfl

instance instDecidableMaskedAdj [DecidableRel G.Adj] : DecidableRel (masked G M).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ M u = true ∧ M v = true))

/-- `v` is within distance `k` of `u` in the masked graph: some walk of
the masked graph from `u` to `v` has length at most `k`. This is
`Lax3.ColoredGraphs.WithinDist (masked G M) k u v`, spelled locally
because this package cannot import that one. -/
def WD (G : SimpleGraph (Fin n)) (M : Fin n → Bool) (k : ℕ) (u v : Fin n) : Prop :=
  ∃ w : (masked G M).Walk u v, w.length ≤ k

/-- Every vertex is within distance `0` of itself — alive or not. -/
theorem WD.refl (G : SimpleGraph (Fin n)) (M : Fin n → Bool) (k : ℕ) (v : Fin n) :
    WD G M k v v :=
  ⟨SimpleGraph.Walk.nil, by simp⟩

/-- Monotone in the threshold. -/
theorem WD.mono {k k' : ℕ} {u v : Fin n} (hk : k ≤ k') (h : WD G M k u v) : WD G M k' u v :=
  ⟨h.choose, le_trans h.choose_spec hk⟩

/-- Walks reverse. -/
theorem WD.symm {k : ℕ} {u v : Fin n} (h : WD G M k u v) : WD G M k v u := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w.reverse, by rwa [SimpleGraph.Walk.length_reverse]⟩

/-- Step extension: one masked edge at the far end. -/
theorem WD.step {k : ℕ} {u v z : Fin n} (h : WD G M k u v) (e : (masked G M).Adj v z) :
    WD G M (k + 1) u z := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w.concat e, by rw [SimpleGraph.Walk.length_concat]; omega⟩

/-- At threshold `0` there is nothing but the vertex itself. -/
theorem WD.eq_of_zero {u v : Fin n} (h : WD G M 0 u v) : u = v := by
  obtain ⟨w, hw⟩ := h
  cases w with
  | nil => rfl
  | cons _ p => simp at hw

/-- Head decomposition: a walk of length at most `k + 1` is trivial or
starts with a masked edge. -/
theorem WD.head {k : ℕ} {u v : Fin n} (h : WD G M (k + 1) u v) :
    u = v ∨ ∃ c, (masked G M).Adj u c ∧ WD G M k c v := by
  obtain ⟨w, hw⟩ := h
  cases w with
  | nil => exact Or.inl rfl
  | cons hadj p => exact Or.inr ⟨_, hadj, p, by simpa using hw⟩

/-- Tail decomposition: a walk of length at most `k + 1` is shorter or
ends with a masked edge. This is the form the BFS argument uses. -/
theorem WD.tail {k : ℕ} {u v : Fin n} (h : WD G M (k + 1) u v) :
    WD G M k u v ∨ ∃ c, WD G M k u c ∧ (masked G M).Adj c v := by
  rcases h.symm.head with heq | ⟨c, hadj, hc⟩
  · exact Or.inl (heq ▸ WD.refl G M k u)
  · exact Or.inr ⟨c, hc.symm, hadj.symm⟩

/-- **The dead-source degeneracy.** A dead vertex has no masked edge at
all, so its only ball is itself, at every threshold. -/
theorem WD.of_dead {k : ℕ} {v : Fin n} (hs : M s = false) : WD G M k s v ↔ s = v := by
  refine ⟨fun h => ?_, fun h => h ▸ WD.refl G M k s⟩
  obtain ⟨w, -⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ => rw [masked_adj] at hadj; simp [hs] at hadj

/-! ### `Reach`: the executable reading of `WD`

The level-by-level unfolding of `WD`, used by the D4 gate to decide the
specification's own postcondition. The equivalence is proved, so the
gate checks `WD` itself. -/

/-- `WD`, unfolded one threshold at a time. -/
def Reach (G : SimpleGraph (Fin n)) (M : Fin n → Bool) : ℕ → Fin n → Fin n → Prop
  | 0, u, v => u = v
  | (k + 1), u, v => Reach G M k u v ∨ ∃ c, Reach G M k u c ∧ (masked G M).Adj c v

@[simp] theorem Reach_zero {u v : Fin n} : Reach G M 0 u v ↔ u = v := Iff.rfl

@[simp] theorem Reach_succ {k : ℕ} {u v : Fin n} :
    Reach G M (k + 1) u v ↔ Reach G M k u v ∨ ∃ c, Reach G M k u c ∧ (masked G M).Adj c v :=
  Iff.rfl

instance instDecidableReach [DecidableRel G.Adj] :
    ∀ (k : ℕ) (u v : Fin n), Decidable (Reach G M k u v)
  | 0, u, v => inferInstanceAs (Decidable (u = v))
  | (k + 1), _, _ =>
    letI : ∀ (a b : Fin n), Decidable (Reach G M k a b) := instDecidableReach k
    inferInstanceAs (Decidable (_ ∨ ∃ _, _))

/-- **The gate's bridge.** -/
theorem reach_iff_WD {k : ℕ} {u v : Fin n} : Reach G M k u v ↔ WD G M k u v := by
  induction k generalizing v with
  | zero =>
    exact ⟨fun h => h ▸ WD.refl G M 0 u, fun h => h.eq_of_zero⟩
  | succ k ih =>
    constructor
    · rintro (h | ⟨c, hc, hadj⟩)
      · exact (ih.mp h).mono (Nat.le_succ k)
      · exact (ih.mp hc).step hadj
    · intro h
      rcases h.tail with h' | ⟨c, hc, hadj⟩
      · exact Or.inl (ih.mpr h')
      · exact Or.inr ⟨c, ih.mpr hc, hadj⟩

instance instDecidableWD [DecidableRel G.Adj] (k : ℕ) (u v : Fin n) :
    Decidable (WD G M k u v) :=
  decidable_of_iff _ reach_iff_WD

/-! ## The abstract state

Plain data: the distance array as a function, the frontier as a list,
the level as a number. The sentinel is `d + 1`, exactly as `RamBfs`
uses it. -/

/-- The abstract search state. -/
abbrev State (n : ℕ) : Type := (Fin n → ℕ) × List (Fin n) × ℕ

/-- The distance array of a state. -/
abbrev distArr (st : State n) : Fin n → ℕ := st.1

/-- The frontier of a state. -/
abbrev front (st : State n) : List (Fin n) := st.2.1

/-- The level of a state. -/
abbrev level (st : State n) : ℕ := st.2.2

@[simp] theorem distArr_mk (D : Fin n → ℕ) (F : List (Fin n)) (l : ℕ) :
    distArr (D, F, l) = D := rfl

@[simp] theorem front_mk (D : Fin n → ℕ) (F : List (Fin n)) (l : ℕ) :
    front (D, F, l) = F := rfl

@[simp] theorem level_mk (D : Fin n → ℕ) (F : List (Fin n)) (l : ℕ) :
    level (D, F, l) = l := rfl

/-- The initial distance array: the sentinel everywhere, `0` at the
source. A dead source is written too — it is at distance `0` from
itself in the masked graph. -/
def initDist (s : Fin n) (d : ℕ) : Fin n → ℕ := fun v => if v = s then 0 else d + 1

/-- What the frontier's expansion is allowed to return: a duplicate-free
list of exactly the undiscovered vertices with a masked neighbour on the
frontier. The *order* is left open — that is the nondeterminism the
abstract program keeps. -/
def NextLevel (G : SimpleGraph (Fin n)) (M : Fin n → Bool) (d : ℕ) (st : State n)
    (F' : List (Fin n)) : Prop :=
  F'.Nodup ∧
    ∀ v, v ∈ F' ↔ (distArr st v = d + 1 ∧ ∃ u ∈ front st, (masked G M).Adj u v)

/-- Relaxation: everything on the new level is written at the new level,
everything else keeps what it had. -/
def relax (st : State n) (F' : List (Fin n)) : Fin n → ℕ :=
  fun v => if v ∈ F' then level st + 1 else distArr st v

/-! ## The cost model -/

/-- What scanning one vertex costs: one unit per adjacency slot, plus
one for the vertex itself. -/
def vweight (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) : ℕ := G.degree v + 1

/-- What expanding one frontier costs. -/
def levelWeight (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (F : List (Fin n)) : ℕ :=
  (F.map (vweight G)).sum

/-- What the *remaining* levels can still cost: the alive vertices not
yet expanded. This is the touched-only measure the energy annotation
rides on. -/
def remWeight (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool)
    (D : Fin n → ℕ) (l : ℕ) : ℕ :=
  ∑ v ∈ Finset.univ.filter (fun v => l ≤ D v ∧ M v = true), vweight G v

/-- What a whole run can cost in `bfs.expand`. -/
def totalWeight (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool) : ℕ :=
  ∑ v ∈ Finset.univ.filter (fun v => M v = true), vweight G v

/-- The `bfs.expand` budget is the linear-in-the-graph one. -/
theorem totalWeight_le (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool) :
    totalWeight G M ≤ 2 * G.edgeFinset.card + n := by
  classical
  have h : totalWeight G M ≤ ∑ v : Fin n, vweight G v :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  calc totalWeight G M ≤ ∑ v : Fin n, vweight G v := h
    _ = (∑ v : Fin n, G.degree v) + n := by
        simp [vweight, Finset.sum_add_distrib]
    _ = 2 * G.edgeFinset.card + n := by rw [G.sum_degrees_eq_twice_card_edges]

/-- At level `0` nothing has been expanded yet. -/
theorem remWeight_zero (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool)
    (D : Fin n → ℕ) : remWeight G M D 0 = totalWeight G M := by
  refine Finset.sum_congr (Finset.filter_congr fun v _ => ?_) fun _ _ => rfl
  simp

/-- The energy annotation: the levels still to run and the weight still
to scan. -/
def bfsE (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool) (d : ℕ)
    (st : State n) : ACost String ℕ :=
  ACost.cost "bfs.level" (d - level st)
    + ACost.cost "bfs.expand" (remWeight G M (distArr st) (level st))

/-- The advertised budget, at `ℕ`. -/
def bfsBudgetN (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool) (d : ℕ) :
    ACost String ℕ :=
  ACost.cost "bfs.init" (n + 1) + ACost.cost "if" 1 + ACost.cost "bfs.level" d
    + ACost.cost "bfs.expand" (totalWeight G M)

/-! ## The specification -/

/-- **The postcondition**: at every threshold up to the cap, the array
decides masked distance from the source. One threshold at a time. -/
def Post (G : SimpleGraph (Fin n)) (M : Fin n → Bool) (s : Fin n) (d : ℕ)
    (D : Fin n → ℕ) : Prop :=
  ∀ v : Fin n, ∀ k ≤ d, (D v ≤ k ↔ WD G M k s v)

/-- The postcondition is decidable — this is what lets the D4 gate below
check the specification itself rather than a paraphrase of it. -/
instance instDecidablePost (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool)
    (s : Fin n) (d : ℕ) (D : Fin n → ℕ) : Decidable (Post G M s d D) :=
  inferInstanceAs (Decidable (∀ v : Fin n, ∀ k ≤ d, (D v ≤ k ↔ WD G M k s v)))

/-- **The specification**, as one `NRest.spec`: any array deciding the
masked distance thresholds, for the advertised currency budget. -/
noncomputable def bfsSpec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool)
    (s : Fin n) (d : ℕ) : NRest (Fin n → ℕ) ECost :=
  NRest.spec (Post G M s d) fun _ => liftACost (bfsBudgetN G M d)

/-! ## The abstract algorithm -/

/-- The loop runs while the frontier is non-empty and the cap is not
reached. -/
def bfsCond (d : ℕ) (st : State n) : Bool := !(front st).isEmpty && decide (level st < d)

/-- **The invariant**: the classical BFS frontier invariant with the
mask folded in. The abstract counterpart of `Lax3Proofs.RamBfs.Frontier`
— written distances correct and final up to the current level, the
frontier is the current level, undiscovered reads the sentinel. -/
structure Inv (G : SimpleGraph (Fin n)) (M : Fin n → Bool) (s : Fin n) (d : ℕ)
    (st : State n) : Prop where
  /-- The cap has not been passed. -/
  level_le : level st ≤ d
  /-- Nothing is on the frontier twice. -/
  nodup : (front st).Nodup
  /-- The frontier is exactly the alive part of the current level. -/
  front_eq : ∀ v, v ∈ front st ↔ (distArr st v = level st ∧ M v = true)
  /-- Nothing ever exceeds the sentinel. -/
  cap : ∀ v, distArr st v ≤ d + 1
  /-- Everything is either settled at or below the current level, or
  still reading the sentinel. -/
  settled : ∀ v, distArr st v ≤ level st ∨ distArr st v = d + 1
  /-- Every threshold up to the current level is already decided. -/
  correct : ∀ v, ∀ k ≤ level st, (distArr st v ≤ k ↔ WD G M k s v)

/-- `Inv`'s constructor, with the state's three components spelled out —
the projections are definitional, so this is `Inv.mk`, but it keeps the
goals of the invariant proofs readable. -/
theorem inv_mk {D : Fin n → ℕ} {F : List (Fin n)} {l : ℕ} (h1 : l ≤ d) (h2 : F.Nodup)
    (h3 : ∀ v, v ∈ F ↔ (D v = l ∧ M v = true)) (h4 : ∀ v, D v ≤ d + 1)
    (h5 : ∀ v, D v ≤ l ∨ D v = d + 1)
    (h6 : ∀ v, ∀ k ≤ l, (D v ≤ k ↔ WD G M k s v)) : Inv G M s d (D, F, l) :=
  ⟨h1, h2, h3, h4, h5, h6⟩

theorem bfsCond_eq_true {st : State n} :
    bfsCond d st = true ↔ front st ≠ [] ∧ level st < d := by
  cases h : front st <;> simp [bfsCond, h]

theorem bfsCond_eq_false {st : State n} :
    bfsCond d st = false ↔ front st = [] ∨ d ≤ level st := by
  cases h : front st <;> simp [bfsCond, h]

/-- **One iteration**: assert that the cap leaves room, pick the next
level (paying one `bfs.expand` unit per adjacency slot it scans), write
it, and step the level — paying one `bfs.level` unit for the iteration
itself. -/
noncomputable def bfsBody (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool)
    (d : ℕ) (st : State n) : NRest (State n) ECost :=
  NRest.consume
    (NRest.bindT (NRest.assert (level st < d)) fun _ =>
      NRest.bindT
        (NRest.spec (NextLevel G M d st)
          fun _ => ACost.cost "bfs.expand" ((levelWeight G (front st) : ℕ) : ℕ∞))
        fun F' => NRest.returnT (relax st F', F', level st + 1))
    (ACost.cost "bfs.level" (1 : ℕ∞))

/-- **The abstract algorithm**: fill the distance array with the
sentinel and seed the source, put the source on the frontier if it is
alive, then run the level loop to exhaustion or to the cap, and read the
distance array off the final state. -/
noncomputable def bfsAlg (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool)
    (s : Fin n) (d : ℕ) : NRest (Fin n → ℕ) ECost :=
  NRest.bindT
    (NRest.consume (NRest.returnT (initDist s d))
      (ACost.cost "bfs.init" ((n + 1 : ℕ) : ℕ∞))) fun D₀ =>
  NRest.bindT (NRest.MIf (M s) (NRest.returnT [s]) (NRest.returnT [])) fun F₀ =>
  NRest.bindT
    (NRest.whileIET (Inv G M s d) (bfsE G M d) (bfsCond d) (bfsBody G M d) (D₀, F₀, 0))
    fun st => NRest.returnT (distArr st)

/-! ## The invariant lemmas (the math-side-shaped proof) -/

/-- The seed establishes the invariant, in both branches of the seed's
`MIf`: `F₀` is `[s]` when the source is alive and `[]` when it is
not. -/
theorem inv_init {F₀ : List (Fin n)} (hnd : F₀.Nodup)
    (hF₀ : ∀ v, v ∈ F₀ ↔ (v = s ∧ M v = true)) :
    Inv G M s d (initDist s d, F₀, 0) := by
  refine inv_mk (Nat.zero_le _) hnd (fun v => ?_) (fun v => ?_) (fun v => ?_) (fun v k hk => ?_)
  · rw [hF₀ v]
    constructor
    · rintro ⟨rfl, hm⟩; exact ⟨by simp [initDist], hm⟩
    · rintro ⟨h0, hm⟩
      refine ⟨?_, hm⟩
      by_contra hne
      simp [initDist, hne] at h0
  · by_cases hv : v = s <;> simp [initDist, hv]
  · by_cases hv : v = s <;> simp [initDist, hv]
  · have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    constructor
    · intro h
      have hv : v = s := by
        by_contra hne
        simp [initDist, hne] at h
      exact hv ▸ WD.refl G M 0 s
    · intro h
      have hsv := h.eq_of_zero
      simp [initDist, ← hsv]

/-- **The step.** One iteration preserves the invariant: the new level
is written at `l + 1`, and every threshold up to `l + 1` is decided
afterwards. The `l + 1` half is the classical BFS argument — a walk of
length `l + 1` ends at a masked neighbour of a vertex the invariant has
already settled, and such a vertex is either on the frontier (so its
neighbour is discovered now) or below it (so its neighbour was
discovered earlier). -/
theorem inv_step {st : State n} (hI : Inv G M s d st) (hb : bfsCond d st = true)
    {F' : List (Fin n)} (hF' : NextLevel G M d st F') :
    Inv G M s d (relax st F', F', level st + 1) := by
  obtain ⟨hnd', hmem'⟩ := hF'
  obtain ⟨-, hlt⟩ := bfsCond_eq_true.mp hb
  -- the two clauses of `relax`, named
  have hrelax_mem : ∀ v, v ∈ F' → relax st F' v = level st + 1 := by
    intro v hv; simp [relax, hv]
  have hrelax_not : ∀ v, v ∉ F' → relax st F' v = distArr st v := by
    intro v hv; simp [relax, hv]
  -- a vertex of the new level was undiscovered, and is alive
  have hsent : ∀ v ∈ F', distArr st v = d + 1 := fun v hv => ((hmem' v).mp hv).1
  have halive : ∀ v ∈ F', M v = true := by
    intro v hv
    obtain ⟨-, u, -, hadj⟩ := (hmem' v).mp hv
    exact (masked_adj.mp hadj).2.2
  -- everything settled at or below the level is off the new level
  have hoff : ∀ v, distArr st v ≤ level st → v ∉ F' := by
    intro v hv hmem
    have := hsent v hmem
    have := hI.level_le
    omega
  -- a vertex of the new level really is at distance `l + 1`
  have hnew : ∀ v ∈ F', WD G M (level st + 1) s v := by
    intro v hv
    obtain ⟨-, u, hu, hadj⟩ := (hmem' v).mp hv
    have hdu := ((hI.front_eq u).mp hu).1
    exact ((hI.correct u (level st) le_rfl).mp (le_of_eq hdu)).step hadj
  -- **the closure step**: a masked neighbour of a settled vertex is settled
  have hclose : ∀ c v, distArr st c ≤ level st → (masked G M).Adj c v →
      relax st F' v ≤ distArr st c + 1 := by
    intro c v hc hadj
    rcases lt_or_eq_of_le hc with hlt' | heq
    · -- `c` is below the frontier: its neighbours were discovered earlier
      have hwd : WD G M (distArr st c) s c := (hI.correct c _ hc).mp le_rfl
      have hwd' : WD G M (distArr st c + 1) s v := hwd.step hadj
      have hle : distArr st c + 1 ≤ level st := by omega
      have hdv : distArr st v ≤ distArr st c + 1 := (hI.correct v _ hle).mpr hwd'
      rw [hrelax_not v (hoff v (by omega))]
      exact hdv
    · -- `c` is on the frontier, so `v` is discovered now if it was not before
      have hcF : c ∈ front st := (hI.front_eq c).mpr ⟨heq, (masked_adj.mp hadj).2.1⟩
      by_cases hdv : distArr st v = d + 1
      · have : v ∈ F' := (hmem' v).mpr ⟨hdv, c, hcF, hadj⟩
        rw [hrelax_mem v this]
        omega
      · have hdv' : distArr st v ≤ level st := (hI.settled v).resolve_right hdv
        rw [hrelax_not v (hoff v hdv')]
        omega
  refine inv_mk (by omega) hnd' (fun v => ?_) (fun v => ?_) (fun v => ?_) (fun v k hk => ?_)
  · -- the frontier is the new level
    constructor
    · intro hv; exact ⟨hrelax_mem v hv, halive v hv⟩
    · rintro ⟨hd, hm⟩
      by_contra hv
      rw [hrelax_not v hv] at hd
      rcases hI.settled v with h | h <;> omega
  · -- the sentinel is still the ceiling
    by_cases hv : v ∈ F'
    · rw [hrelax_mem v hv]; omega
    · rw [hrelax_not v hv]; exact hI.cap v
  · -- settled or sentinel
    by_cases hv : v ∈ F'
    · exact Or.inl (le_of_eq (hrelax_mem v hv))
    · rw [hrelax_not v hv]
      rcases hI.settled v with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
  · -- every threshold up to `l + 1` is decided
    rcases Nat.lt_or_ge k (level st + 1) with hk' | hk'
    · -- below the new level: nothing changed
      have hkl : k ≤ level st := by omega
      constructor
      · intro h
        have hv : v ∉ F' := by
          intro hmem
          rw [hrelax_mem v hmem] at h
          omega
        rw [hrelax_not v hv] at h
        exact (hI.correct v k hkl).mp h
      · intro h
        have hd := (hI.correct v k hkl).mpr h
        have hv : v ∉ F' := hoff v (by omega)
        rw [hrelax_not v hv]
        exact hd
    · -- at the new level
      have hkeq : k = level st + 1 := by omega
      subst hkeq
      constructor
      · intro h
        by_cases hv : v ∈ F'
        · exact hnew v hv
        · rw [hrelax_not v hv] at h
          have hdv : distArr st v ≤ level st := by
            rcases hI.settled v with h' | h' <;> omega
          exact ((hI.correct v _ hdv).mp le_rfl).mono (by omega)
      · intro h
        rcases h.tail with h' | ⟨c, hc, hadj⟩
        · have hd := (hI.correct v _ le_rfl).mpr h'
          rw [hrelax_not v (hoff v hd)]
          omega
        · have hdc := (hI.correct c _ le_rfl).mpr hc
          exact le_trans (hclose c v hdc hadj) (by omega)

/-- **The exit argument.** When the loop stops, every threshold up to
the cap is decided — either because the level has reached the cap, or
because an empty frontier means nothing further is reachable. The second
case is the abstract counterpart of `Frontier.complete`: the last edge
of a walk of length `k + 1` leaves a vertex the induction has already
settled, that vertex is alive (a masked edge has two live ends), hence
it would be on the frontier if it sat at the current level — and the
frontier is empty, so it sits strictly below it. -/
theorem post_of_exit {st : State n} (hI : Inv G M s d st) (hb : bfsCond d st = false) :
    Post G M s d (distArr st) := by
  by_cases hlvl : level st = d
  · intro v k hk
    exact hI.correct v k (by omega)
  -- the level has not reached the cap, so the frontier is empty
  have hempty : front st = [] := by
    rcases bfsCond_eq_false.mp hb with h | h
    · exact h
    · exact absurd (le_antisymm hI.level_le h) hlvl
  have hnone : ∀ v, ¬ (distArr st v = level st ∧ M v = true) := by
    intro v hv
    have := (hI.front_eq v).mpr hv
    rw [hempty] at this
    simp at this
  -- everything the array claims is real
  have hsound : ∀ v, ∀ k ≤ d, distArr st v ≤ k → WD G M k s v := by
    intro v k hk h
    have hdv : distArr st v ≤ level st := by
      rcases hI.settled v with h' | h' <;> omega
    exact ((hI.correct v _ hdv).mp le_rfl).mono h
  -- and everything real is claimed
  have hcomplete : ∀ k, k ≤ d → ∀ v, WD G M k s v → distArr st v ≤ k := by
    intro k
    induction k with
    | zero =>
      intro _ v hwd
      have hs0 : distArr st s ≤ 0 := (hI.correct s 0 (Nat.zero_le _)).mpr (WD.refl G M 0 s)
      rw [← hwd.eq_of_zero]
      exact hs0
    | succ k ih =>
      intro hk v hwd
      rcases hwd.tail with h' | ⟨c, hc, hadj⟩
      · exact le_trans (ih (by omega) v h') (by omega)
      · have hdc := ih (by omega) c hc
        have hdc' : distArr st c ≤ level st := by
          rcases hI.settled c with h' | h' <;> omega
        have hne : distArr st c ≠ level st :=
          fun hcc => hnone c ⟨hcc, (masked_adj.mp hadj).2.1⟩
        have hlt : distArr st c + 1 ≤ level st := by omega
        have hwd' : WD G M (distArr st c + 1) s v :=
          ((hI.correct c _ hdc').mp le_rfl).step hadj
        have := (hI.correct v _ hlt).mpr hwd'
        omega
  exact fun v k hk => ⟨hsound v k hk, hcomplete k hk v⟩

/-! ## The cost lemmas

The frontier weights telescope: every vertex enters at most one
frontier, so the per-level `bfs.expand` charges add up to the alive
weight of the graph and not to `n` per level. -/

/-- The frontier's weight is the weight of the level it is. -/
theorem levelWeight_eq [DecidableRel G.Adj] {st : State n} (hI : Inv G M s d st) :
    levelWeight G (front st)
      = ∑ v ∈ Finset.univ.filter (fun v => distArr st v = level st ∧ M v = true),
          vweight G v := by
  classical
  have hset : (front st).toFinset
      = Finset.univ.filter (fun v => distArr st v = level st ∧ M v = true) := by
    ext v
    simp [List.mem_toFinset, hI.front_eq v]
  rw [levelWeight, ← List.sum_toFinset _ hI.nodup, hset]

/-- **The telescoping.** What the next level still has to scan, plus
what this level scanned, is what this level still had to scan. -/
theorem remWeight_step [DecidableRel G.Adj] {st : State n} (hI : Inv G M s d st)
    (hb : bfsCond d st = true) {F' : List (Fin n)} (hF' : NextLevel G M d st F') :
    remWeight G M (relax st F') (level st + 1) + levelWeight G (front st)
      = remWeight G M (distArr st) (level st) := by
  classical
  obtain ⟨-, hmem'⟩ := hF'
  obtain ⟨-, hlt⟩ := bfsCond_eq_true.mp hb
  -- the relaxation does not move any vertex across the `l + 1` threshold
  have hfilter : Finset.univ.filter (fun v => level st + 1 ≤ relax st F' v ∧ M v = true)
      = Finset.univ.filter (fun v => level st + 1 ≤ distArr st v ∧ M v = true) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hv : v ∈ F'
    · have h1 : relax st F' v = level st + 1 := by simp [relax, hv]
      have h2 : distArr st v = d + 1 := ((hmem' v).mp hv).1
      rw [h1, h2]
      constructor
      · rintro ⟨-, hm⟩; exact ⟨by omega, hm⟩
      · rintro ⟨-, hm⟩; exact ⟨le_rfl, hm⟩
    · rw [show relax st F' v = distArr st v by simp [relax, hv]]
  -- and the level splits off the front of the remaining weight
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun v => level st ≤ distArr st v ∧ M v = true))
    (fun v => distArr st v = level st) (vweight G)
  have hA : (Finset.univ.filter (fun v => level st ≤ distArr st v ∧ M v = true)).filter
      (fun v => distArr st v = level st)
      = Finset.univ.filter (fun v => distArr st v = level st ∧ M v = true) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨-, hm⟩, he⟩; exact ⟨he, hm⟩
    · rintro ⟨he, hm⟩; exact ⟨⟨le_of_eq he.symm, hm⟩, he⟩
  have hB : (Finset.univ.filter (fun v => level st ≤ distArr st v ∧ M v = true)).filter
      (fun v => ¬ distArr st v = level st)
      = Finset.univ.filter (fun v => level st + 1 ≤ distArr st v ∧ M v = true) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hle, hm⟩, he⟩; exact ⟨by omega, hm⟩
    · rintro ⟨hle, hm⟩; exact ⟨⟨by omega, hm⟩, by omega⟩
  rw [hA, hB] at hsplit
  rw [remWeight, hfilter, levelWeight_eq hI, remWeight, ← hsplit]
  omega

/-! ### The two `wfR2` gaps (deviation E3) -/

/-- `wfR2` of the zero cost. -/
theorem wfR2_zero {κ : Type} : NRest.wfR2 (0 : ACost κ ℕ) := by
  refine Set.Finite.subset (Set.finite_empty) fun k hk => ?_
  simp at hk

/-- `wfR2` is closed under sums. -/
theorem wfR2_add {κ : Type} {A B : ACost κ ℕ} (hA : NRest.wfR2 A) (hB : NRest.wfR2 B) :
    NRest.wfR2 (A + B) := by
  refine (hA.union hB).subset fun k hk => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  exact hk (by simp [ACost.toFun_add, hc.1, hc.2])

/-- The energy annotation has finite support. The `Decidable` argument
is instance-implicit so that the loop rule's own classical instance is
what the application picks up. -/
theorem wfR2_bfsE [DecidableRel G.Adj] (st : State n) [Decidable (Inv G M s d st)] :
    NRest.wfR2 (if Inv G M s d st then bfsE G M d st else 0) := by
  split
  · exact wfR2_add (NRest.wfR2_cost _ _) (NRest.wfR2_cost _ _)
  · exact wfR2_zero

/-! ### The one `progress` gap (deviation E2) -/

/-- Charging a positive cost up front is progress. This is the
`consume` instance of the source's `progress_bind`, which
`BackwardsReasoning.lean` did not port. -/
theorem progress_consume {α : Type} {T : ECost} (h : (0 : ECost) < T) (m : NRest α ECost) :
    progress (NRest.consume m T) := by
  rintro s' N hN hs
  cases m with
  | fail => simp at hN
  | rest X =>
    rw [NRest.consume_rest, NRest.rest_inj_iff] at hN
    subst hN
    replace hs : WithBot.map (fun x => T + x) (X s') ≠ ⊥ := hs
    show ((0 : ECost) : WithBot ECost) < WithBot.map (fun x => T + x) (X s')
    rcases withBot_eq_bot_or_coe (X s') with hX | ⟨t, hX⟩
    · rw [hX] at hs; simp at hs
    · rw [hX]
      refine lt_of_lt_of_le (WithBot.coe_lt_coe.mpr h) ?_
      rw [WithBot.map_coe, WithBot.coe_le_coe]
      exact le_add_of_nonneg_right (Nonneg.needname_nonneg (γ := ECost) t)

/-- One `bfs.level` unit is a positive cost. -/
theorem cost_level_pos : (0 : ECost) < ACost.cost "bfs.level" (1 : ℕ∞) := by
  refine lt_iff_le_not_ge.mpr ⟨Nonneg.needname_nonneg _, fun hc => ?_⟩
  have := ACost.le_def.mp hc "bfs.level"
  simp at this

/-! ### The `ℕ`-to-`ℕ∞` bridge for the two cost side conditions

Every cost in the program is a `ℕ` count coerced into `ℕ∞`, so both
arithmetic side conditions are `liftACost` of a `ℕ`-level inequality and
are discharged pointwise by `omega`. -/

/-- The body's charge, as a lift. -/
theorem body_cost_eq_lift (w : ℕ) :
    (ACost.cost "bfs.level" (1 : ℕ∞) + 0 + ACost.cost "bfs.expand" ((w : ℕ) : ℕ∞) : ECost)
      = liftACost (ACost.cost "bfs.level" 1 + 0 + ACost.cost "bfs.expand" w) := by
  ext k
  simp only [ACost.toFun_add, ACost.toFun_zero, ACost.toFun_cost, toFun_liftACost]
  split_ifs <;> simp

/-- **The energy really decreases**: one level fewer to run, and the
weight this level scanned is gone from what is left to scan. -/
theorem energy_le {l dd rw rw' : ℕ} (hl : l < dd) (hle : rw' ≤ rw) :
    (ACost.cost "bfs.level" (dd - (l + 1)) + ACost.cost "bfs.expand" rw' : ACost String ℕ)
      ≤ ACost.cost "bfs.level" (dd - l) + ACost.cost "bfs.expand" rw := by
  refine ACost.le_def.mpr fun k => ?_
  simp only [ACost.toFun_add, ACost.toFun_cost]
  split_ifs <;> (simp_all; try omega)

/-- **The body's charge is paid by the decrease**: one `bfs.level` unit
for the iteration and one `bfs.expand` unit per slot the level scanned,
against the energy the iteration gave up. -/
theorem step_cost_le {l dd w rw rw' : ℕ} (hl : l < dd) (hsplit : rw' + w = rw) :
    (ACost.cost "bfs.level" 1 + 0 + ACost.cost "bfs.expand" w : ACost String ℕ)
      ≤ (ACost.cost "bfs.level" (dd - l) + ACost.cost "bfs.expand" rw)
        - (ACost.cost "bfs.level" (dd - (l + 1)) + ACost.cost "bfs.expand" rw') := by
  refine ACost.le_def.mpr fun k => ?_
  simp only [ACost.toFun_add, ACost.toFun_zero, ACost.toFun_sub, ACost.toFun_cost]
  split_ifs <;> simp_all <;> omega

/-- **The advertised budget covers the run**: whatever the loop gave up
in energy, plus the seed's own charges, is inside the budget. -/
theorem exit_cost_le {i l dd tw rw : ℕ} :
    (ACost.cost "if" 1 + (ACost.cost "bfs.init" i + 0)
        + ((ACost.cost "bfs.level" (dd - 0) + ACost.cost "bfs.expand" tw)
           - (ACost.cost "bfs.level" (dd - l) + ACost.cost "bfs.expand" rw)) : ACost String ℕ)
      ≤ ACost.cost "bfs.init" i + ACost.cost "if" 1 + ACost.cost "bfs.level" dd
        + ACost.cost "bfs.expand" tw := by
  refine ACost.le_def.mpr fun k => ?_
  simp only [ACost.toFun_add, ACost.toFun_zero, ACost.toFun_sub, ACost.toFun_cost]
  split_ifs <;> simp_all

/-- The prefix's charge, as a lift. -/
theorem prefix_cost_eq_lift :
    (ACost.cost "if" (1 : ℕ∞) + (ACost.cost "bfs.init" ((n + 1 : ℕ) : ℕ∞) + 0) : ECost)
      = liftACost (ACost.cost "if" 1 + (ACost.cost "bfs.init" (n + 1) + 0)) := by
  ext k
  simp only [ACost.toFun_add, ACost.toFun_zero, ACost.toFun_cost, toFun_liftACost]
  split_ifs <;> simp

/-! ## The refinement theorem -/

/-- **P1's acceptance.** The abstract masked depth-capped BFS refines
its specification, cost included: `bfsAlg` delivers an array deciding
every masked-distance threshold up to the cap, for
`(n+1)` `bfs.init` + one `if` + `d` `bfs.level` +
`∑ v alive (deg v + 1)` `bfs.expand` units.

The proof is `gwp_specifies_I` and one `refine_vcg` run: the tactic
peels the whole program down to side conditions, and the loop rule reads
the invariant and the energy off the `whileIET` term. What is left are
the five obligations of the loop rule (twice, once per branch of the
seed's `MIf`) and the assertion, each discharged by the lemmas above. No
`gwp` rule is applied by hand. -/
theorem bfsAlg_correct (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool)
    (s : Fin n) (d : ℕ) : bfsAlg G M s d ≤ bfsSpec G M s d := by
  classical
  -- the two cost side conditions, once for both branches of the seed
  have hstep : ∀ (st : State n), Inv G M s d st → bfsCond d st = true →
      ∀ F', NextLevel G M d st F' →
        ((ACost.cost "bfs.level" (1 : ℕ∞) + 0
            + ACost.cost "bfs.expand" ((levelWeight G (front st) : ℕ) : ℕ∞) : ECost)
          : WithBot ECost)
        ≤ mm3 (liftACost (bfsE G M d st))
            (if Inv G M s d (relax st F', F', level st + 1) then
              ((liftACost (bfsE G M d (relax st F', F', level st + 1)) : ECost) : WithBot ECost)
             else ⊥) := by
    intro st hI hb F' hF'
    have hlt : level st < d := (bfsCond_eq_true.mp hb).2
    have hrem := remWeight_step hI hb hF'
    rw [if_pos (inv_step hI hb hF'), mm3_coe]
    have hle : liftACost (bfsE G M d (relax st F', F', level st + 1))
        ≤ liftACost (bfsE G M d st) := by
      rw [liftACost_le_iff]
      simpa only [bfsE, distArr_mk, front_mk, level_mk] using energy_le hlt (by omega)
    rw [if_pos hle, liftACost_resSub, body_cost_eq_lift, WithBot.coe_le_coe, liftACost_le_iff]
    simpa only [bfsE, distArr_mk, front_mk, level_mk] using step_cost_le hlt hrem
  have hexit : ∀ (F₀ : List (Fin n)) (st : State n),
      ((ACost.cost "if" (1 : ℕ∞) + (ACost.cost "bfs.init" ((n + 1 : ℕ) : ℕ∞) + 0)
          + liftACost (bfsE G M d (initDist s d, F₀, 0) - bfsE G M d st)
          : ECost) : WithBot ECost)
        ≤ ((liftACost (bfsBudgetN G M d) : ECost) : WithBot ECost) := by
    intro F₀ st
    rw [prefix_cost_eq_lift, ← liftACost_add, WithBot.coe_le_coe, liftACost_le_iff]
    simpa only [bfsE, bfsBudgetN, distArr_mk, front_mk, level_mk, remWeight_zero]
      using exit_cost_le (i := n + 1) (l := level st) (dd := d)
        (tw := totalWeight G M) (rw := remWeight G M (distArr st) (level st))
  refine gwp_specifies_I ?_
  rw [bfsAlg]
  refine_vcg
  -- the alive branch of the seed's `MIf`
  · exact wfR2_bfsE _
  · rename_i hms
    refine inv_init (List.nodup_singleton s) fun v => ?_
    simp only [List.mem_singleton]
    exact ⟨fun h => ⟨h, h ▸ hms⟩, And.left⟩
  · rename_i _ _ _ hb
    exact (bfsCond_eq_true.mp hb).2
  · rename_i _ st hI hb _ F' hF'
    exact hstep st hI hb F' hF'
  · exact progress_consume cost_level_pos _
  · rename_i _ st hb hI _
    rw [if_pos (post_of_exit hI hb)]
    exact hexit [s] st
  -- the dead branch: the source is never enqueued
  · exact wfR2_bfsE _
  · rename_i hms
    refine inv_init List.nodup_nil fun v => ?_
    constructor
    · intro h; simp at h
    · rintro ⟨rfl, hm⟩; rw [hms] at hm; simp at hm
  · rename_i _ _ _ hb
    exact (bfsCond_eq_true.mp hb).2
  · rename_i _ st hI hb _ F' hF'
    exact hstep st hI hb F' hF'
  · exact progress_consume cost_level_pos _
  · rename_i _ st hb hI _
    rw [if_pos (post_of_exit hI hb)]
    exact hexit [] st

/-! ## The executable gate (design record ledger D4)

`bfsAlg` is `noncomputable` (the whole NREST layer is), so the gate runs
an executable *twin*: the same algorithm with the frontier order fixed.
`nextLevelE_spec` proves that the level the twin picks is one the
abstract program's `SPEC` allows, so the twin's runs are runs of
`bfsAlg`, and the postcondition checked below is `Post` — the
specification's own statement — decided against `Reach`, the naive
level-by-level reachability decider that `reach_iff_WD` proves equal to
`WD`. That is the differential test the campaign asks for: the
specification is checked, not a paraphrase of it. -/

namespace Sanity

open Plausible

/-- The graph of a `Bool` adjacency matrix, symmetrised and made
irreflexive — so *any* sampled matrix is a legal simple graph. -/
def graphOf (A : Fin n → Fin n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => A u v = true

instance instDecidableGraphOfAdj (A : Fin n → Fin n → Bool) : DecidableRel (graphOf A).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The twin's choice of next level: the undiscovered vertices with a
masked neighbour on the frontier, in `finRange` order. -/
def nextLevelE (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool) (d : ℕ)
    (st : State n) : List (Fin n) :=
  (List.finRange n).filter fun v =>
    decide (distArr st v = d + 1 ∧ ∃ u ∈ front st, (masked G M).Adj u v)

/-- **The twin is a run of the abstract program**: its choice satisfies
the `SPEC` the algorithm leaves open. -/
theorem nextLevelE_spec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool)
    (d : ℕ) (st : State n) : NextLevel G M d st (nextLevelE G M d st) := by
  refine ⟨(List.nodup_finRange n).filter _, fun v => ?_⟩
  simp [nextLevelE, List.mem_filter]

/-- The twin's loop: at most `d` iterations, the loop condition of the
abstract program. -/
def bfsIter (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool) (d : ℕ) :
    ℕ → State n → State n
  | 0, st => st
  | (k + 1), st =>
    if bfsCond d st then
      bfsIter G M d k (relax st (nextLevelE G M d st), nextLevelE G M d st, level st + 1)
    else st

@[simp] theorem bfsIter_zero (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool)
    (d : ℕ) (st : State n) : bfsIter G M d 0 st = st := rfl

theorem bfsIter_succ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool)
    (d k : ℕ) (st : State n) :
    bfsIter G M d (k + 1) st =
      if bfsCond d st then
        bfsIter G M d k (relax st (nextLevelE G M d st), nextLevelE G M d st, level st + 1)
      else st := rfl

/-- The executable twin of `bfsAlg`. -/
def bfsRun (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Fin n → Bool) (s : Fin n)
    (d : ℕ) : Fin n → ℕ :=
  distArr (bfsIter G M d d (initDist s d, (if M s then [s] else []), 0))

/-! ### The samples

`RamBfs`'s own demo arena: the path `0—1—2—3` with an isolated vertex
`4`. The three cases the brief names are the three masks/caps below. -/

/-- The path `0—1—2—3`, with `4` isolated. -/
def pathA : Fin 5 → Fin 5 → Bool := fun u v => decide (u.val + 1 = v.val ∧ v.val ≤ 3)

/-- The demo arena. -/
def pathG : SimpleGraph (Fin 5) := graphOf pathA

instance : DecidableRel pathG.Adj := instDecidableGraphOfAdj pathA

/-- Everything alive. -/
def fullM : Fin 5 → Bool := fun _ => true

/-- The mask cuts the path at `2`. -/
def cutM : Fin 5 → Bool := fun v => decide (v.val ≠ 2)

/-- The mask kills the source. -/
def deadM : Fin 5 → Bool := fun v => decide (v.val ≠ 0)

-- the whole path, cap above the diameter: the distances are the path's
#guard List.ofFn (bfsRun pathG fullM 0 4) = [0, 1, 2, 3, 5]
#guard Post pathG fullM 0 4 (bfsRun pathG fullM 0 4)

-- a mask cutting the path: everything beyond `1` reads the sentinel
#guard List.ofFn (bfsRun pathG cutM 0 4) = [0, 1, 5, 5, 5]
#guard Post pathG cutM 0 4 (bfsRun pathG cutM 0 4)

-- a dead source: at distance `0` from itself, and from nothing else
#guard List.ofFn (bfsRun pathG deadM 0 4) = [0, 5, 5, 5, 5]
#guard Post pathG deadM 0 4 (bfsRun pathG deadM 0 4)

-- a cap below the diameter: the far end is truncated, and the
-- postcondition still decides every threshold up to the cap
#guard List.ofFn (bfsRun pathG fullM 0 1) = [0, 1, 2, 2, 2]
#guard Post pathG fullM 0 1 (bfsRun pathG fullM 0 1)

-- the source in the middle, both directions
#guard List.ofFn (bfsRun pathG fullM 2 4) = [2, 1, 0, 1, 5]
#guard Post pathG fullM 2 4 (bfsRun pathG fullM 2 4)

-- negative controls: the gate discriminates
#guard !decide (Post pathG fullM 0 4 fun v => if v.val = 0 then 0 else 1)
#guard !decide (Post pathG fullM 0 4 fun _ => 0)
#guard !decide (Post pathG cutM 0 4 (bfsRun pathG fullM 0 4))

/-! ### The property check

Sampled graphs (an edge list of number pairs, reduced mod `5`), sampled
*dead* sets, sampled source and cap: the specification's postcondition
must hold of the twin's output every time. A failure here is a refuted
specification, which is the point. -/

/-- A sampled adjacency matrix. -/
def adjOfPairs (l : List (ℕ × ℕ)) : Fin 5 → Fin 5 → Bool :=
  fun u v => l.any fun p => decide (p.1 % 5 = u.val ∧ p.2 % 5 = v.val)

/-- A sampled mask, from a sampled *dead* set. -/
def maskOfDead (l : List ℕ) : Fin 5 → Bool := fun v => decide (v.val ∉ l.map (· % 5))

/-- A sampled vertex. -/
def fin5 (k : ℕ) : Fin 5 := ⟨k % 5, Nat.mod_lt _ (by norm_num)⟩

#test ∀ (el : List (ℕ × ℕ)) (dl : List ℕ) (sv dv : ℕ),
  Post (graphOf (adjOfPairs el)) (maskOfDead dl) (fin5 sv) (dv % 5)
    (bfsRun (graphOf (adjOfPairs el)) (maskOfDead dl) (fin5 sv) (dv % 5))

-- and the twin's array never passes the sentinel, whatever is sampled
#test ∀ (el : List (ℕ × ℕ)) (dl : List ℕ) (sv dv : ℕ), ∀ v : Fin 5,
  bfsRun (graphOf (adjOfPairs el)) (maskOfDead dl) (fin5 sv) (dv % 5) v ≤ dv % 5 + 1

end Sanity

end Bfs

end Lax13Proofs.Refine
