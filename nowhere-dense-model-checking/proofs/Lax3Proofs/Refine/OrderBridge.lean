import Lax3Proofs.Refine.ElimSynth6
import Lax3Proofs.RamDriverCompose

/-!
# ND-MC rebase, Integration-B **wave B1** — the ordering phase's bridge

The tower's `R = 0` ordering phase (`Refine.OrderSynth.orderPhase0_le`,
`207n + 30ns + 15W + 169 + 2e`) and its elimination engine
(`Refine.ElimSynth6.elimAvailA_of_engine`, `engineK5 = 333n + 168ns +
45`), brought to the vocabulary `RamDriver.OrderImplements` speaks —
and the one seam that is **not** a transport, named and measured.

## What this file lands

* **B1/B-a** — the list/function transport, both directions, with the
  wrong direction refuted (`arrOf_larr`, `larr_arrOf`).
* **B1/B-b** — `OrderPost`, the tower's answer as a `Prop` about the
  array the phase leaves, and `orderClause_of_orderPost`: the exact
  fifth clause of `RamDriver.OrderImplements`' postcondition, produced
  from it. Plus `ord_lt_of_orderPost`, the clause the *cover* phase then
  asks for (`RamDriver.CoverImplements`' `∀ z < n, ord z < n`).
* **B1/B-c** — `orderPhase0_engine_le`: the phase with the engine
  *plugged in* rather than assumed. This is the composition the swap
  consumes; it is where `engineK5` enters the phase's price.
* **B1/B-d** — the cost flow. `orderTowerK n ns W = 873n + 366ns + 15W
  + 259` is the cashed price of B-c, and it is **below**
  `RamDriverCompose.orderPhaseCost n ns W = 1400n + 1250ns + 20W + 450`,
  which is what `RamDriverRoot.levelAt` threads into the `Ko` slot of
  `RamDriverCluster.levelImplements`. So a swap can keep the root's
  cost instantiation letter for letter.
* **B1/B-e** — `orderSpec_of_towerPost` and `orderImplements_of_spec`:
  the driver-side half of the bridge, discharged. Given a `Spec` at
  *any* command whose postcondition carries `LevelPre`, the three frame
  clauses and `OrderPost` at `ordName j`, `OrderImplements` follows.
* **B1/B-f** — adequacy (§5.1). The transport runs **both** ways
  (`orderPost_of_orderClause`), so the frozen discharger itself can be
  put in the bridge's input shape (`orderImplements₀_towerPost`) and the
  frozen obligation comes back out of it unchanged
  (`orderImplements₀_via_bridge`). That is the compiled evidence that
  `OrderPost` is the right interface Prop and that nothing but the
  program is missing. `RamDriverCompose.orderImplements₀` stands: this
  is a second route to the same statement, not a replacement.

## B1/F-a — THE SEAM: there is no `Com` to bridge to

`OrderImplements B n R W … K` is a `Spec` **at the command
`RamDriver.orderCom R j`**. `BfsBridge`'s P1 template closes such a
gap because the tower's search has a *program*: `BfsQSynth.bfsQ_spec` is
a `Reasoning.Spec` at `Codegen.embed bfsQSynth_impl`, so the bridge is
`bfsSetup` plus a change of vocabulary. The ordering phase has no
counterpart, at either of two levels:

1. **The phase is not one program.** `OrderSynth` §12 (2E/E2) records
   it: the twenty-one passes are `copyPass`/`fillPass`/`ordPass` at
   twenty-one different cell-name sets, and only the *abstract*
   composition `orderPhase0` exists. No `sepref_synth` has been run on
   the phase, so there is no `Ir` program and hence no `Com`.
2. **The engine is not one program either.** `orderPhase0` takes the
   elimination as a hypothesis `ElimAvailA` (2E/D-a) precisely because
   satellite 2B′ synthesized the five passes separately and never
   assembled them. `ElimSynth6.elimProgram` — the witness B-c plugs in
   — is an `NRest` program built from `elimEngine5`, and of its five
   phases only the elimination *loop* is registered as a synthesizable
   leaf (`OrderSynth.mopElim`, §9).

Consequently a `Spec`-level discharge of `OrderImplements` is **not** a
thin transport in either shape available:

* *as a re-proof at the frozen program* — impossible in principle: a
  synthesized program is a different command from `orderCom R j`, and
  no lemma relates two commands' `Spec`s except by proving one of them;
* *as a swap* — possible, and it is the honest route, but it needs the
  two assemblies above (a whole-phase synthesis over fifteen array
  arguments, and the engine's five passes assembled into one leaf), and
  then a `RamDriver.orderCom` text change. That is B3/B4 scale, not B1.

What B1 therefore delivers is the bridge minus its missing input,
compiled: **every** clause of `OrderImplements` except the identity of
the program is discharged from the tower's export here (B-e), the
engine's cost is shown to flow into the frozen `Ko` slot with room to
spare (B-d), and the two vocabulary transports the export needs are
proved and refuted (B-a, B-b). The remainder is stated exactly:

> `∃ c : Com, Spec B (LevelPre …) c (fun σ σ' => LevelPre … ∧
> σ'.out = σ.out ∧ (∀ a, σ'.vars (ctrName a) = σ.vars (ctrName a)) ∧
> (∀ a, σ'.arrs (gamName a) = σ.arrs (gamName a)) ∧
> OrderPost n (σ'.arrs (ordName j))) (orderTowerK n ns W)`
>
> with `c` the lowering of `orderPhase0` at
> `ElimSynth6.elimProgram` — and then `orderCom R j := c`.

`orderImplements_of_spec` is that statement's consumer, at the frozen
command; `orderSpec_of_towerPost` is the same reasoning at an arbitrary
command, which is what the swap wave will call.

## House traps observed

`larr`/`arrOf` is the classic wrong-direction hazard and carries a
negative control in both directions (§1); the ranks-versus-order
confusion carries the demo control (§5); the cost figures are
`#guard`ed, including the control that shows the engine's price is
really in the total.
-/

namespace Lax3Proofs.Refine.OrderBridge

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning (Spec arrOf length_arrOf)
open Lax13Proofs.Refine
open Lax3Proofs.Refine.ElimSynth2 (larr larr_apply)
open Lax3Proofs.Refine.OrderSynth (orderPhase0 orderPhase0C orderPhase0K)
open Lax3Proofs.Refine.ElimSynth6 (elimProgram engineC5 engineK5)

/-! ## 1. B1/B-a — the list and the function array

The tower states its answer as a `List ℕ` and reads it with
`ElimSynth2.larr` (`getElem!`); the driver stack holds arrays as
`Lax13Proofs.Reasoning.arrOf` of a function. The two are inverse **only
under the length hypothesis**, and only in one of the two directions
unconditionally — which is the whole content of the transport. -/

/-- **The array of the reading is the list.** At the list's own length,
`arrOf` undoes `larr`. -/
theorem arrOf_larr {n : ℕ} {L : List ℕ} (h : L.length = n) : arrOf n (larr L) = L := by
  refine List.ext_getElem (by rw [length_arrOf, h]) fun i h₁ h₂ => ?_
  rw [Lax13Proofs.Reasoning.Lib.getElem_arrOf, larr_apply, getElem!_pos L i h₂]

/-- **The reading of the array is the function — below the length.**
Above it there is nothing to read, which is why every use of this
direction carries its range condition. -/
theorem larr_arrOf {n i : ℕ} (f : ℕ → ℕ) (h : i < n) : larr (arrOf n f) i = f i := by
  rw [larr_apply, getElem!_pos (arrOf n f) i (by rw [length_arrOf]; exact h),
    Lax13Proofs.Reasoning.Lib.getElem_arrOf]

/-! ### Refutation (B1/B-a)

Both directions can be got wrong, and both wrong readings are refuted by
`#guard`s the build runs. -/

section RefuteTransport

-- **the length hypothesis is load-bearing**: at the right length the
-- round trip is the identity …
#guard arrOf 3 (larr [4, 5, 6]) == [4, 5, 6]
-- … at a longer claimed length the array cannot be the list, on the
-- lengths alone, and the cell the extra index would read is not there …
#guard ! ((arrOf 3 (larr [4, 5, 6])).length == [4, 5].length)
#guard [4, 5][2]? == none
-- … and at a shorter one the tail is lost.
#guard arrOf 2 (larr [4, 5, 6]) == [4, 5]
#guard ! (arrOf 2 (larr [4, 5, 6]) == [4, 5, 6])

-- **the other direction is a prefix statement**: inside the array the
-- reading is the function …
#guard (List.range 3).all fun i => larr (arrOf 3 (fun z => z + 7)) i == i + 7
-- … and one past the end there is nothing to read, so the reading is
-- the fall-through and not the function.
#guard (arrOf 3 (fun z => z + 7))[3]? == none
#guard ! ((arrOf 3 (fun z => z + 7))[3]? == some (3 + 7))

end RefuteTransport

/-! ## 2. B1/B-b — the phase's answer, as the driver reads it -/

/-- **What the tower's phase leaves**, verbatim from
`OrderSynth.orderPhase0_le`'s postcondition: an array of the carrier's
length that orders *some* permutation. -/
def OrderPost (n : ℕ) (L : List ℕ) : Prop :=
  L.length = n ∧ ∃ π : Equiv.Perm (Fin n), RamCover.OrdersBy n π (larr L)

/-- **The fifth clause of `RamDriver.OrderImplements`, produced.** The
driver asks for a *function* array and an ordering of it; the tower
delivers a list and an ordering of its reading, and B-a is the only step
between them. -/
theorem orderClause_of_orderPost {n : ℕ} {a : String} {σ' : Env} {L : List ℕ}
    (hL : OrderPost n L) (hσ : σ'.arrs a = L) :
    ∃ (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ),
      σ'.arrs a = arrOf n ord ∧ RamCover.OrdersBy n π ord := by
  obtain ⟨hlen, π, hπ⟩ := hL
  exact ⟨π, larr L, by rw [hσ, arrOf_larr hlen], hπ⟩

/-- **The same clause, back.** The two vocabularies are *equivalent*,
not merely one-directional: a function array with an ordering is a list
with an ordering of its reading. This is what says the bridge loses
nothing — and it is what lets §5.1 run the frozen discharger through
the bridge and get the frozen obligation back. -/
theorem orderPost_of_orderClause {n : ℕ} {L : List ℕ} {π : Equiv.Perm (Fin n)}
    {ord : ℕ → ℕ} (hL : L = arrOf n ord) (h : RamCover.OrdersBy n π ord) :
    OrderPost n L := by
  subst hL
  exact ⟨length_arrOf _ _, π, fun v => by rw [larr_arrOf ord (π v).isLt]; exact h v⟩

/-- **And the clause the cover phase asks for next.**
`RamDriver.CoverImplements` takes `∀ z < n, ord z < n` beside the
ordering; it is `RamCover.OrdersBy.lt`, and it is recorded here so the
swap wave does not re-derive it. -/
theorem ord_lt_of_orderPost {n : ℕ} {L : List ℕ} (hL : OrderPost n L) :
    ∀ z < n, larr L z < n := fun _ hz => hL.2.choose_spec.lt hz

/-! ## 3. B1/B-c — the phase with the engine plugged in

`OrderSynth.orderPhase0_le` takes the elimination as a hypothesis;
`ElimSynth6.elimAvailA_of_engine` is a witness for that hypothesis at a
block structure. Composing them is the *one* place in this file where
the two towers meet, and it is a single term. -/

section Composed

open Lax13Proofs.Refine.NRest

variable {n ns W : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}

/-- **The ordering phase at `R = 0`, engine included.** No hypothesis is
left about the elimination: the five-phase engine of `ElimSynth6` is the
program the phase calls, and the price is the phase's twenty-one passes
plus **two** engines. -/
theorem orderPhase0_engine_le (hcsr : RamElim.CsrSimple G ns O T) (hW : ns ≤ W)
    {deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀ : List ℕ}
    (hdeg : deg₀.length = n) (helm : elm₀.length = n) (helm0 : ∀ v < n, elm₀[v]! = 0)
    (hrnk : rnk₀.length = n) (hidg : idg₀.length = n)
    (hbh : bh₀.length = n + 1) (hbh0 : ∀ j ≤ n, bh₀[j]! = 0)
    (hbv : bv₀.length = n + W + 1) (hbn : bn₀.length = n + W + 1)
    (hio : ioff₀.length = n + 1) (hio0 : ioff₀[0]! = 0) (hifl : ifl₀.length = n)
    (hitg : itg₀.length = W)
    {gof gtg alvj alv doff dtg ooff noff stf sta std ste ord : List ℕ}
    (hgof : gof.length = n + 1) (hgtg : gtg.length = ns) (halvj : alvj.length = n)
    (halv : alv.length = n) (hdoff : doff.length = n + 1) (hdtg : dtg.length = W)
    (hooff : ooff.length = n + 1) (hnoff : noff.length = n + 1) (hstf : stf.length = n)
    (hsta : sta.length = n) (hstd : std.length = n) (hste : ste.length = n)
    (hord : ord.length = n) :
    orderPhase0 n ns W
        (fun _ _ _ => elimProgram n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M)
          deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀)
        (arrOf (n + 1) O) (arrOf ns T) gof gtg alvj alv doff dtg ooff noff stf sta std
        ste ord
      ≤ NRest.spec (OrderPost n)
          (fun _ => liftACost (orderPhase0C n ns W (engineC5 n ns))) :=
  OrderSynth.orderPhase0_le
    (ElimSynth6.elimAvailA_of_engine hcsr hW hdeg helm helm0 hrnk hidg hbh hbh0 hbv hbn
      hio hio0 hifl hitg)
    (length_arrOf _ _) (length_arrOf _ _) hgof hgtg halvj halv hdoff hdtg hooff hnoff
    hstf hsta hstd hste hord

end Composed

/-! ## 4. B1/B-d — the cost, and where it goes

`RamDriverRoot.levelAt` threads `RamDriverCompose.orderPhaseCost n ns W`
into the `Ko` slot of `RamDriverCluster.levelImplements` (its `hKl` side
condition names it literally). So the question the swap has to answer is
not "what does the tower phase cost" but "does it fit in the slot the
frozen root already pays for". It does, with room. -/

section Cash

/-- **The composed phase's price**: `orderPhase0K` at `engineK5`,
multiplied out. Seven prefix copies, eleven prefix fills, one rank
inversion, nineteen loop entries and **two** five-phase eliminations. -/
def orderTowerK (n ns W : ℕ) : ℕ := 873 * n + 366 * ns + 15 * W + 259

/-- The phase's own figure at the engine's, multiplied out. -/
theorem orderPhase0K_engine (n ns W : ℕ) :
    orderPhase0K n ns W (engineK5 n ns) = orderTowerK n ns W := by
  rw [orderPhase0K, engineK5, orderTowerK]; ring

theorem cash_orderPhase0C_engine (n ns W : ℕ) :
    Codegen.cash (orderPhase0C n ns W (engineC5 n ns)) = orderTowerK n ns W := by
  rw [OrderSynth.cash_orderPhase0C, ElimSynth6.cash_engine5Budget, orderPhase0K_engine]

/-- **The cost flow into `Ko`.** The tower's ordering phase — engine
included — costs strictly less than the budget the frozen root already
instantiates `Ko` with, at every size. A swap therefore needs no change
to `RamDriverRoot.levelAt`, to `hKl`, or to `CostRecurrence`'s witness:
`Spec.mono` absorbs the difference. -/
theorem orderTowerK_le_orderPhaseCost (n ns W : ℕ) :
    orderTowerK n ns W ≤ RamDriverCompose.orderPhaseCost n ns W := by
  rw [orderTowerK, RamDriverCompose.orderPhaseCost]; omega

/-- The same fact as the driver stack will use it: an `OrderImplements`
at the tower's price is one at the frozen budget. -/
theorem orderImplements_mono {B n R W cap mb ns j K K' : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {P : Equiv.Perm (Fin n) → (ℕ → ℕ) → Prop}
    (h : RamDriver.OrderImplements B n R W cap mb ns j G O T M Gm C P K) (hK : K ≤ K') :
    RamDriver.OrderImplements B n R W cap mb ns j G O T M Gm C P K' :=
  fun hB hcsr hWB helim haug => (h hB hcsr hWB helim haug).mono hK

-- the two figures at the demo's size, and the frozen budget beside them
#guard orderTowerK 5 10 10 = 8434
#guard RamDriverCompose.orderPhaseCost 5 10 10 = 22750
#guard orderTowerK 5 10 10 ≤ RamDriverCompose.orderPhaseCost 5 10 10

/-! ### Negative controls (B1/B-d)

The claim is a `≤`, so what falsifies it is a price that is too small —
and the one way to make it too small is to forget that the phase runs
the engine **twice**. -/

-- **(a) the engine's price is really in the total.** The phase's own
-- twenty-one passes, at a free engine, are a sixth of the figure.
#guard orderPhase0K 5 10 10 0 = 1654
#guard ! (orderTowerK 5 10 10 ≤ orderPhase0K 5 10 10 0)

-- **(b) it is two engines, not one.** One would leave the total 3 390
-- short, and the check can tell.
#guard orderTowerK 5 10 10 - orderPhase0K 5 10 10 0 = 2 * engineK5 5 10
#guard ! (orderTowerK 5 10 10 = orderPhase0K 5 10 10 0 + engineK5 5 10)

-- **(c) the fit is not vacuous.** The margin in `n` is 873 against
-- 1 600 (rebase F-c-2 raised the budget by the symmetrization's
-- `200·n + 100·ns + 200`); on an instance with no slots at all a phase
-- twice as dear per
-- vertex does **not** fit the same budget, so the inequality has
-- content and is not an artefact of the budget's generosity in `ns`.
#guard ! (2 * 873 * 1000 + 259 ≤ RamDriverCompose.orderPhaseCost 1000 0 0)
#guard orderTowerK 1000 0 0 ≤ RamDriverCompose.orderPhaseCost 1000 0 0

end Cash

/-! ## 5. B1/B-e — the driver-side half, discharged

`RamDriver.OrderImplements`' postcondition has five clauses. Four of
them — `LevelPre` back, the output stream, the connectors, the game
masks — are frame facts a program either has or does not, and they are
carried unchanged; the fifth is the tower's answer, and §2 is the
translation. What the two lemmas below do is fix that seam once, so the
wave that supplies the program supplies *only* the program. -/

section DriverSide

variable {B n cap mb ns W j K : ℕ} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}

open RamDriver (LevelPre ctrName gamName ordName)

/-- **The postcondition transport, at an arbitrary command.** This is
the form the *swap* wave calls: it says nothing about which program the
phase is, only that a program leaving `OrderPost` at `ordName j` leaves
what the obligation asks for. -/
theorem orderSpec_of_towerPost {c : Com}
    (h : Spec B (fun σ => LevelPre B n cap mb ns W O T j M Gm C σ) c
      (fun σ σ' => LevelPre B n cap mb ns W O T j M Gm C σ' ∧ σ'.out = σ.out ∧
        (∀ a : ℕ, σ'.vars (ctrName a) = σ.vars (ctrName a)) ∧
        (∀ a : ℕ, σ'.arrs (gamName a) = σ.arrs (gamName a)) ∧
        OrderPost n (σ'.arrs (ordName j))) K) :
    Spec B (fun σ => LevelPre B n cap mb ns W O T j M Gm C σ) c
      (fun σ σ' => LevelPre B n cap mb ns W O T j M Gm C σ' ∧ σ'.out = σ.out ∧
        (∀ a : ℕ, σ'.vars (ctrName a) = σ.vars (ctrName a)) ∧
        (∀ a : ℕ, σ'.arrs (gamName a) = σ.arrs (gamName a)) ∧
        ∃ (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ),
          σ'.arrs (ordName j) = arrOf n ord ∧ RamCover.OrdersBy n π ord ∧ True) K :=
  h.post fun _ _ _ hq => by
    refine ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, ?_⟩
    obtain ⟨π, ord, h₁, h₂⟩ := orderClause_of_orderPost hq.2.2.2.2 rfl
    exact ⟨π, ord, h₁, h₂, trivial⟩

/-- **`RamDriver.OrderImplements`, from the tower's phase
postcondition.** Everything the obligation asks for, discharged from a
`Spec` in the tower's own vocabulary — at the frozen command, so that
the only thing this theorem still wants is the lowering named in the
header's F-a. -/
theorem orderImplements_of_spec {R : ℕ} {G : SimpleGraph (Fin n)}
    (h : ∀ {d : ℕ}, RamDriver.WordBoundK B n d ns cap mb → RamElim.CsrSimple G ns O T →
      n + W + 1 < B →
      RamDriver.ElimAvail B n → RamDriver.AugAvail B n →
      Spec B (fun σ => LevelPre B n cap mb ns W O T j M Gm C σ)
        (RamDriver.orderCom R j)
        (fun σ σ' => LevelPre B n cap mb ns W O T j M Gm C σ' ∧ σ'.out = σ.out ∧
          (∀ a : ℕ, σ'.vars (ctrName a) = σ.vars (ctrName a)) ∧
          (∀ a : ℕ, σ'.arrs (gamName a) = σ.arrs (gamName a)) ∧
          OrderPost n (σ'.arrs (ordName j))) K) :
    RamDriver.OrderImplements B n R W cap mb ns j G O T M Gm C (fun _ _ => True) K :=
  fun hB hcsr hWB helim haug => orderSpec_of_towerPost (h hB hcsr hWB helim haug)

/-! ### 5.1 Adequacy — the bridge, run on the only discharger there is

`orderImplements_of_spec` is worth exactly as much as the shape of the
`Spec` it asks for. The check that the shape is the right one is to
produce it from the *hand-walked* phase, which does have a program, and
to see the frozen obligation come back out unchanged. It does — so the
bridge's input Prop is adequate, and the only thing separating the
tower from `RamDriver.OrderImplements` is B1/F-a's missing lowering,
not a mismatch of vocabulary.

`RamDriverCompose.orderImplements₀` is **not** superseded here: this is
a second route to the same statement, which is what the wave was asked
to build. -/

section Adequacy

/-- **The hand-walked phase, in the tower's vocabulary.** Its
postcondition's ordering clause, read back as `OrderPost`. -/
theorem orderImplements₀_towerPost {B cap mb ns W j : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} :
    ∀ {d : ℕ}, RamDriver.WordBoundK B n d ns cap mb → RamElim.CsrSimple G ns O T →
    n + W + 1 < B → RamDriver.ElimAvail B n → RamDriver.AugAvail B n →
    Spec B (fun σ => RamDriver.LevelPre B n cap mb ns W O T j M Gm C σ)
      (RamDriver.orderCom 0 j)
      (fun σ σ' => RamDriver.LevelPre B n cap mb ns W O T j M Gm C σ' ∧ σ'.out = σ.out ∧
        (∀ a : ℕ, σ'.vars (RamDriver.ctrName a) = σ.vars (RamDriver.ctrName a)) ∧
        (∀ a : ℕ, σ'.arrs (RamDriver.gamName a) = σ.arrs (RamDriver.gamName a)) ∧
        OrderPost n (σ'.arrs (RamDriver.ordName j)))
      (RamDriverCompose.orderPhaseCost n ns W) := by
  intro d hB hcsr hWB helim haug
  refine (RamDriverCompose.orderImplements₀ hB hcsr hWB helim haug).post ?_
  rintro σ σ' - ⟨h1, h2, h3, h4, π, ord, hord, hOrd, -⟩
  exact ⟨h1, h2, h3, h4, orderPost_of_orderClause hord hOrd⟩

/-- **The frozen obligation, through the bridge.** Identical statement
to `RamDriverCompose.orderImplements₀`, obtained by handing
`orderImplements_of_spec` the tower-shaped postcondition. -/
theorem orderImplements₀_via_bridge {B cap mb ns W j : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} :
    RamDriver.OrderImplements B n 0 W cap mb ns j G O T M Gm C (fun _ _ => True)
      (RamDriverCompose.orderPhaseCost n ns W) :=
  orderImplements_of_spec orderImplements₀_towerPost

end Adequacy

end DriverSide

/-! ### Refutation (B1/B-b, B1/B-e)

The transport's hazard is the *direction* of the ordering: `OrdersBy n
π ord` says `ord (π v) = v` — the array is the rank map's **inverse**,
not the rank map. `OrderSynth` §1 pins the demo's two arrays against
`RamElim.Demo`'s published ranks; the controls below are the same data
read through the clause this file produces.

The second hazard is the elimination's own postcondition. `ElimPost`
asks the ranks to be positions and to be injective; drop injectivity and
the inversion silently leaves a cell no vertex ever wrote, so the array
is not an ordering of anything and `OrderPost` is false of it — the
`ElimOut` mismatch the wave's falsification gate names. -/

section RefuteOrder

/-- The demo's ranks with the mask off at vertex `2`, and their
inversion, as `OrderSynth` §1 pins them. -/
private def dRnk : List ℕ := [0, 1, 4, 2, 3]
private def dOrd : List ℕ := [0, 1, 3, 4, 2]

/-- `OrdersBy`'s clause, made decidable at a concrete size: the array
sends the position a vertex occupies back to the vertex. -/
private def ordersByAt (n : ℕ) (rnk ordA : List ℕ) : Bool :=
  (List.range n).all fun v => ordA[rnk[v]!]! == v

-- **the inversion orders the ranks** …
#guard ordersByAt 5 dRnk dOrd
-- … and the ranks do **not** order themselves: a bridge that took the
-- rank array for the order array is refuted on this instance.
#guard ! ordersByAt 5 dRnk dRnk
#guard dOrd ≠ dRnk

/-- `ElimPost`'s two rank clauses, made decidable: positions, and no two
vertices at one position. -/
private def ranksOk (n : ℕ) (rnk : List ℕ) : Bool :=
  ((List.range n).all fun v => decide (rnk[v]! < n)) &&
    ((List.range n).all fun v => (List.range n).all fun w =>
      decide (rnk[v]! = rnk[w]!) == decide (v = w))

-- **the demo's ranks meet `ElimPost`** …
#guard ranksOk 5 dRnk
-- … and a rank array naming position `1` twice does not …
#guard ! ranksOk 3 [1, 1, 0]
-- … and the phase's answer on it is not an ordering: position `2` is
-- never written, so the array holds the caller's junk and `OrderPost`'s
-- permutation cannot exist.
#guard OrderSynth.ordRun 3 [1, 1, 0] [9, 9, 9] == [2, 1, 9]
#guard ! ((List.range 3).all fun z => decide ((OrderSynth.ordRun 3 [1, 1, 0] [9, 9, 9])[z]! < 3))
-- the same array from a *good* rank array is a permutation of the
-- carrier, so the control separates the two cases and is not vacuous
#guard (List.range 5).all fun z => decide ((OrderSynth.ordRun 5 dRnk (List.replicate 5 0))[z]! < 5)

end RefuteOrder

/-! ## 6. Axioms -/

/-- info: 'Lax3Proofs.Refine.OrderBridge.orderPhase0_engine_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms orderPhase0_engine_le

/-- info: 'Lax3Proofs.Refine.OrderBridge.orderClause_of_orderPost' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms orderClause_of_orderPost

/-- info: 'Lax3Proofs.Refine.OrderBridge.orderImplements_of_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms orderImplements_of_spec

/-- info: 'Lax3Proofs.Refine.OrderBridge.orderTowerK_le_orderPhaseCost' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms orderTowerK_le_orderPhaseCost

/-- info: 'Lax3Proofs.Refine.OrderBridge.orderPost_of_orderClause' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms orderPost_of_orderClause

/-- info: 'Lax3Proofs.Refine.OrderBridge.orderImplements₀_via_bridge' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms orderImplements₀_via_bridge

end Lax3Proofs.Refine.OrderBridge
