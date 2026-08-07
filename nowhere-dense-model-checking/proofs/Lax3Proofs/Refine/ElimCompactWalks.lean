import Lax3Proofs.Refine.ElimCompact

/-!
# ND-MC E2-sat — the compacted engine's two walks, and the weight tie

`Refine/ElimCompact.lean` §8 leaves two named obligation `Prop`s and one
arithmetic tie; this satellite is all three, in the campaign's
obligation-Props discipline (state once, refute on data, discharge in a
satellite, never restate).

* §1 is the **weight tie** the parent file's §9 hands to E5: the
  compacted arena's own weight is the level arena's weight, a `wsum`
  transported along `memEmb`. It is a `MassWeight` fact and nothing in
  it mentions a program.
* §2 discharges **`ScatterBacks`** — `scatterCom` sends the compact rank
  of member `j` to the arena cell `ork[mem j]` and touches nothing else.
* §3 is the **cost finding on `CompactInstalls`**, compiled. The frozen
  `Prop` charges the compaction at `compactCost mm cs` with `cs` the
  *live* slot count of the member pullback, while `cRow` walks the
  member's **raw** row in the level CSR. Where a member's row lists dead
  vertices the two diverge, and §3.1 exhibits an instance on which the
  clock exceeds the budget — so that clause of `CompactInstalls` is
  false as stated. §3.2 names the true charge (`compactCostRaw`, at the
  raw member-row sum) and §3.3 identifies it with the arena's `csrW`
  weight, which is what `MassWeight` keeps a second weight reading for.
* §4 discharges `cixPass`, the compaction's first half — the *same*
  member walk as the scatter, as `ElimCompact` §9(3) predicts. The nested
  CSR construction `compactCsr` is `Refine/ElimCompactCsr.lean`.
* §5 is the ledger: what is done, what was refuted, and where each
  repair landed — including the one in the engine's own landed export,
  where `RamElim.ElimPost` dropped the rank bound the scatter needs.

Nothing here is `sorry`, and no theorem below assumes an unproved
obligation.
-/

namespace Lax3Proofs.Refine.ElimCompactWalks

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamBfs (masked masked_adj)
open Lax3Proofs.RamDriver (copyUpto fillUpto)
open Lax3Proofs.RamDriverCluster (markSet mem_markSet)
open Lax3Proofs.Refine.ScatterBlock (MemList MemOf)
open Lax3Proofs.Refine.MassWeight (wsum graphW vdeg arenaWeight csrW)
open Lax3Proofs.Refine.ElimCompact (memEmb memEmb_injective memGraph memGraph_adj
  scatterCom scatterCost ScatterBacks ScatterBacksW memRowSum compactCostRaw)

/-! ## §1 The weight tie

`ElimCompact` §6 bounds the composite's clock by the *compacted* arena's
weight (`elimCompactCost_le_arenaWeight`, at `MassWeight.arenaWeight_root`
of the compact graph). What the G2 interface budgets in is the **level**
arena's weight. The two are the same number, and the reason is that
`memEmb` is a bijection from the compact carrier onto the arena's mark
set which preserves degrees — a member's compact neighbours are exactly
its live neighbours, because the members *are* the live vertices.

This is a `MassWeight` lemma: no program, no store, no cost. -/

variable {n mm : ℕ} {G : SimpleGraph (Fin n)} {M Mem : ℕ → ℕ}

/-- **The member embedding lands in the arena.** -/
theorem memEmb_mem_markSet (hml : MemList n mm Mem (markSet n M)) (i : Fin mm) :
    memEmb hml i ∈ markSet n M := by
  obtain ⟨h, hmem⟩ := hml.sound (i : ℕ) i.isLt
  have : (⟨Mem (i : ℕ), h⟩ : Fin n) = memEmb hml i := Fin.ext rfl
  rwa [this] at hmem

/-- **…and onto it.** Every live vertex is a member, so it is some
compact vertex's image. This is `MemList.complete`, in `Fin` form. -/
theorem exists_memEmb_eq (hml : MemList n mm Mem (markSet n M)) {v : Fin n}
    (hv : v ∈ markSet n M) : ∃ i : Fin mm, memEmb hml i = v := by
  obtain ⟨j, hj, hMj⟩ := hml.complete (v : ℕ) ⟨v.isLt, by simpa using hv⟩
  exact ⟨⟨j, hj⟩, Fin.ext hMj⟩

/-- **The compact neighbourhood is the arena neighbourhood, renumbered.**
The forward inclusion is `memGraph_adj`; the reverse is where the
member list does the work — an arena-neighbour of a member is *alive*
(`masked_adj`'s third clause), hence a member, hence listed. -/
theorem image_nbr_memEmb (hml : MemList n mm Mem (markSet n M)) (i : Fin mm) :
    (memEmb hml) '' {j : Fin mm | (memGraph G M hml).Adj i j} =
      {u : Fin n | (masked G M).Adj (memEmb hml i) u} := by
  ext u
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact memGraph_adj.1 hj
  · intro hu
    have hlive : u ∈ markSet n M := mem_markSet.2 (masked_adj.1 hu).2.2
    obtain ⟨j, rfl⟩ := exists_memEmb_eq hml hlive
    exact ⟨j, memGraph_adj.2 hu, rfl⟩

/-- **Compaction preserves degrees.** -/
theorem vdeg_memGraph (hml : MemList n mm Mem (markSet n M)) (i : Fin mm) :
    vdeg (memGraph G M hml) i = vdeg (masked G M) (memEmb hml i) := by
  rw [vdeg, vdeg, ← image_nbr_memEmb hml i,
    Set.ncard_image_of_injective _ (memEmb_injective hml)]

/-- …hence weights. -/
theorem graphW_memGraph (hml : MemList n mm Mem (markSet n M)) (i : Fin mm) :
    graphW (memGraph G M hml) i = graphW (masked G M) (memEmb hml i) := by
  rw [graphW, graphW, vdeg_memGraph]

/-- **A weight transported along the member list.** The general form: any
weight on the carrier, summed over the arena's mark set, is its pullback
summed over the whole compact carrier. `memEmb` is injective by
`MemList.smono` and onto the mark set by `MemList.complete`, so this is
one `Finset.sum_bij`. -/
theorem wsum_markSet_eq (hml : MemList n mm Mem (markSet n M)) (f : Fin n → ℕ) :
    wsum f (markSet n M) = ∑ i : Fin mm, f (memEmb hml i) := by
  classical
  refine (Finset.sum_bij (i := fun (i : Fin mm) _ => memEmb hml i) ?_ ?_ ?_ ?_).symm
  · exact fun i _ => Lax3Proofs.Refine.MassWeight.mem_wsumFinset.2 (memEmb_mem_markSet hml i)
  · exact fun i _ j _ h => memEmb_injective hml h
  · intro v hv
    obtain ⟨i, hi⟩ :=
      exists_memEmb_eq hml (Lax3Proofs.Refine.MassWeight.mem_wsumFinset.1 hv)
    exact ⟨i, Finset.mem_univ i, hi⟩
  · exact fun _ _ => rfl

/-- **The tie.** The compacted arena's own weight — read at the constant
all-alive mask, which is what compaction leaves (`ElimCompact`'s
`masked_of_all_alive`) — is the level arena's weight. So
`ElimCompact.elimCompactCost_le_arenaWeight`, which bounds the composite's
clock by `800 · arenaWeight mm (memGraph …) 1 + 300`, is a bound in the
number the G2 interface budgets in, with no carrier term and no second
weight vocabulary.

E5/E6 consume this direction; the reverse is the same statement read
right to left. -/
theorem arenaWeight_memGraph (hml : MemList n mm Mem (markSet n M)) :
    arenaWeight mm (memGraph G M hml) (fun _ => 1) = arenaWeight n (masked G M) M := by
  have hset : {v : Fin mm | (1 : ℕ) ≠ 0} = (Set.univ : Set (Fin mm)) :=
    Set.eq_univ_of_forall fun _ => one_ne_zero
  rw [Lax3Proofs.Refine.MassWeight.arenaWeight_eq_markSet,
    Lax3Proofs.Refine.MassWeight.arenaWeight_eq_markSet, wsum_markSet_eq hml]
  show wsum (graphW (memGraph G M hml)) {v : Fin mm | (1 : ℕ) ≠ 0} = _
  rw [hset, Lax3Proofs.Refine.MassWeight.wsum_univ]
  exact Finset.sum_congr rfl fun i _ => graphW_memGraph hml i

/-- The same tie in the `1`-as-a-function spelling `ElimCompact` §9
writes it in. -/
theorem arenaWeight_memGraph' (hml : MemList n mm Mem (markSet n M)) :
    arenaWeight mm (memGraph G M hml) 1 = arenaWeight n (masked G M) M :=
  arenaWeight_memGraph hml

/-! ## §2 The scatter walk

`scatterCom` sends the compact rank of member `j` to the arena cell
`ork[mem j]`. The walk itself is one `forRangeZero'` at the member
counter and nothing else; what this section had to find first is that the
frozen `Prop` of `ElimCompact` §8 is **not** what the walk proves. -/

/-! ### §2.1 The frozen `Prop` is false: the member list must be
repetition-free

`ScatterBacks` asks only that every listed entry be a vertex
(`∀ j < mm, Mem j < n`). It does not ask that the list be
repetition-free — and the conclusion it states is a *pointwise* reading
of a single arena cell, `ork[Mem j] = R j` for every member `j`. Two
members at the same arena number with different ranks therefore ask one
cell to hold two values, and no state satisfies the conclusion, whatever
program is run.

The instance is minimal: one arena vertex, two list entries at it, and
the two ranks `0` and `1`. -/

/-- The store the refutation runs in: one arena cell, and a rank array
holding `0` and `1`. -/
def repeatSt : Env :=
  { vars := fun _ => 2
    arrs := fun a => if a = "rnk" then [0, 1] else [0]
    inp := []
    out := [] }

/-- **The refutation.** `ScatterBacks` is false at a member list that
repeats: its conclusion asks `ork[0]` to be `0` and `1` at once. No run
is inverted here — the *postcondition* is unsatisfiable, so the defect is
in the statement and not in the program. -/
theorem not_scatterBacks_of_repeat : ¬ ScatterBacks 100 1 2 (fun _ => 0) := by
  intro h
  obtain ⟨σ', -, hork, -, -, -⟩ :=
    h (fun j => j) repeatSt rfl (by decide) (fun _ _ => Nat.zero_lt_one)
      (by decide) ⟨fun _ => 0, by decide⟩
  have h0 := hork 0 (by omega)
  have h1 := hork 1 (by omega)
  rw [h0] at h1
  exact absurd h1 (by omega)

/-! ### §2.2 The obligation, repaired

Four clauses are added and **nothing in the conclusion changes**: the
`Prop` below has `ScatterBacks`'s conclusion verbatim.

* `hsm` — the list is strictly increasing, hence repetition-free. This
  is `MemList.smono`, which the caller (`elimCompact_spec`) already
  holds; §2.1 is the compiled proof that it cannot be dropped.
* `hnB` — the carrier fits in a word. Every landed specification of the
  package carries a clause of this shape (`RamElim.elim_specW`'s
  `hB`); without it neither the loop test nor the `mem` read evaluates,
  and `Run` is a *derivation*, so the conclusion fails vacuously.
* `hRB`, `hρlen` — the ranks are readable: `scatterCom` reads `rnk[km]`
  with an IMP+ `get`, which needs the cell to exist and to hold a word.
  The frozen `getD` clause gives neither (it is satisfied by the empty
  array at `R = 0`).

`hsm` and `hnB` are the two the caller supplies for free; `hRB` is
`RamElim.RnkLt`, which E2-fold threaded back through the engine's
landed export (§5).

The repaired `Prop` itself lives in `ElimCompact` §8, next to the
reading it supersedes, so that the two sibling compacted engines read one
obligation; this section discharges it. -/

/-! ### §2.3 The walk -/

/-- A strictly increasing list of vertices is no longer than the
carrier — `MemList.card_le`'s argument off the bare monotonicity clause,
which is all `ScatterBacksW` carries. -/
theorem le_of_smono {mm : ℕ} {Mem : ℕ → ℕ}
    (hsm : ∀ i j, i < j → j < mm → Mem i < Mem j) {j : ℕ} (hj : j < mm) : j ≤ Mem j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have h₁ := hsm k (k + 1) (by omega) hj
      have h₂ := ih (by omega)
      omega

theorem card_le_of_smono {n mm : ℕ} {Mem : ℕ → ℕ}
    (hsm : ∀ i j, i < j → j < mm → Mem i < Mem j) (hlt : ∀ j, j < mm → Mem j < n) : mm ≤ n := by
  rcases Nat.eq_zero_or_pos mm with rfl | hpos
  · exact Nat.zero_le _
  · have h1 : mm - 1 < mm := by omega
    have := le_of_smono hsm h1
    have := hlt (mm - 1) h1
    omega

/-- **The scatter loop's invariant.** After `km` members the arena cells
of those members hold their ranks; the member list, the count and the
rank array are the ones the walk entered with. -/
def ScatInv (n mm : ℕ) (Mem R : ℕ → ℕ) (ρ : List ℕ) (σ : Env) : Prop :=
  σ.vars "mm" = mm ∧ σ.arrs "mem" = arrOf n Mem ∧ σ.arrs "rnk" = ρ ∧ σ.vars "km" ≤ mm ∧
    ∃ Ork, σ.arrs "ork" = arrOf n Ork ∧ ∀ j, j < σ.vars "km" → Ork (Mem j) = R j

/-- **One member scattered.** Read the arena number, store the rank
there, step the counter: eleven ticks, and the invariant grows by one
member. The one place the member list's sortedness is used is the
`upd_of_ne` below — an earlier member's cell is a *different* cell. -/
theorem scatBody_spec {B n mm : ℕ} {Mem R : ℕ → ℕ} {ρ : List ℕ}
    (hnB : n < B) (hMlt : ∀ j, j < mm → Mem j < n)
    (hsm : ∀ i j, i < j → j < mm → Mem i < Mem j)
    (hρ : ∀ j, j < mm → ρ[j]? = some (R j)) (hRB : ∀ j, j < mm → R j < B) :
    Spec B (fun σ => ScatInv n mm Mem R ρ σ ∧ σ.vars "km" < mm)
      (.seq (.assign "ku" (.get "mem" (.var "km")))
        (.seq (.store "ork" (.var "ku") (.get "rnk" (.var "km")))
          (.assign "km" (.add (.var "km") (.lit 1)))))
      (fun σ σ' => ScatInv n mm Mem R ρ σ' ∧ σ'.vars "km" = σ.vars "km" + 1) 11 := by
  have hmn : mm ≤ n := card_le_of_smono hsm hMlt
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hmm, hmem, hrnk, -, Ork, hork, hcell⟩, hk⟩ := hσ
  have hkn : σ.vars "km" < n := lt_of_lt_of_le hk hmn
  have hMk : Mem (σ.vars "km") < n := hMlt _ hk
  -- read the arena number of the member
  have e₁ : (Expr.get "mem" (.var "km")).evalB B σ = some (Mem (σ.vars "km")) :=
    evalB_get (evalB_var (by omega)) (by rw [hmem, getElem?_arrOf _ hkn]) (by omega)
  have r₁ := Run.assign (x := "ku") e₁
  -- store the rank at it
  have e₂ : (Expr.var "ku").evalB B (σ.setVar "ku" (Mem (σ.vars "km"))) =
      some (Mem (σ.vars "km")) :=
    evalB_var (by simp only [vars_setVar, if_true]; omega)
  have e₃ : (Expr.get "rnk" (.var "km")).evalB B (σ.setVar "ku" (Mem (σ.vars "km"))) =
      some (R (σ.vars "km")) := by
    refine evalB_get (k := σ.vars "km") (evalB_var ?_) ?_ (hRB _ hk)
    · simp only [vars_setVar, if_neg (by decide : ¬ ("km" = "ku"))]; omega
    · simp only [arrs_setVar, hrnk]
      exact hρ _ hk
  have r₂ := Run.store (a := "ork") e₂ e₃
    (by simp only [arrs_setVar, hork, length_arrOf]; exact hMk)
  -- step the counter
  have hkmv : (((σ.setVar "ku" (Mem (σ.vars "km"))).setArr "ork" (Mem (σ.vars "km"))
      (R (σ.vars "km")))).vars "km" = σ.vars "km" := by
    simp only [vars_setArr, vars_setVar, if_neg (by decide : ¬ ("km" = "ku"))]
  have e₄ : (Expr.bin .add (.var "km") (.lit 1)).evalB B
      (((σ.setVar "ku" (Mem (σ.vars "km"))).setArr "ork" (Mem (σ.vars "km"))
        (R (σ.vars "km")))) = some (σ.vars "km" + 1) := by
    have h := evalB_bin (op := .add) (B := B)
      (σ := ((σ.setVar "ku" (Mem (σ.vars "km"))).setArr "ork" (Mem (σ.vars "km"))
        (R (σ.vars "km"))))
      (evalB_var (x := "km") (by rw [hkmv]; omega)) (evalB_lit (B := B) (n := 1) (by omega))
      (by rw [Bop.apply_add, hkmv]; omega)
    rwa [Bop.apply_add, hkmv] at h
  have r₃ := Run.assign (x := "km") e₄
  refine ⟨_, _, (r₁.seq (r₂.seq r₃)), by simp [Expr.size], ⟨?_, ?_, ?_, ?_, ?_⟩, by simp⟩
  · simp only [vars_setVar, vars_setArr]; simpa using hmm
  · simp only [arrs_setVar, arrs_setArr, if_neg (by decide : ¬ ("mem" = "ork"))]; exact hmem
  · simp only [arrs_setVar, arrs_setArr, if_neg (by decide : ¬ ("rnk" = "ork"))]; exact hrnk
  · simp only [vars_setVar, if_true]; omega
  · refine ⟨upd Ork (Mem (σ.vars "km")) (R (σ.vars "km")), ?_, ?_⟩
    · simp only [arrs_setVar, arrs_setArr, if_true, hork, set_arrOf_eq_upd]
    · intro j hj
      simp only [vars_setVar, if_true] at hj
      rcases Nat.lt_or_ge j (σ.vars "km") with hlt | hge
      · rw [upd_of_ne _ (Nat.ne_of_lt (hsm j _ hlt hk)), hcell j hlt]
      · have : j = σ.vars "km" := by omega
        rw [this, upd_self]

/-- **`ScatterBacksW`, discharged.** The whole walk: `15·mm + 6` ticks,
inside `scatterCost mm = 100·mm + 100`, and the three frame clauses off
the syntax (`scatterCom` writes `"ork"` and the two `k`-scalars, so
`kmax`, `ioff` and `itg` come out as they went in). -/
theorem scatterBacksW {B n mm : ℕ} {Mem : ℕ → ℕ} : ScatterBacksW B n mm Mem := by
  intro R σ hmm hmem hMlt hrnk hork hsm hnB hRB hρlen
  have hmn : mm ≤ n := card_le_of_smono hsm hMlt
  have hmB : mm < B := by omega
  have hρ : ∀ j, j < mm → (σ.arrs "rnk")[j]? = some (R j) := by
    intro j hj
    have hjlen : j < (σ.arrs "rnk").length := lt_of_lt_of_le hj hρlen
    have h := hrnk j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlen, Option.getD_some] at h
    rw [List.getElem?_eq_getElem hjlen, h]
  obtain ⟨g, hg⟩ := hork
  have hspec := (Lax3Proofs.RamDriverOrder.forRangeZero' (B := B) "km" (.var "mm")
    (ScatInv n mm Mem R (σ.arrs "rnk")) mm 11 (by omega)
    (fun τ hτ => lt_of_le_of_lt hτ.2.2.2.1 hmB)
    (fun τ hτ => by rw [← hτ.1]; exact evalB_var (by rw [hτ.1]; exact hmB))
    (fun τ hτ => hτ.2.2.2.1)
    (scatBody_spec hnB hMlt hsm hρ hRB))
  obtain ⟨σ', hrun, ⟨-, -, -, -, Ork, hOrk, hOcell⟩, hkm⟩ :=
    hspec.run (σ := σ) ⟨by simpa using hmm, hmem, rfl, by simp, g, hg, by simp⟩
  refine ⟨σ', ?_, ?_, ?_, ?_, ?_⟩
  · refine hrun.mono ?_
    show (11 + (Expr.var "mm").size + 3) * mm + (Expr.var "mm").size + 5 ≤ scatterCost mm
    simp only [size_var, scatterCost]
    omega
  · intro j hj
    rw [hOrk, getD_arrOf _ (hMlt j hj)]
    exact hOcell j (by rw [hkm]; exact hj)
  · exact hrun.frame_var "kmax" (by decide)
  · exact hrun.frame_arr "ioff" (Lax3Proofs.Refine.ElimCompact.notMem_scatterCom_warrs (by decide))
  · exact hrun.frame_arr "itg" (Lax3Proofs.Refine.ElimCompact.notMem_scatterCom_warrs (by decide))

/-! ## §3 The compaction walk: the charge is the RAW member-row sum

`CompactInstalls` charges `compactPass ; installCom` at
`compactCost mm cs = 100·mm + 100·cs + 100`, with `cs` the slot count of
the compact CSR — and `CsrGraph.last` pins that to the *live* degree sum
of the member pullback. But `cRow` walks `off[ku] … off[ku+1)`, the
member's **raw** row in the level CSR, and drops the dead targets by an
`ite` *inside* the loop. Where a member's row lists dead vertices the
walk pays for them and the budget does not.

`ElimCompact` §2.4's wedge separates the two counts (`ks = 10` against a
raw sum of `11`) but does not clock the compaction against
`compactCost`; §3.1 does, on an instance where the gap is forty slots
against zero. -/

open Lax3Proofs.TgtWidenProbe (PSt PRes exec execC pB pF)
open Lax3Proofs.Refine.ElimCompact (cSt compactPass installCom compactCost)

/-! ### §3.1 The instance, and the clock

A star: the centre `0` is alive and is the single member; its forty
leaves `1 … 40` are all dead. The level CSR is a genuine `CsrSimple` (the
star, symmetric, each neighbour listed once), the mask marks exactly
`{0}`, and the member list is `[0]` — so every hypothesis of
`CompactInstalls` holds at `mm = 1`, `nt = 80`.

The compact CSR is a single empty row: `cs = 0`. So the budget is
`compactCost 1 0 = 200`, while the walk crosses the centre's forty raw
slots. -/

/-- The star's offsets: `0 ↦ {1 … 40}`, `k ↦ {0}` for `1 ≤ k ≤ 40`,
everything above isolated. -/
def deadOffL (n : ℕ) : List ℕ :=
  (0 :: (List.range 41).map (fun k => 40 + k)) ++ List.replicate (n + 1 - 42) 80

/-- …its targets: the centre's row is `1 … 40`, each leaf's row is `0`. -/
def deadTgtL (W : ℕ) : List ℕ := (List.range 40).map (fun k => k + 1) ++ List.replicate (W - 40) 0

/-- …its mask: the centre alone. -/
def deadAlvL (n : ℕ) : List ℕ := 1 :: List.replicate (n - 1) 0

/-- …and its member list, at the carrier's physical length with junk
above the live prefix. -/
def deadMemL (n : ℕ) : List ℕ := 0 :: List.replicate (n - 1) 999

/-- The dead-row arena at carrier `n`. -/
def deadSt (n W : ℕ) : PSt := cSt n W 1 (deadOffL n) (deadTgtL W) (deadAlvL n) (deadMemL n)

def deadRun (n W : ℕ) : PRes := exec pB pF (.seq compactPass installCom) (deadSt n W)

/-- The compaction's clock on the dead-row arena. -/
def deadClock (n W : ℕ) : ℕ := (execC pB pF (.seq compactPass installCom) (deadSt n W)).2

#guard (deadRun 100 128).isOk
-- the compact CSR is one empty row: the live slot count is zero …
#guard (deadRun 100 128).scalar "ks" = 0
#guard (List.range 2).map ((deadRun 100 128).cell "kof") = [0, 0]
-- … the raw row the walk crossed is forty slots long …
#guard (deadOffL 100).getD 1 0 - (deadOffL 100).getD 0 0 = 40
-- … and the clock is outside the budget `CompactInstalls` states. THIS
-- REFUTES the cost clause of the frozen obligation.
#guard ¬ (deadClock 100 128 ≤ compactCost 1 0)
#guard compactCost 1 0 = 200
#guard deadClock 100 128 = 849
-- the honest direction: it *is* inside the budget read at the raw sum,
-- and that budget is carrier-blind exactly as `compactCost` is
#guard deadClock 100 128 ≤ compactCostRaw 1 40
#guard deadClock 800 128 = 849

/-! ### §3.2 The honest charge

The quantity the walk actually pays is the members' raw row-length sum,
`ElimCompact.memRowSum`, and the budget is `ElimCompact.compactCostRaw`
at it — `compactCost`'s shape with the live slot count replaced. It is
still **carrier-blind** and still arena-relative: it is the `csrW`
reading of `MassWeight` §1, the machine's own weight, as against the
`graphW` reading that `arenaWeight` uses. §3.3 is that identity, and
`ElimCompact.CompactInstalls` now states the charge this way. -/

/-! ### §3.3 …and it is the arena's machine weight

`MassWeight` carries two weight readings, `graphW H v = 1 + vdeg H v`
and `csrW n O v = 1 + rowLen O v`, and proves its lemmas of a general
weight precisely so that a consumer holding the machine's reading can
instantiate them. This is the reason the second reading exists: the
compaction's charge is the `csrW`-weight of the arena, exactly, and the
transport is §1's `wsum_markSet_eq` at `f := csrW n O`. -/

/-- **The compaction's charge is the arena's machine weight.** -/
theorem wsum_csrW_markSet {O : ℕ → ℕ} (hml : MemList n mm Mem (markSet n M)) :
    wsum (csrW n O) (markSet n M) = mm + memRowSum mm O Mem := by
  rw [wsum_markSet_eq hml, memRowSum, ← Fin.sum_univ_eq_sum_range
    (fun j => Csr.rowLen O (Mem j)) mm]
  have h : ∀ i : Fin mm, csrW n O (memEmb hml i) = 1 + Csr.rowLen O (Mem (i : ℕ)) :=
    fun _ => rfl
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib]
  simp

/-! ## §4 The compaction walk's first half: the inverse numbering

`compactPass = cixPass ; compactCsr`, and the two halves are of quite
different sizes. `cixPass` is the *same* member walk as `scatterCom` — a
`forRangeZero'` at `"km"` that stores one value at the member's arena
cell, and `ElimCompact` §9(3) is right that this is shared plumbing:

```
cixPass    = memScatter "kix" (.var "km")
scatterCom = memScatter "ork" (.get "rnk" (.var "km"))
```

for the same `memScatter`. So it is discharged here, in full, at the same
tight charge; `compactCsr` — the nested CSR construction, whose
postcondition is a `CsrSimple` of the member pullback — is the leaf that
did not fit this session (§5).

The numbering this leaves is exactly `cRow`'s reader: member `k` of the
list becomes compact vertex `k`, written at the member's *arena*
position, and the non-member cells are untouched. -/

/-- **The inverse numbering's invariant.** -/
def CixInv (n mm : ℕ) (Mem : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "mm" = mm ∧ σ.arrs "mem" = arrOf n Mem ∧ σ.vars "km" ≤ mm ∧
    ∃ Kix, σ.arrs "kix" = arrOf n Kix ∧ ∀ j, j < σ.vars "km" → Kix (Mem j) = j

/-- **One member numbered.** Ten ticks; the member list's sortedness is
again what keeps an earlier member's cell from being overwritten. -/
theorem cixBody_spec {B n mm : ℕ} {Mem : ℕ → ℕ}
    (hnB : n < B) (hMlt : ∀ j, j < mm → Mem j < n)
    (hsm : ∀ i j, i < j → j < mm → Mem i < Mem j) :
    Spec B (fun σ => CixInv n mm Mem σ ∧ σ.vars "km" < mm)
      (.seq (.assign "ku" (.get "mem" (.var "km")))
        (.seq (.store "kix" (.var "ku") (.var "km"))
          (.assign "km" (.add (.var "km") (.lit 1)))))
      (fun σ σ' => CixInv n mm Mem σ' ∧ σ'.vars "km" = σ.vars "km" + 1) 10 := by
  have hmn : mm ≤ n := card_le_of_smono hsm hMlt
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hmm, hmem, -, Kix, hkix, hcell⟩, hk⟩ := hσ
  have hkn : σ.vars "km" < n := lt_of_lt_of_le hk hmn
  have hMk : Mem (σ.vars "km") < n := hMlt _ hk
  have e₁ : (Expr.get "mem" (.var "km")).evalB B σ = some (Mem (σ.vars "km")) :=
    evalB_get (evalB_var (by omega)) (by rw [hmem, getElem?_arrOf _ hkn]) (by omega)
  have r₁ := Run.assign (x := "ku") e₁
  have e₂ : (Expr.var "ku").evalB B (σ.setVar "ku" (Mem (σ.vars "km"))) =
      some (Mem (σ.vars "km")) :=
    evalB_var (by simp only [vars_setVar, if_true]; omega)
  have e₃ : (Expr.var "km").evalB B (σ.setVar "ku" (Mem (σ.vars "km"))) =
      some (σ.vars "km") := by
    refine evalB_var ?_
    simp only [vars_setVar, if_neg (by decide : ¬ ("km" = "ku"))]; omega
  have r₂ := Run.store (a := "kix") e₂ e₃
    (by simp only [arrs_setVar, hkix, length_arrOf]; exact hMk)
  have hkmv : (((σ.setVar "ku" (Mem (σ.vars "km"))).setArr "kix" (Mem (σ.vars "km"))
      (σ.vars "km"))).vars "km" = σ.vars "km" := by
    simp only [vars_setArr, vars_setVar, if_neg (by decide : ¬ ("km" = "ku"))]
  have e₄ : (Expr.bin .add (.var "km") (.lit 1)).evalB B
      (((σ.setVar "ku" (Mem (σ.vars "km"))).setArr "kix" (Mem (σ.vars "km"))
        (σ.vars "km"))) = some (σ.vars "km" + 1) := by
    have h := evalB_bin (op := .add) (B := B)
      (σ := ((σ.setVar "ku" (Mem (σ.vars "km"))).setArr "kix" (Mem (σ.vars "km"))
        (σ.vars "km")))
      (evalB_var (x := "km") (by rw [hkmv]; omega)) (evalB_lit (B := B) (n := 1) (by omega))
      (by rw [Bop.apply_add, hkmv]; omega)
    rwa [Bop.apply_add, hkmv] at h
  have r₃ := Run.assign (x := "km") e₄
  refine ⟨_, _, (r₁.seq (r₂.seq r₃)), by simp [Expr.size], ⟨?_, ?_, ?_, ?_⟩, by simp⟩
  · simp only [vars_setVar, vars_setArr]; simpa using hmm
  · simp only [arrs_setVar, arrs_setArr, if_neg (by decide : ¬ ("mem" = "kix"))]; exact hmem
  · simp only [vars_setVar, if_true]; omega
  · refine ⟨upd Kix (Mem (σ.vars "km")) (σ.vars "km"), ?_, ?_⟩
    · simp only [arrs_setVar, arrs_setArr, if_true, hkix, set_arrOf_eq_upd]
    · intro j hj
      simp only [vars_setVar, if_true] at hj
      rcases Nat.lt_or_ge j (σ.vars "km") with hlt | hge
      · rw [upd_of_ne _ (Nat.ne_of_lt (hsm j _ hlt hk)), hcell j hlt]
      · have hje : j = σ.vars "km" := by omega
        rw [hje, upd_self]

/-- **`cixPass`, discharged.** Member `k` becomes compact vertex `k`, at
the member's arena cell, in `14·mm + 6` ticks — the member count and
nothing else. The member list and the count come out untouched, which is
what `compactCsr` reads next. -/
theorem cixPass_run {B n mm : ℕ} {Mem : ℕ → ℕ} {σ : Env}
    (hnB : n < B) (hmm : σ.vars "mm" = mm) (hmem : σ.arrs "mem" = arrOf n Mem)
    (hMlt : ∀ j, j < mm → Mem j < n) (hsm : ∀ i j, i < j → j < mm → Mem i < Mem j)
    (hkix : ∃ g, σ.arrs "kix" = arrOf n g) :
    ∃ (σ' : Env) (Kix : ℕ → ℕ),
      Run B Lax3Proofs.Refine.ElimCompact.cixPass σ σ' (14 * mm + 6) ∧
        σ'.arrs "kix" = arrOf n Kix ∧ (∀ j, j < mm → Kix (Mem j) = j) ∧
        σ'.vars "mm" = mm ∧ σ'.arrs "mem" = arrOf n Mem := by
  have hmn : mm ≤ n := card_le_of_smono hsm hMlt
  have hmB : mm < B := by omega
  obtain ⟨g, hg⟩ := hkix
  have hspec := (Lax3Proofs.RamDriverOrder.forRangeZero' (B := B) "km" (.var "mm")
    (CixInv n mm Mem) mm 10 (by omega)
    (fun τ hτ => lt_of_le_of_lt hτ.2.2.1 hmB)
    (fun τ hτ => by rw [← hτ.1]; exact evalB_var (by rw [hτ.1]; exact hmB))
    (fun τ hτ => hτ.2.2.1)
    (cixBody_spec hnB hMlt hsm))
  obtain ⟨σ', hrun, ⟨hmm', hmem', -, Kix, hKix, hKcell⟩, hkm⟩ :=
    hspec.run (σ := σ) ⟨by simpa using hmm, hmem, by simp, g, hg, by simp⟩
  refine ⟨σ', Kix, hrun.mono ?_, hKix, fun j hj => hKcell j (by rw [hkm]; exact hj),
    hmm', hmem'⟩
  show (10 + (Expr.var "mm").size + 3) * mm + (Expr.var "mm").size + 5 ≤ 14 * mm + 6
  simp only [size_var]
  omega

/-! ## §5 The ledger: what was found here, and where each repair landed

**Discharged here.** `arenaWeight_memGraph` (§1, the E5 tie),
`scatterBacksW` (§2, the scatter walk in full), `wsum_csrW_markSet`
(§3.3, the compaction's honest charge in `MassWeight`'s own vocabulary),
`cixPass_run` (§4, the compaction's first half).

**Refuted, and repaired in the parent.** Both obligation `Prop`s of
`ElimCompact` §8 were false as first frozen, and the two failures are of
different kinds.

1. `ScatterBacks` — `not_scatterBacks_of_repeat` (§2.1). The
   postcondition is unsatisfiable at a member list that repeats an arena
   number: two members at one cell ask it to hold two ranks, and no
   program can be blamed for that. The repair is
   `ElimCompact.ScatterBacksW` — `MemList.smono`, `n < B`,
   `mm ≤ (σ.arrs "rnk").length` and `∀ j < mm, R j < B` added, the
   conclusion unmoved — and `scatterBacksW` above discharges it, with no
   hypothesis on `B`, `n`, `mm` or `Mem` at all. `elimCompact_spec`
   consumes the repaired form. The refuted reading is kept compiled,
   because the refutation is stated against it and because
   `Refine/AugCompact.lean` — a sibling wave's file — still names it
   (see the open defect below).
2. `CompactInstalls` — §3.1. Its cost clause charged the compaction at
   the *live* slot count `cs` while `cRow` crosses the member's **raw**
   row: on the dead-row star the clock is `849` against a budget of
   `200`. The repair is `ElimCompact.compactCostRaw mm
   (ElimCompact.memRowSum mm O Mem)`, still carrier-blind and still
   arena-relative — `wsum_csrW_markSet` identifies `mm + memRowSum` with
   the arena's own `csrW`-weight, which is why `MassWeight` carries that
   second reading at all. `ElimCompact.CompactInstalls` now states the
   charge that way, adds the conclusion `cs ≤ memRowSum mm O Mem` that
   ties the two readings together, and adds the word bounds a `Run`
   needs (without them no derivation exists and the conclusion fails
   vacuously — the same defect class as `ScatterBacks`'s missing
   `n < B`). Its correctness content, untouched by the cost finding, is
   discharged in `Refine/ElimCompactCsr.lean`.
3. `CompactInstalls` a second time, on a clause found *while* it was
   being discharged: `∀ v < n, M v < B`, the **mask's own magnitude**.
   `ArenaEntryC` pins the mask's *length* (`alv = arrOf n M`) and says
   nothing about the numbers in it, while `cRow` tests liveness with an
   IMP+ `get` on `alv`, whose value must fit the word. The
   counterexample is a store whose mask cell holds `100` at word bound
   `B = 6`: the read returns `none`, so no run of `compactPass` exists
   and the postcondition is unreachable however good the program is.
   This is exactly `RamElim.elim_specW`'s long-standing `hMB`, lost when
   `ArenaEntryC` replaced `ElimPre`'s clause list at the compacted entry
   surface — the engine call inside `elimCompact_spec` would have needed
   it even if the compaction had not. The clause now sits inside
   `CompactInstalls`, and the compiled falsification that warrants it is
   `Refine/ElimCompactCsr.lean` §0, with the same standing that
   `not_scatterBacks_of_repeat` has for `ScatterBacksW`. `ScatterBacksW`
   is unaffected: `scatterCom` never reads `alv`.

**The third defect, in the engine's landed export, is closed.**
`RamElim.AfterLoopW` and `AfterOffW` both carry `∀ v < n, R v < n`, and
`ElimMem` — written before the rank inversion existed — dropped it, so
`ElimPost` dropped it too. That is a statement gap, not a proof gap:
`scatterCom` reads `rnk[km]` with an IMP+ `get`, so without the bound
there is no derivation and the landed contract cannot be used at all.
`RamElim.ElimMem` could not simply be widened — `RamDriverCompose` and
`RamDriverAugment` destructure it — so the clause is threaded *beside*
it: `RamElim.RnkLt`, carried by `implementsWR`/`elim_specWR`, with the
frozen `implementsW` derived from `implementsWR` by weakening. Every
consumer sees the surface it always saw, and `ElimCompact.elimCompact_spec`
gets the rank bound it needs. `elimCompact_spec` also gained `n < B`,
which every landed caller of the package holds.

**Open, and not this wave's to fix.** `Refine/AugCompact.lean:941`
(`augCompact_spec`) still names the refuted `ScatterBacks` as a
hypothesis, so it stands on a `Prop` that has no witness. The repair is
one word — `ScatterBacksW`, whose statement was deliberately kept usable
by both families — but the file belongs to the E2-aug wave.

**The composed corollary** the E2-sat session could not produce — a
compacted engine on real discharges, with no hypothesis manufactured by
weakening — is `Refine/ElimCompactCsr.lean`'s. -/

/-! ## §6 Axioms -/

#print axioms arenaWeight_memGraph
#print axioms scatterBacksW
#print axioms not_scatterBacks_of_repeat
#print axioms cixPass_run
#print axioms wsum_csrW_markSet

end Lax3Proofs.Refine.ElimCompactWalks

