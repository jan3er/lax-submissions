import Lax3Proofs.RamDriverCompose
import Lax3Proofs.Refine.DeadRow

/-!
**The dead-row sweep, walked** — rebase B8, the machine half.

`RamDriver.SweepImplements` is the obligation; this file discharges it.
There is almost no new walk in it: `RamDriver.sweepCom` *is* the vertex
loop of the base case, factored out of `RamDriver.baseCom` and run at a
level's own depth instead of at the bottom, so `RamDriverBot.base_turn_spec`
is its turn verbatim and `Spec.forRangeZero` is its loop. What is new is
two lines of mathematics and one frame.

# §1 The mathematics: two readings of a dead vertex's row

`RamDriverBot.BaseTabOk` says the cells hold the truth values on the
**edgeless** arena. `RamDriver.TableInv` asks for the truth values on
the level's own arena `masked G M`. At a vertex the mask kills, those
are the same question — `Refine.DeadRow.sat_bot_of_dead` — and at a
vertex it does not kill they are different questions, which is why the
sweep's postcondition is quantified over the dead vertices only and why
the alive vertices' cells, which the sweep also writes, are left
uncharacterized: their own turn overwrites them.

# §2 The frame

The pass sits *between* the cover phase and the centre loop, so
everything the cover phase produced has to survive it. What it writes is
the depth's own tables and the generated evaluator's scratch —
`RamDriverBot.warrs_baseFold`/`wvars_baseFold`, read through the two
frame lemmas below — and every name a level holds is a depth-family name
whose first character is not `b`, hence not an extension of `"bb"`, and
is not a `tabName`. So the whole frame is character arithmetic on names.

# §3 Cost, and what it costs the recursion

`sweepCost` is one carrier-width walk whose turn is the depth's own
straight line of `botCom` fragments — which since R1.8-T4a is
`RamDriverBot.baseCost` on the nose (`baseCost_eq`), the base case having
shed the representative pass. It joins `Ko` and `Kc` as a **phase constant of a
level read at the arena's size**, which is the same debt the ordering
and cover phases already carry (`RamDriverRoot.levelAt`'s `hKo`/`hKc`
instantiate size-blind carrier-width constants at every size) and the
same debt the touched-only revision R1.6 owns. It is emphatically *not*
the debt B3 removed: that one was `n` **turns**, each opening a whole
nested driver; this is `n` **cells**, each a straight line of fixed
length. The arithmetic is `#guard`ed below.

Note the sweep is deliberately **not** guarded on aliveness. A guard
would save the alive vertices' fragments, but the alive vertices are the
minority of a nested arena — the dead ones are `n - m` of `n` — so the
guard buys a constant factor at best and costs a mask read per vertex.
The guard that matters is the one on the *turns*, and that one is in
`RamDriver.compactCom`.
-/

namespace Lax3Proofs.Refine.DeadSweep

open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverBot
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ### §0 The names the sweep does not touch

The evaluator writes the cell `"bb"` and its extensions, the counter
`"z"`, the environment slots, and the depth's tables. Every name a level
holds is a depth-family name whose first character is not `b`, so none of
them is an extension of `"bb"`; and none of them is a `tabName`. -/

theorem not_ext_bb_append {c : Char} {t : List Char} {p : String} (hp : p.toList = c :: t)
    (hc : c ≠ 'b') (u : String) : ¬ Ext "bb" (p ++ u) := fun h =>
  not_ext_b_of_cons (y := p ++ u) (by rw [String.toList_append, hp]; rfl) hc
    (RamDriverCompose.ext_b_of_ext_bb h)

theorem not_ext_bb_ordName (a : ℕ) : ¬ Ext "bb" (ordName a) := by
  rw [ordName]; exact not_ext_bb_append (p := "od") rfl (by decide) _

theorem not_ext_bb_xofName (a : ℕ) : ¬ Ext "bb" (xofName a) := by
  rw [xofName]; exact not_ext_bb_append (p := "xf") rfl (by decide) _

theorem not_ext_bb_xmmName (a : ℕ) : ¬ Ext "bb" (xmmName a) := by
  rw [xmmName]; exact not_ext_bb_append (p := "xm") rfl (by decide) _

theorem not_ext_bb_asgName (a : ℕ) : ¬ Ext "bb" (asgName a) := by
  rw [asgName]; exact not_ext_bb_append (p := "ag") rfl (by decide) _

theorem not_ext_bb_xpName (a : ℕ) : ¬ Ext "bb" (xpName a) := by
  rw [xpName]; exact not_ext_bb_append (p := "xq") rfl (by decide) _

theorem not_ext_bb_cpsName (a : ℕ) : ¬ Ext "bb" (cpsName a) := by
  rw [cpsName]; exact not_ext_bb_append (p := "cs") rfl (by decide) _

theorem not_ext_bb_cnumName (a : ℕ) : ¬ Ext "bb" (cnumName a) := by
  rw [cnumName]; exact not_ext_bb_append (p := "cq") rfl (by decide) _

theorem not_ext_bb_ctrName (a : ℕ) : ¬ Ext "bb" (ctrName a) := by
  rw [ctrName]; exact not_ext_bb_append (p := "ctr") rfl (by decide) _

/-! ### §1 The syntactic frame of the sweep -/

theorem warrs_sweepCom {q_top cap mb jd : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ jd, IsLocal β) :
    ∀ a ∈ (sweepCom q_top cap mb jd φ).warrs, (∃ i, a = tabName jd i) ∨ Ext "bb" a := by
  intro a ha
  rw [show (sweepCom q_top cap mb jd φ).warrs =
    [] ++ ([] ++ ((foldIdx (fun i β =>
      Com.seq (botCom jd β "bb") (.store (tabName jd i) (.var "z") (.var "bb"))) 0
      (tablesAt q_top cap mb φ jd)).warrs ++ [])) from rfl] at ha
  simp only [List.append_nil, List.nil_append] at ha
  exact warrs_baseFold jd _ 0 hlocal a ha

theorem wvars_sweepCom {q_top cap mb jd : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ jd, IsLocal β) :
    ∀ y ∈ (sweepCom q_top cap mb jd φ).wvars,
      y = "z" ∨ (∃ i, y = envName i) ∨ Ext "bb" y := by
  intro y hy
  rw [show (sweepCom q_top cap mb jd φ).wvars =
    ["z"] ++ ([envName 0] ++ ((foldIdx (fun i β =>
      Com.seq (botCom jd β "bb") (.store (tabName jd i) (.var "z") (.var "bb"))) 0
      (tablesAt q_top cap mb φ jd)).wvars ++ ["z"])) from rfl] at hy
  simp only [List.mem_append, List.mem_singleton] at hy
  rcases hy with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨0, h⟩)
  · rcases wvars_baseFold jd _ 0 hlocal y h with h' | ⟨i, -, h'⟩
    · exact Or.inr (Or.inr h')
    · exact Or.inr (Or.inl ⟨i, h'⟩)
  · exact Or.inl h

/-! ### §2 The pass, walked -/

/-- The cost of the sweep: one carrier walk whose turn is the depth's own
straight line of `botCom` fragments. -/
noncomputable def sweepCost (q_top cap mb jd n : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  (turnCost q_top cap mb jd φ + 4) * n + 6

/-- **The base case IS the sweep at the bottom depth** (R1.8-T4a). It used
to be the representative pass followed by the sweep, and `baseCost` used
to be `reprCost` plus this; the scan is out of the program (`RamDriver.baseCom`),
so the two costs coincide. The shed itself is `Refine.BaseShed`. -/
theorem baseCost_eq (q_top cap mb ℓ n : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    baseCost q_top cap mb ℓ n φ = sweepCost q_top cap mb ℓ n φ :=
  rfl

/-- **The sweep, walked.** Every cell of every table of the depth holds
the truth value of its formula on the edgeless arena. -/
theorem sweep_spec {B n q_top cap mb jd : ℕ} {C : ℕ → ℕ → ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hB : 1 < B) (hn : n < B) (hbit : ∀ c < sigL cap mb jd, ∀ v < n, C c v ≤ 1)
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ jd, IsLocal β) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ BotEnv n (sigL cap mb jd) jd C σ ∧
        BaseMem B q_top cap mb jd φ σ ∧
        ∀ (i : ℕ), i < (tablesAt q_top cap mb φ jd).length →
          ∃ Tb : ℕ → ℕ, σ.arrs (tabName jd i) = arrOf n Tb)
      (sweepCom q_top cap mb jd φ)
      (fun _ σ' => BaseTabOk q_top cap mb jd n φ C (fun _ => n) σ')
      (sweepCost q_top cap mb jd n φ) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hvn, hcol, hmem, htabs⟩ := hσ
  have hstart : BaseTabOk q_top cap mb jd n φ C (fun _ => (σ.setVar "z" 0).vars "z")
      (σ.setVar "z" 0) := by
    intro i hi
    obtain ⟨Tb, hTb⟩ := htabs i hi
    refine ⟨Tb, by rw [arrs_setVar]; exact hTb, fun v hv => ?_⟩
    exfalso
    replace hv : (v : ℕ) < (σ.setVar "z" 0).vars "z" := hv
    rw [vars_setVar, if_pos rfl] at hv
    omega
  obtain ⟨σ₂, hrun₂, ⟨-, -, htab₂⟩, hz₂⟩ :=
    (Spec.forRangeZero (B := B) "z" "n" (BaseInv B n q_top cap mb jd C φ) n
      (turnCost q_top cap mb jd φ) hn (fun τ hτ => hτ.2.1) (fun τ hτ => hτ.1.1)
      (base_turn_spec hB hn hbit hlocal)).run (σ := σ)
      ⟨⟨by rw [vars_setVar, if_neg (by decide)]; exact hvn,
        fun c hc => by rw [arrs_setVar]; exact hcol c hc,
        fun i hi => botMem_of_length (fun a => by rw [arrs_setVar]) _ "bb" (hmem i hi)⟩,
        by rw [vars_setVar, if_pos rfl]; omega, hstart⟩
  refine ⟨σ₂, _, hrun₂, by rw [sweepCost], ?_⟩
  intro i hi
  obtain ⟨Tb, hTb, hTbval⟩ := htab₂ i hi
  exact ⟨Tb, hTb, fun v hv => hTbval v (by rw [hz₂]; exact v.isLt)⟩

/-! ### §3 The obligation -/

/-- The two membership frames, in the form `RamDriverCompose.levelPre_run`
and the obligation's clauses consume. -/
theorem notMem_warrs_sweepCom {q_top cap mb jd : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ jd, IsLocal β) {a : String}
    (htab : ∀ i, a ≠ tabName jd i) (hext : ¬ Ext "bb" a) :
    a ∉ (sweepCom q_top cap mb jd φ).warrs := by
  intro h
  rcases warrs_sweepCom hlocal a h with ⟨i, hi⟩ | h'
  · exact htab i hi
  · exact hext h'

theorem notMem_wvars_sweepCom {q_top cap mb jd : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ jd, IsLocal β) {y : String}
    (hz : y ≠ "z") (hev : ∀ i, y ≠ envName i) (hext : ¬ Ext "bb" y) :
    y ∉ (sweepCom q_top cap mb jd φ).wvars := by
  intro h
  rcases wvars_sweepCom hlocal y h with h' | ⟨i, hi⟩ | h'
  · exact hz h'
  · exact hev i hi
  · exact hext h'

theorem noWrite_sweepCom (q_top cap mb jd : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    (sweepCom q_top cap mb jd φ).NoWrite :=
  ⟨trivial, trivial, RamDriverBot.noWrite_baseFold jd _ 0, trivial⟩

open Classical in
/-- **The dead-row sweep of a level, discharged.**
`RamDriver.SweepImplements`, from `sweep_spec` and the two frames.

The mathematics is one rewrite: `sweep_spec` leaves the *edgeless*
readings, and `Refine.DeadRow.sat_bot_of_dead` says that at a vertex the
mask kills the edgeless reading is the reading in the level's own arena.
Everything else is names. -/
theorem sweepImplements {n B q_top cap mb ns W ℓ jd : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {d : ℕ} (hB : WordBoundK B n d ns cap mb) :
    SweepImplements B q_top cap mb ns W ℓ jd φ G O T M Gm C
      (sweepCost q_top cap mb jd n φ) := by
  have hlocal : ∀ β ∈ tablesAt q_top cap mb φ jd, IsLocal β :=
    fun β hβ => (tableRank_of_mem_tablesAt jd β hβ).1
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hlev, htsz, hbarr⟩ := hσ
  obtain ⟨σ', hrun, htab⟩ :=
    (sweep_spec (C := C) hB.one_lt hB.n_lt hlev.2.2.2.2.2.2.2.2.1 hlocal).run (σ := σ)
      ⟨hlev.1, fun c hc => hlev.2.2.2.2.2.1 c hc, hbarr.2 jd, fun i hi => htsz.get jd hi⟩
  -- the frame, once, on the two shapes every clause below is an instance of
  have harr : ∀ (a : String), (∀ i, a ≠ tabName jd i) → ¬ Ext "bb" a →
      σ'.arrs a = σ.arrs a :=
    fun a htb hext => hrun.frame_arr a (notMem_warrs_sweepCom hlocal htb hext)
  have hvar : ∀ (y : String), y ≠ "z" → (∀ i, y ≠ envName i) → ¬ Ext "bb" y →
      σ'.vars y = σ.vars y :=
    fun y hz hev hext => hrun.frame_var y (notMem_wvars_sweepCom hlocal hz hev hext)
  have hnev : ∀ (p : String) (c : Char), (∃ t, p.toList = c :: t) → c ≠ 'e' →
      ∀ i, p ≠ envName i := fun p c hp hc i =>
    RamDriverBot.ne_of_head_ne hp (RamDriverBot.head_envName i) hc
  refine ⟨σ', _, hrun, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the level's own precondition
    refine RamDriverCompose.levelPre_run hlev hrun
      (notMem_wvars_sweepCom hlocal (by decide)
        (fun i => RamDriverBot.lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (RamDriverBot.not_ext_of_not_prefix (by decide)))
      (notMem_wvars_sweepCom hlocal (by decide)
        (fun i => RamDriverBot.lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (RamDriverBot.not_ext_of_not_prefix (by decide)))
      (notMem_wvars_sweepCom hlocal (by decide)
        (fun i => RamDriverBot.lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (RamDriverBot.not_ext_of_not_prefix (by decide)))
      (notMem_warrs_sweepCom hlocal
        (fun i => RamDriverBase.lit_ne_tabName (by decide) jd i)
        (RamDriverBot.not_ext_of_not_prefix (by decide)))
      (notMem_warrs_sweepCom hlocal
        (fun i => RamDriverBase.lit_ne_tabName (by decide) jd i)
        (RamDriverBot.not_ext_of_not_prefix (by decide)))
      (notMem_warrs_sweepCom hlocal (fun i => RamDriverBot.alvName_ne_tabName jd jd i)
        (fun h => RamDriverBot.not_ext_b_alvName jd (RamDriverCompose.ext_b_of_ext_bb h)))
      (notMem_warrs_sweepCom hlocal (fun i => RamDriverBot.gamName_ne_tabName jd jd i)
        (fun h => RamDriverBot.not_ext_b_gamName jd (RamDriverCompose.ext_b_of_ext_bb h)))
      (fun q => notMem_warrs_sweepCom hlocal (fun i => RamDriverBot.colName_ne_tabName jd q jd i)
        (fun h => RamDriverBot.not_ext_b_colName jd q (RamDriverCompose.ext_b_of_ext_bb h)))
      (fun a ha => by
        simp only [RamDriverCompose.zeroArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact notMem_warrs_sweepCom hlocal
            (fun i => RamDriverBase.lit_ne_tabName (by decide) jd i)
            (RamDriverBot.not_ext_of_not_prefix (by decide)))
      -- the member list and its count (rebase E-mem): the sweep writes the
      -- tables and the names below its own output, neither of which is a
      -- depth's `mem`/`mm`
      (notMem_warrs_sweepCom hlocal
        (fun i => RamDriverBot.ne_of_head_ne (RamDriverCompose.head_memName jd)
          (RamDriverBot.head_tabName jd i) (by decide))
        (RamDriverCompose.not_ext_bb_memName jd))
      (notMem_wvars_sweepCom hlocal (by simp [mnumName, String.ext_iff])
        (fun i => RamDriverBot.lit_ne_envName (RamDriverCompose.head_mnumName jd) (by decide) i)
        (RamDriverCompose.not_ext_bb_mnumName jd))
  · exact hrun.out_eq (noWrite_sweepCom q_top cap mb jd φ)
  · exact fun a => hvar _ (by simp [ctrName, String.ext_iff])
      (hnev _ 'c' ⟨_, by rw [ctrName, String.toList_append]; rfl⟩ (by decide))
      (not_ext_bb_ctrName a)
  · exact fun a => harr _ (fun i => RamDriverBot.gamName_ne_tabName a jd i)
      (fun h => RamDriverBot.not_ext_b_gamName a (RamDriverCompose.ext_b_of_ext_bb h))
  · exact fun a => harr _ (by simp [ordName, tabName, String.ext_iff]) (not_ext_bb_ordName a)
  · exact fun a => harr _ (by simp [xofName, tabName, String.ext_iff]) (not_ext_bb_xofName a)
  · exact fun a => harr _ (by simp [xmmName, tabName, String.ext_iff]) (not_ext_bb_xmmName a)
  · exact fun a => harr _ (by simp [asgName, tabName, String.ext_iff]) (not_ext_bb_asgName a)
  · exact fun a => hvar _ (by simp [xpName, String.ext_iff])
      (hnev _ 'x' ⟨_, by rw [xpName, String.toList_append]; rfl⟩ (by decide))
      (not_ext_bb_xpName a)
  · exact fun a => harr _ (by simp [cpsName, tabName, String.ext_iff]) (not_ext_bb_cpsName a)
  · exact fun a => hvar _ (by simp [cnumName, String.ext_iff])
      (hnev _ 'c' ⟨_, by rw [cnumName, String.toList_append]; rfl⟩ (by decide))
      (not_ext_bb_cnumName a)
  · -- **the dead rows.** The edgeless reading is the reading in the level's arena
    intro i hi Tb harr₀ v hdv
    obtain ⟨Tb', harr', hval⟩ := htab i hi
    have hTb : Tb (v : ℕ) = Tb' (v : ℕ) := RamDriverCluster.eq_of_arrOf_eq (harr₀.symm.trans harr') v.isLt
    obtain ⟨h1, h2⟩ := hval v v.isLt
    exact ⟨by rw [hTb]; exact h1,
      by rw [hTb]; exact h2.trans (DeadRow.sat_bot_of_dead₁ (G := G) hdv
        (hlocal _ (List.getElem_mem hi))).symm⟩

/-! ### §4 Falsification: the budget arithmetic

What the dead-vertex path costs a level, checked on numbers before it was
argued in prose. The sweep is `a · n + b` — a *cell* per vertex, not a
turn — and it enters the level's phase block as one more summand beside
`Ko` and `Kc`, with no factor anywhere. The last two checks are the
negative controls: a turn-shaped charge on the same carrier is orders
larger, and a per-turn sweep (one sweep inside every turn, the shape this
design deliberately avoids) is quadratic. -/

section Falsification

/-- The sweep's cost at a turn cost `K` on a carrier of `n`. -/
private def sc (K n : ℕ) : ℕ := (K + 4) * n + 6

#guard sc 10 100 = 1406
#guard sc 10 200 = 2806

-- Linear: doubling the carrier doubles the pass, exactly.
#guard sc 10 200 - sc 10 100 = sc 10 100 - sc 10 0

/-- The level's phase block: `Ko + (Kc + (Kd + (Σ + 6)))`. -/
private def phase (Ko Kc Kd S : ℕ) : ℕ := Ko + (Kc + (Kd + (S + 6)))

-- One more summand, no new factor — the sweep is additive in the block.
#guard phase 100 200 300 50 = 656
#guard phase 100 200 0 50 + 300 = phase 100 200 300 50

-- **Negative control 1.** A *turn*-shaped charge is not what this is: B3's
-- floor was `n` turns, each running a whole nested driver.
#guard ¬ (1000 * 100 ≤ sc 10 100)

-- **Negative control 2.** One sweep per turn — the shape rejected in §3 —
-- is quadratic in the carrier and leaves any linear budget behind.
#guard ¬ (100 * sc 10 100 ≤ 20 * sc 10 100)
#guard 100 * sc 10 100 = 140600

end Falsification

/-! ### §4b The member-list header, refuted (finding R1.8/1)

Wave R1.8 asked for this pass's loop header — and the base case's, since
`RamDriver.baseCom` *is* this `Com` at depth `ℓ` (R1.8-T4a; before it,
`reprCom` followed by this `Com`) — to walk the depth's member list
`RamDriver.memName j` instead of
the carrier, so that the charge becomes
`Refine.G2CostProbe.sweepCoeffA · (w + 1)` at the arena's weight. **The
header cannot move, and the obstruction is not a cost accident: it is
this pass's entire purpose.**

`RamDriver.MemEnum` (`LevelPre`'s sixteenth clause) enumerates
`{a < n | M a ≠ 0}` — the **alive** set. `RamDriver.DeadRows` — the
whole of `SweepImplements`' output clause, discharged above — is
quantified over `M v = 0`, the **dead** set. The two index sets are
exact complements (`notMem_markSet_of_dead`), so a member-list header
visits precisely the vertices whose rows this pass is *not* responsible
for (their own turns overwrite them, §1) and none of the vertices whose
rows it is. The same stop covers the base half twice over:

* `RamDriver.BaseImplements` asks for `RamDriver.TableInv` at depth `ℓ`,
  which is quantified over **all** of `Fin n`, dead vertices included;
* `BotEval.sat_exU_bot_of_repr`'s hypothesis `hW` — what `reprCom` was
  built to supply — asks for a same-row representative of every
  `v : Fin n` off the tuple, again dead ones included, because the
  bottom formula's *unrestricted* quantifier ranges over the carrier and
  not over the arena. (R1.8-T4a: this second reading is now moot for the
  landed surface — no tabled formula has an unrestricted quantifier
  (`Refine.DeadRowProbe.tabled_isLocal`), so the scan and its `hW` story
  left the program. The first reading, `TableInv` over all of `Fin n`,
  is the one the R1.8 design answers, by re-domaining the obligation.)

The witness below is the extreme case and the negative control: at the
all-dead mask the member list is **empty** at every carrier size, while
the pass owes a row at every one of the `n` vertices. No coefficient
read at the member count pays that walk — `no_memCoeff_pays_deadRows` —
which is `Refine.G2CostProbe.hKd_gap` again, but located at the
*obligation* rather than at the landed cost function, and therefore not
repairable by re-deriving a charge.

Re-charging the dead rows is consequently a **program** change and not
a header change. The recorded design intent is that a vertex's
death-row write charges to the turn that killed it — its block contains
it — which moves the write out of this pass and into the centre loop's
turn; that is the turn re-thread's wave, and no charging scheme is
invented here. -/

section HeaderStop

/-- **The all-dead mask has an empty member list**, at every carrier
size and whatever junk the array holds: `MemEnum`'s completeness clause
is vacuous because no vertex is alive. -/
theorem memEnum_zero_of_allDead (n : ℕ) (Mem : ℕ → ℕ) :
    MemEnum n 0 Mem (fun _ => 0) :=
  ⟨fun k hk => absurd hk (Nat.not_lt_zero k),
    fun _ k _ hk => absurd hk (Nat.not_lt_zero k),
    fun k hk => absurd hk (Nat.not_lt_zero k),
    fun _ _ ha => absurd rfl ha⟩

/-- **The two index sets are complements.** A vertex this pass owes a
row for is never on the member list — so a member-list header meets
none of its obligation. -/
theorem notMem_markSet_of_dead {n : ℕ} {M : ℕ → ℕ} {v : Fin n} (hv : M (v : ℕ) = 0) :
    v ∉ RamDriverCluster.markSet n M := fun h => RamDriverCluster.mem_markSet.mp h hv

/-- …and at the all-dead mask the obligation is the whole carrier. -/
theorem allDead_owes_every_row (n : ℕ) (v : Fin n) : (fun _ => (0 : ℕ)) (v : ℕ) = 0 := rfl

/-- **The negative control.** However the coefficient is chosen, a
budget read at the member count does not pay the rows this pass owes:
at the all-dead mask the count is `0` and the rows are `n`. -/
theorem no_memCoeff_pays_deadRows (coeff : ℕ) :
    ∃ n : ℕ, MemEnum n 0 (fun _ => 0) (fun _ => 0) ∧ coeff * (0 + 1) < n :=
  ⟨coeff + 1, memEnum_zero_of_allDead _ _, by omega⟩

end HeaderStop

/-! ### §5 Axioms -/

/-- info: 'Lax3Proofs.Refine.DeadSweep.sweepImplements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sweepImplements

/-- info: 'Lax3Proofs.Refine.DeadSweep.memEnum_zero_of_allDead' does not depend on any axioms -/
#guard_msgs in
#print axioms memEnum_zero_of_allDead

/-- info: 'Lax3Proofs.Refine.DeadSweep.notMem_markSet_of_dead' does not depend on any axioms -/
#guard_msgs in
#print axioms notMem_markSet_of_dead

/-- info: 'Lax3Proofs.Refine.DeadSweep.no_memCoeff_pays_deadRows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms no_memCoeff_pays_deadRows

end Lax3Proofs.Refine.DeadSweep
