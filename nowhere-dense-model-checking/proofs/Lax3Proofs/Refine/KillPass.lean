import Lax3Proofs.RamDriverWrites
import Lax3Proofs.Refine.DeadSweep

/-!
**The kill pass, walked** — wave R1.8-T2, the machine half.

`RamDriverCluster.KillStep` is the obligation; this file discharges it.
`RamDriver.killCom` is the base case's *row body* — the straight line of
`RamDriver.botCom` fragments of a depth's table, one store apiece — run
at the entries of the turn's padded batch buffer instead of at a carrier
counter, and guarded on the kill test. So there is one new walk (the
buffer loop and its accumulating invariant), one line of mathematics, and
one frame.

# §1 The mathematics: the row of a killed vertex

`bot_spec` leaves the **edgeless** reading. `RamDriver.TableInv` at depth
`j + 1` asks for the reading in the child arena `masked G Alv'`. At a
vertex the child mask kills those are the same question —
`Refine.DeadRow.sat_bot_of_dead₁` — and the pointwise clause of
`RamDriverCluster.BatchData` (wave R1.8-T1) is what says the guard picks
out killed vertices: an entry of the buffer lies in the batch `W`, so
`M v ≠ 0 ∧ v ∈ X` gives `Alv' v = 0` there. That is the whole of §1, and
it is the reason the pass must run **after** `colourCom`: the reading is
at the child palette, and writing the parent's rows would be a silent
semantic error no cost probe catches.

# §2 The walk: an accumulating invariant over the buffer

The loop's invariant is *every entry already passed that the guard
accepted has its row*, and the body must therefore not disturb the rows
already written. So the fold's specification below is **pointwise in the
cell** — the row at the entry is the bit, and every other cell of every
table comes back — which `RamDriverBot.base_block_spec`'s prefix
invariant cannot give (it speaks about the cells *below* a counter, and
the buffer's entries are in no order at all).

The padding repeats the buffer's first entry, and the guard's verdict and
the row's content are both functions of the vertex alone, so re-killing
writes the same row: `killTurn_spec`'s postcondition is what makes the
repetition harmless rather than an argument in prose.

# §3 The frame

The pass writes the child depth's tables, the evaluator's scratch, and
its own two scalars `"kk"`/`"kv"`. Every name a level or a turn holds is
a depth-family name whose first character is not `b`, hence not an
extension of `"bb"`, is not a `tabName`, and carries a digit, hence is
neither of the two literals. So the whole frame is character arithmetic
on names, exactly as in `Refine.DeadSweep`, and the write-set lemmas it
runs on are `RamDriverWrites.warrs_killCom`/`wvars_killCom`.

# §4 Cost

`killCost` is `(blockCost + 17 + 4) · mb + 6`: **carrier-blind** — `n`
does not occur — and linear in the buffer's width `mb`, which is the
formula-sized `ℓ · (2·cap + 1)`. It rides the turn's own size slot
(design §7, disposition F-4), where the probe measured the same law at
`(3·t + 20)·kills + 6` (`Refine.DeadRowProbe.killTurnCom`). §5 below is
the arithmetic, checked in both directions.
-/

namespace Lax3Proofs.Refine.KillPass

open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverBot
open Lax3Proofs.RamDriverCluster (TurnPre CoverHeld ClusterData ClusterWa BatchData markSet
  KillRowsAt KillStep eq_of_arrOf_eq)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n : ℕ}

/-! ### §0 The buffer, as a cell function -/

/-- The cell function of the padded batch buffer: the enumeration
`RamDriverCluster.ClusterWa` pins, read as a function of the index. -/
def waCell (mb : ℕ) (w : Fin mb → Fin n) : ℕ → ℕ :=
  fun k => if h : k < mb then (w ⟨k, h⟩ : ℕ) else 0

theorem waCell_lt {mb : ℕ} (w : Fin mb → Fin n) (p : Fin mb) :
    waCell mb w (p : ℕ) = (w p : ℕ) := by
  rw [waCell, dif_pos p.isLt]

theorem clusterWa_eq {mb : ℕ} {w : Fin mb → Fin n} {σ : Env} (h : ClusterWa mb w σ) :
    σ.arrs "wa" = arrOf mb (waCell mb w) := h

/-! ### §1 The row body at one entry

The fold, pointwise in the cell. Three clauses: every cell but the
entry's comes back, the entry's cell holds the bit at every table the
fold has passed, and the entry's cell comes back at every table it has
not. The third is what lets the induction put the head's own table back
together after the tail has run. -/

theorem killFold_spec {B q_top cap mb jd : ℕ} {C' : ℕ → ℕ → ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hB : 1 < B) (hn : n < B) (hbit : ∀ c < sigL cap mb jd, ∀ v < n, C' c v ≤ 1)
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ jd, IsLocal β) {u : Fin n} :
    ∀ (l : List (DistFO (sigL cap mb jd) 1)) (p : ℕ), l = (tablesAt q_top cap mb φ jd).drop p →
      Spec B
        (fun σ => BaseBase B n q_top cap mb jd C' φ σ ∧ σ.vars "kv" = (u : ℕ) ∧
          σ.vars (envName 0) = (u : ℕ) ∧
          ∀ (i : ℕ), i < (tablesAt q_top cap mb φ jd).length →
            ∃ Tb : ℕ → ℕ, σ.arrs (tabName jd i) = arrOf n Tb)
        (foldIdx (fun i β =>
          .seq (botCom jd β "bb") (.store (tabName jd i) (.var "kv") (.var "bb"))) p l)
        (fun σ σ' => BaseBase B n q_top cap mb jd C' φ σ' ∧ σ'.vars "kv" = (u : ℕ) ∧
          σ'.vars (envName 0) = (u : ℕ) ∧
          ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ jd).length),
            ∃ Tb Tb₀ : ℕ → ℕ, σ'.arrs (tabName jd i) = arrOf n Tb ∧
              σ.arrs (tabName jd i) = arrOf n Tb₀ ∧
              (∀ z < n, z ≠ (u : ℕ) → Tb z = Tb₀ z) ∧
              (p ≤ i → i < p + l.length →
                Tb (u : ℕ) ≤ 1 ∧ (Tb (u : ℕ) ≠ 0 ↔
                  Sat (⊥ : SimpleGraph (Fin n)) (colRead n C' (sigL cap mb jd)) (fun _ => u)
                    (tablesAt q_top cap mb φ jd)[i])) ∧
              ((i < p ∨ p + l.length ≤ i) → Tb (u : ℕ) = Tb₀ (u : ℕ)))
        (blockCost l) := by
  have hEbb : Ext "b" "bb" := ext_of_prefix (by decide)
  intro l
  induction l with
  | nil =>
    intro p _
    refine Spec.of_exists fun σ hσ => ?_
    refine ⟨σ, 1, Run.skip, by rw [blockCost], hσ.1, hσ.2.1, hσ.2.2.1, fun i hi => ?_⟩
    obtain ⟨Tb, hTb⟩ := hσ.2.2.2 i hi
    exact ⟨Tb, Tb, hTb, hTb, fun _ _ _ => rfl, fun hle hlt => absurd hlt (by simp only [List.length_nil]; omega),
      fun _ => rfl⟩
  | cons β l ih =>
    intro p hl
    have hp : p < (tablesAt q_top cap mb φ jd).length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hl
      exact absurd hl (by simp)
    rw [List.drop_eq_getElem_cons hp] at hl
    obtain ⟨hβ, hltail⟩ := List.cons.inj hl
    subst hβ
    have hloc : IsLocal (tablesAt q_top cap mb φ jd)[p] := hlocal _ (List.getElem_mem hp)
    refine Spec.of_exists fun σ hσ => ?_
    obtain ⟨⟨hvn, hcol, hmem⟩, hkv, hev, htab⟩ := hσ
    -- the fragment: the bit of the head's formula at the entry
    obtain ⟨σ₁, hrun₁, ⟨hb1, hbiff1⟩, hfv₁, hfa₁, hlen₁⟩ :=
      (bot_framed hloc (bot_spec (jd := jd) hB hn hbit (tablesAt q_top cap mb φ jd)[p] hloc "bb"
        hEbb (fun _ => u))).run (σ := σ)
        ⟨hcol, fun i => by rw [show (i : ℕ) = 0 from by omega, hev], hmem p hp⟩
    have hkeep : ∀ y : String, ¬ Ext "bb" y → (∀ i, 1 ≤ i → y ≠ envName i) →
        σ₁.vars y = σ.vars y := fun y hy hy' => hfv₁ y hy hy'
    have hvn₁ : σ₁.vars "n" = n := by
      rw [hkeep "n" (not_ext_of_not_prefix (by decide))
        (fun i _ => lit_ne_envName ⟨_, rfl⟩ (by decide) i)]
      exact hvn
    have hkv₁ : σ₁.vars "kv" = (u : ℕ) := by
      rw [hkeep "kv" (not_ext_of_not_prefix (by decide))
        (fun i _ => lit_ne_envName ⟨_, rfl⟩ (by decide) i)]
      exact hkv
    have hev₁ : σ₁.vars (envName 0) = (u : ℕ) := by
      rw [hkeep _ (not_ext_envName hEbb 0) (fun i hi => envName_ne_of_lt (by omega))]
      exact hev
    have hcol₁ : BotEnv n (sigL cap mb jd) jd C' σ₁ := fun c hc => by
      rw [hfa₁ (colName jd c) (not_ext_of_fresh hEbb (not_ext_b_colName jd c))]
      exact hcol c hc
    have hmem₁ : BaseMem B q_top cap mb jd φ σ₁ :=
      fun i hi => botMem_of_length hlen₁ _ "bb" (hmem i hi)
    have htabarr₁ : ∀ (i : ℕ), i < (tablesAt q_top cap mb φ jd).length →
        σ₁.arrs (tabName jd i) = σ.arrs (tabName jd i) :=
      fun i _ => hfa₁ (tabName jd i) (not_ext_of_fresh hEbb (not_ext_b_tabName jd i))
    -- the store of the bit into the head's table, at the entry
    obtain ⟨Tp, hTp⟩ := htab p hp
    have hTp₁ : σ₁.arrs (tabName jd p) = arrOf n Tp := by rw [htabarr₁ p hp]; exact hTp
    have hst := Run.store (B := B) (a := tabName jd p) (i := .var "kv") (e := .var "bb")
      (σ := σ₁) (by rw [evalB_var (by omega), hkv₁]) (by rw [evalB_var (by omega)])
      (by rw [hTp₁, length_arrOf]; exact u.isLt)
    set σ₂ := σ₁.setArr (tabName jd p) (u : ℕ) (σ₁.vars "bb") with hσ₂def
    have hlen₂ : ∀ a, (σ₂.arrs a).length = (σ₁.arrs a).length := fun a => by
      rw [hσ₂def]; exact length_arrs_setArr ..
    have harr₂ : ∀ (i : ℕ), i ≠ p → σ₂.arrs (tabName jd i) = σ₁.arrs (tabName jd i) :=
      fun i hi => by rw [hσ₂def, arrs_setArr, if_neg (RamDriverBase.tabName_ne_of_ne jd hi)]
    have hTp₂ : σ₂.arrs (tabName jd p) =
        arrOf n (fun k => if k = (u : ℕ) then σ₁.vars "bb" else Tp k) := by
      rw [hσ₂def, arrs_setArr, if_pos rfl, hTp₁, set_arrOf]
    -- the tail
    obtain ⟨σ₃, hrun₃, hbase₃, hkv₃, hev₃, htab₃⟩ :=
      (ih (p + 1) hltail).run (σ := σ₂)
        ⟨⟨by rw [hσ₂def, vars_setArr]; exact hvn₁,
          fun c hc => by
            rw [hσ₂def, arrs_setArr, if_neg (colName_ne_tabName jd c jd p)]; exact hcol₁ c hc,
          fun i hi => botMem_of_length hlen₂ _ "bb" (hmem₁ i hi)⟩,
          by rw [hσ₂def, vars_setArr]; exact hkv₁,
          by rw [hσ₂def, vars_setArr]; exact hev₁,
          fun i hi => by
            by_cases hip : i = p
            · subst hip; exact ⟨_, hTp₂⟩
            · rw [harr₂ i hip, htabarr₁ i hi]; exact htab i hi⟩
    refine ⟨σ₃, _, (hrun₁.seq hst).seq hrun₃, ?_, hbase₃, hkv₃, hev₃, fun i hi => ?_⟩
    · rw [blockCost]
      simp only [size_var]
      omega
    obtain ⟨Tb, Tb₂, hTb, hTb₂, hoff, hin, hout⟩ := htab₃ i hi
    obtain ⟨Tb₀, hTb₀⟩ := htab i hi
    by_cases hip : i = p
    · -- the head's own table: the tail did not touch it, and the store put the bit in
      subst hip
      have h₂ : ∀ z < n, Tb₂ z = if z = (u : ℕ) then σ₁.vars "bb" else Tp z :=
        fun z hz => eq_of_arrOf_eq (hTb₂.symm.trans hTp₂) hz
      have h₀ : ∀ z < n, Tb₀ z = Tp z :=
        fun z hz => eq_of_arrOf_eq (hTb₀.symm.trans hTp) hz
      have hbbu : Tb (u : ℕ) = σ₁.vars "bb" := by
        rw [hout (Or.inl (by omega)), h₂ _ u.isLt, if_pos rfl]
      refine ⟨Tb, Tb₀, hTb, hTb₀, fun z hz hzu => ?_, fun _ _ => ?_, fun hc => ?_⟩
      · rw [hoff z hz hzu, h₂ z hz, if_neg hzu, h₀ z hz]
      · rw [hbbu]
        exact ⟨hb1, hbiff1⟩
      · exact absurd hc (by simp only [List.length_cons]; omega)
    · -- any other table: the store missed it, so the tail's readings are the entering ones
      have h₂ : ∀ z < n, Tb₂ z = Tb₀ z := fun z hz =>
        eq_of_arrOf_eq (hTb₂.symm.trans
          ((harr₂ i hip).trans ((htabarr₁ i hi).trans hTb₀))) hz
      refine ⟨Tb, Tb₀, hTb, hTb₀, fun z hz hzu => ?_, fun h₁ h₂' => ?_, fun hc => ?_⟩
      · rw [hoff z hz hzu, h₂ z hz]
      · exact hin (by omega) (by simp only [List.length_cons] at h₂'; omega)
      · rw [hout ?_, h₂ _ u.isLt]
        rcases hc with hc | hc
        · exact Or.inl (by omega)
        · exact Or.inr (by simp only [List.length_cons] at hc; omega)

/-- The row body's own write set, as the frames of the turn read it. -/
theorem notMem_warrs_killFold {q_top cap mb jd : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ jd, IsLocal β) {a : String}
    (htab : ∀ i, a ≠ tabName jd i) (hext : ¬ Ext "bb" a) :
    a ∉ (foldIdx (fun i β =>
      Com.seq (botCom jd β "bb") (.store (tabName jd i) (.var "kv") (.var "bb"))) 0
      (tablesAt q_top cap mb φ jd)).warrs := by
  intro h
  rcases RamDriverWrites.warrs_killFold jd _ 0 hlocal a h with ⟨i, hi⟩ | h'
  · exact htab i hi
  · exact hext h'

/-! ### §2 The buffer loop

The invariant: the child's tables are there, and every entry the counter
has passed that the guard accepted holds its row. The entries are in no
order, so this is a statement about a *set* of cells and not about a
prefix — which is what §1's pointwise fold spec is for. -/

/-- What the kill loop carries. -/
def KillInv (B q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) (C' : ℕ → ℕ → ℕ)
    (M Xa : ℕ → ℕ) {n : ℕ} (w : Fin mb → Fin n) (σ : Env) : Prop :=
  BaseBase B n q_top cap mb (j + 1) C' φ σ ∧
    σ.arrs "wa" = arrOf mb (waCell mb w) ∧
    σ.arrs (alvName j) = arrOf n M ∧ σ.arrs (cluName j) = arrOf n Xa ∧
    σ.vars "kk" ≤ mb ∧
    ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ (j + 1)).length), ∃ Tb : ℕ → ℕ,
      σ.arrs (tabName (j + 1) i) = arrOf n Tb ∧
      ∀ p : Fin mb, (p : ℕ) < σ.vars "kk" → M (w p : ℕ) ≠ 0 → Xa (w p : ℕ) ≠ 0 →
        Tb (w p : ℕ) ≤ 1 ∧ (Tb (w p : ℕ) ≠ 0 ↔
          Sat (⊥ : SimpleGraph (Fin n)) (colRead n C' (sigL cap mb (j + 1)))
            (fun _ => w p) (tablesAt q_top cap mb φ (j + 1))[i])

/-- The cost of one turn of the kill loop: the row body, the entry read,
the guard, and the counter. -/
noncomputable def killTurnCost (q_top cap mb jd : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  blockCost (tablesAt q_top cap mb φ jd) + 17

/-- The cost of the whole pass: **carrier-blind**, linear in the buffer's
width. -/
noncomputable def killCost (q_top cap mb jd : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  (killTurnCost q_top cap mb jd φ + 4) * mb + 6

/-- **One turn of the kill loop.** The entry is read, the guard decides
whether it is a kill of this turn, and if it is, its child row is
written. Nothing else of any table moves, which is why the rows already
written survive — and why the padding's repeated entry is harmless: it is
re-killed to the same row. -/
theorem killTurn_spec {B q_top cap mb j : ℕ} {C' : ℕ → ℕ → ℕ} {φ : Lax3.FirstOrder.FO 0}
    {M Xa : ℕ → ℕ} {w : Fin mb → Fin n}
    (hB : 1 < B) (hn : n < B) (hmbB : mb < B)
    (hbit : ∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1)
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ (j + 1), IsLocal β)
    (hMB : ∀ z < n, M z < B) (hXa1 : ∀ z < n, Xa z ≤ 1) :
    Spec B (fun σ => KillInv B q_top cap mb j φ C' M Xa w σ ∧
        (Cond.lt (.var "kk") (.lit mb)).evalB B σ = some true)
      (.seq (.assign "kv" (.get "wa" (.var "kk")))
        (.seq (.ite (.lt (.lit 0)
                (.mul (.get (alvName j) (.var "kv")) (.get (cluName j) (.var "kv"))))
                (.seq (.assign (envName 0) (.var "kv"))
                  (foldIdx (fun i β =>
                      .seq (botCom (j + 1) β "bb")
                        (.store (tabName (j + 1) i) (.var "kv") (.var "bb"))) 0
                    (tablesAt q_top cap mb φ (j + 1))))
                .skip)
          (.assign "kk" (.add (.var "kk") (.lit 1)))))
      (fun σ σ' => KillInv B q_top cap mb j φ C' M Xa w σ' ∧
        mb - σ'.vars "kk" < mb - σ.vars "kk")
      (killTurnCost q_top cap mb (j + 1) φ) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨⟨hvn, hcol, hmem⟩, hwa, halv, hclu, hkkle, htab⟩, hcond⟩ := hσ
  have hkkB : σ.vars "kk" < B := by omega
  have hkk : σ.vars "kk" < mb := by
    rw [evalB_condLt (evalB_var hkkB) (evalB_lit hmbB)] at hcond
    simpa using hcond
  set p₀ : Fin mb := ⟨σ.vars "kk", hkk⟩ with hp₀
  set u : Fin n := w p₀ with hu
  have hp₀val : (p₀ : ℕ) = σ.vars "kk" := rfl
  have huB : (u : ℕ) < B := by have := u.isLt; omega
  -- the entry
  have hgetwa : (Expr.get "wa" (.var "kk")).evalB B σ = some (u : ℕ) := by
    refine evalB_get (evalB_var hkkB) ?_ huB
    rw [hwa, getElem?_arrOf _ hkk, waCell, dif_pos hkk]
  have hr₁ := Run.assign (B := B) (x := "kv") (σ := σ) hgetwa
  set σ₁ := σ.setVar "kv" (u : ℕ) with hσ₁
  have hkv₁ : σ₁.vars "kv" = (u : ℕ) := by rw [hσ₁, vars_setVar, if_pos rfl]
  have harrs₁ : ∀ a, σ₁.arrs a = σ.arrs a := fun a => by rw [hσ₁, arrs_setVar]
  -- the guard
  have hguard : (Cond.lt (.lit 0)
      (.mul (.get (alvName j) (.var "kv")) (.get (cluName j) (.var "kv")))).evalB B σ₁ =
      some (decide (0 < M (u : ℕ) * Xa (u : ℕ))) := by
    refine evalB_condLt (evalB_lit (by omega)) (evalB_bin ?_ ?_ ?_)
    · exact evalB_get (evalB_var (by rw [hkv₁]; exact huB))
        (by rw [hkv₁, harrs₁, halv, getElem?_arrOf _ u.isLt]) (hMB _ u.isLt)
    · exact evalB_get (evalB_var (by rw [hkv₁]; exact huB))
        (by rw [hkv₁, harrs₁, hclu, getElem?_arrOf _ u.isLt])
        (lt_of_le_of_lt (hXa1 _ u.isLt) hB)
    · have h₁ := hMB _ u.isLt
      have h₂ := hXa1 _ u.isLt
      simp only [Bop.apply_mul]
      calc M (u : ℕ) * Xa (u : ℕ) ≤ M (u : ℕ) * 1 := Nat.mul_le_mul_left _ h₂
        _ < B := by omega
  -- the counter, off whichever branch ran
  have hstep : ∀ τ : Env, τ.vars "kk" = σ.vars "kk" →
      Run B (.assign "kk" (.add (.var "kk") (.lit 1))) τ
        (τ.setVar "kk" (σ.vars "kk" + 1)) 4 := by
    intro τ hτ
    refine (Run.assign (B := B) (x := "kk") (σ := τ)
      (evalB_bin (evalB_var (by rw [hτ]; exact hkkB)) (evalB_lit (by omega)) ?_)).congr ?_
      |>.mono (by simp)
    · simp only [Bop.apply_add, hτ]; omega
    · rw [hτ]; simp only [Bop.apply_add]
  by_cases hkill : 0 < M (u : ℕ) * Xa (u : ℕ)
  · -- a kill: the environment slot and the row body
    have hkilled : M (u : ℕ) ≠ 0 ∧ Xa (u : ℕ) ≠ 0 := by
      constructor <;> intro hc <;> simp [hc] at hkill
    have hr₂ := Run.assign (B := B) (x := envName 0) (σ := σ₁)
      (evalB_var (by rw [hkv₁]; exact huB))
    set σ₂ := σ₁.setVar (envName 0) (σ₁.vars "kv") with hσ₂
    have harrs₂ : ∀ a, σ₂.arrs a = σ.arrs a := fun a => by
      rw [hσ₂, arrs_setVar, harrs₁]
    have hkv₂ : σ₂.vars "kv" = (u : ℕ) := by
      rw [hσ₂, vars_setVar, if_neg (by simp [envName, String.ext_iff]), hkv₁]
    have hev₂ : σ₂.vars (envName 0) = (u : ℕ) := by
      rw [hσ₂, vars_setVar, if_pos rfl, hkv₁]
    have hkk₂ : σ₂.vars "kk" = σ.vars "kk" := by
      rw [hσ₂, vars_setVar, if_neg (by simp [envName, String.ext_iff]), hσ₁, vars_setVar,
        if_neg (by decide)]
    obtain ⟨σ₃, hr₃, ⟨hvn₃, hcol₃, hmem₃⟩, hkv₃, hev₃, htab₃⟩ :=
      (killFold_spec (u := u) hB hn hbit hlocal (tablesAt q_top cap mb φ (j + 1)) 0
        (by rw [List.drop_zero])).run (σ := σ₂)
        ⟨⟨by rw [hσ₂, vars_setVar, if_neg (by simp [envName, String.ext_iff]), hσ₁,
              vars_setVar, if_neg (by decide)]; exact hvn,
          fun c hc => by rw [harrs₂]; exact hcol c hc,
          fun i hi => botMem_of_length (fun a => by rw [harrs₂]) _ "bb" (hmem i hi)⟩,
          hkv₂, hev₂, fun i hi => by rw [harrs₂]; exact (htab i hi).imp fun _ h => h.1⟩
    -- the frames of the row body
    have hfold : ∀ a : String, (∀ i, a ≠ tabName (j + 1) i) → ¬ Ext "bb" a →
        σ₃.arrs a = σ₂.arrs a :=
      fun a hta he => hr₃.frame_arr a (notMem_warrs_killFold hlocal hta he)
    have hkk₃ : σ₃.vars "kk" = σ.vars "kk" := by
      rw [hr₃.frame_var "kk" (fun hm => ?_), hkk₂]
      rcases RamDriverWrites.wvars_killFold (j + 1) _ 0 hlocal "kk" hm with h | ⟨i, -, h⟩
      · exact absurd h (not_ext_of_not_prefix (by decide))
      · exact absurd h (lit_ne_envName ⟨_, rfl⟩ (by decide) i)
    have hr₄ := hstep σ₃ hkk₃
    refine ⟨σ₃.setVar "kk" (σ.vars "kk" + 1), _,
      hr₁.seq ((Run.ite_true (by rw [hguard]; simp [hkill]) (hr₂.seq hr₃)).seq hr₄), ?_,
      ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, by rw [vars_setVar, if_pos rfl]; omega⟩
    · rw [killTurnCost]
      simp only [size_var, size_lit, size_bin, size_get, size_condLt]
      omega
    · rw [vars_setVar, if_neg (by decide)]; exact hvn₃
    · exact fun c hc => by rw [arrs_setVar]; exact hcol₃ c hc
    · exact fun i hi => botMem_of_length (fun a => by rw [arrs_setVar]) _ "bb" (hmem₃ i hi)
    · rw [arrs_setVar, hfold "wa" (fun i => by simp [tabName, String.ext_iff])
        (not_ext_of_not_prefix (by decide)), harrs₂]
      exact hwa
    · rw [arrs_setVar, hfold _ (fun i => alvName_ne_tabName j (j + 1) i)
        (fun h => not_ext_b_alvName j (RamDriverCompose.ext_b_of_ext_bb h)), harrs₂]
      exact halv
    · rw [arrs_setVar, hfold _ (fun i => by simp [cluName, tabName, String.ext_iff])
        (by rw [cluName]; exact DeadSweep.not_ext_bb_append (p := "clu") rfl (by decide) _),
        harrs₂]
      exact hclu
    · rw [vars_setVar, if_pos rfl]; omega
    · -- the rows: the entry's is the bit, and the others come back
      intro i hi
      obtain ⟨Tb, Tb₂, hTb, hTb₂, hoff, hin, -⟩ := htab₃ i hi
      obtain ⟨Tb₀, hTb₀, hval₀⟩ := htab i hi
      have h₂₀ : ∀ z < n, Tb₂ z = Tb₀ z := fun z hz =>
        eq_of_arrOf_eq (hTb₂.symm.trans ((harrs₂ _).trans hTb₀)) hz
      refine ⟨Tb, by rw [arrs_setVar]; exact hTb, fun p hp hM hX => ?_⟩
      rw [vars_setVar, if_pos rfl] at hp
      by_cases hpu : (w p : ℕ) = (u : ℕ)
      · have hwp : w p = u := Fin.ext hpu
        rw [hwp]
        exact hin (by omega) (by omega)
      · have hplt : (p : ℕ) < σ.vars "kk" := by
          rcases Nat.lt_or_ge (p : ℕ) (σ.vars "kk") with h | h
          · exact h
          · exact absurd (by rw [hu, hp₀, show p = p₀ from Fin.ext (by omega)]) hpu
        rw [hoff _ (w p).isLt hpu, h₂₀ _ (w p).isLt]
        exact hval₀ p hplt hM hX
  · -- not a kill: the guard skips, and nothing is written
    have hr₄ := hstep σ₁ (by rw [hσ₁, vars_setVar, if_neg (by decide)])
    refine ⟨σ₁.setVar "kk" (σ.vars "kk" + 1), _,
      hr₁.seq ((Run.ite_false (by rw [hguard]; simp [hkill]) Run.skip).seq hr₄), ?_,
      ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, by rw [vars_setVar, if_pos rfl]; omega⟩
    · rw [killTurnCost]
      have := one_le_blockCost (tablesAt q_top cap mb φ (j + 1))
      simp only [size_var, size_lit, size_bin, size_get, size_condLt]
      omega
    · rw [vars_setVar, if_neg (by decide), hσ₁, vars_setVar, if_neg (by decide)]; exact hvn
    · exact fun c hc => by rw [arrs_setVar, harrs₁]; exact hcol c hc
    · exact fun i hi =>
        botMem_of_length (fun a => by rw [arrs_setVar, harrs₁]) _ "bb" (hmem i hi)
    · rw [arrs_setVar, harrs₁]; exact hwa
    · rw [arrs_setVar, harrs₁]; exact halv
    · rw [arrs_setVar, harrs₁]; exact hclu
    · rw [vars_setVar, if_pos rfl]; omega
    · intro i hi
      obtain ⟨Tb₀, hTb₀, hval₀⟩ := htab i hi
      refine ⟨Tb₀, by rw [arrs_setVar, harrs₁]; exact hTb₀, fun p hp hM hX => ?_⟩
      rw [vars_setVar, if_pos rfl] at hp
      have hplt : (p : ℕ) < σ.vars "kk" := by
        rcases Nat.lt_or_ge (p : ℕ) (σ.vars "kk") with h | h
        · exact h
        · exfalso
          have hpp : p = p₀ := Fin.ext (by omega)
          rw [hpp, ← hu] at hM hX
          exact hkill (Nat.pos_of_ne_zero (Nat.mul_ne_zero hM hX))
      exact hval₀ p hplt hM hX

end Lax3Proofs.Refine.KillPass
