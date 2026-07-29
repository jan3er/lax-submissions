import Lax3Proofs.RamDriverBase

/-!
The **base case of the driver**, walked: `Lax3Proofs.RamDriver.baseCom`
against `Lax3Proofs.BotEval`.

At depth `ℓ` the arena is edgeless and the tables are evaluated
outright. The pass is the representative scan `RamDriver.reprCom`
followed by a walk of the carrier that runs, at every vertex, the
generated evaluator `RamDriver.botCom` of every formula of the bottom
table and stores its bit.

# What is proved here

* `repr_spec` — **the representative scan**. Its invariant is *the rep
  table holds one representative of every row realized below the
  counter, and its entries are pairwise row-distinct*; the second half
  is what bounds the table's length by `2 ^ sigL cap mb ℓ`
  (`le_two_pow_of_rowEq_inj`) and hence what gives the recording store a
  derivation at all. The first half is `BotEval.exists_offRepr`'s
  conclusion read off the program, and is exported.
* `bot_spec` — **the generated evaluator**, by induction on the formula.
  The five atoms are `BotEval.sat_adj_bot`, `sat_eq_bot`,
  `sat_color_bot`, `sat_distLe_bot` and `sat_distColorLt_bot`, all three
  through the one shape `test_spec`; the connectives are truncated
  arithmetic; the local quantifier is `BotEval.sat_exL_bot`, its guard
  set loaded by `guardFold_spec` and scanned by `Spec.forRangeZero`.
  The fresh-name discipline is `Ext`, a `List.IsPrefix` on the names,
  and the frame it gives is `bot_framed`.
* `base_block_spec`, `base_turn_spec`, `base_spec` — **the pass**: the
  straight line of fragments of one vertex, one turn, and the walk of
  the carrier, ending in `BaseTabOk … (fun _ => n)`, which is
  `RamDriver.TableInv`'s content on the edgeless arena.
* the syntactic frames the obligation's own bookkeeping needs:
  `wvars_botCom`, `warrs_botCom`, `wvars_baseCom`, `warrs_baseCom`,
  `noWrite_baseCom`.

# The unrestricted quantifier

`botCom`'s `exU` case is **not** walked, and cannot be. Its candidate
list is the environment together with the *global* representative table,
one vertex per row of the whole arena, while
`BotEval.sat_exU_bot_of_repr` asks for one representative per row
realized **off the environment**: a row realized by an entry of the
environment and by exactly one vertex outside it makes the generated
loop answer *false* where the truth is *true* (`n = 2`, no colours,
`m = (0)`, `ψ = ∃x₁. x₁ ≠ x₀`). The case is also never reached — every
tabled formula is local, by
`FormulaTables.tableRank_of_mem_tablesAt` — so the walk carries
`IsLocal` and discharges `exU` by `SyntaxLemmas.isLocal_exU`. Repairing
`reprCom` would mean recording `k + 1` vertices per row; nothing above
depends on that being done.

# What is left

`RamDriver.BaseImplements` itself is **not** discharged here. What
remains is the translation of `base_spec` into that surface — the frame
of `RamDriver.LevelPre` across the pass, which the four syntactic
lemmas above deliver. The two clauses the surface was missing are now
conjuncts of it:

* **the colour cells are bits** (`∀ c < sigL cap mb ℓ, ∀ v < n,
  C c v ≤ 1`) is a hypothesis of `RamDriver.BaseImplements` and of
  `RamDriver.LevelImplements`, produced one depth at a time by
  `RamDriverCluster.ColourStep`, whose postcondition now carries it;
* **the base evaluator's memory** is `RamDriver.BaseArrs`, the
  representative table at `2 ^ sigL cap mb ℓ` together with
  `RamDriver.BaseMem` — the candidate array of every local quantifier of
  every formula of the bottom table. Both are lengths, so `BaseArrs.run`
  carries them down the recursion and back; `RamDriver.BotMem` and
  `botMem_of_length` live at the surface for the same reason.
-/

namespace Lax3Proofs.RamDriverBot

open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.SyntaxLemmas
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverBase
open Lax3Proofs.RamBfs (masked)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ### Rows, and how many there are

The base case's only question about a vertex is which colours it
carries. The scan compares two vertices by comparing the *cells* of the
depth's colour arrays, so the row it works with is the numeric one; on
arrays holding bits — which is what every pass that writes a colour
array leaves — that is the row of `Lax3Proofs.BotEval.rowOf`, and there
are `2 ^ L` of them. -/

/-- Two vertices agree on every colour cell of the depth. -/
def RowEq (C : ℕ → ℕ → ℕ) (L u v : ℕ) : Prop := ∀ c < L, C c u = C c v

theorem rowEq_refl (C : ℕ → ℕ → ℕ) (L u : ℕ) : RowEq C L u u := fun _ _ => rfl

theorem RowEq.symm {C : ℕ → ℕ → ℕ} {L u v : ℕ} (h : RowEq C L u v) : RowEq C L v u :=
  fun c hc => (h c hc).symm

/-- **Row equality on bit cells is equality of colour rows.** -/
theorem rowEq_iff_rowOf {C : ℕ → ℕ → ℕ} {L n : ℕ} (hbit : ∀ c < L, ∀ v < n, C c v ≤ 1)
    {u v : Fin n} : RowEq C L (u : ℕ) (v : ℕ) ↔
      BotEval.rowOf (colRead n C L) u = BotEval.rowOf (colRead n C L) v := by
  rw [BotEval.rowOf_eq_iff]
  constructor
  · intro h c
    rw [mem_colRead, mem_colRead, h (c : ℕ) c.isLt]
  · intro h c hc
    have h' := h ⟨c, hc⟩
    rw [mem_colRead, mem_colRead] at h'
    have h1 := hbit c hc (u : ℕ) u.isLt
    have h2 := hbit c hc (v : ℕ) v.isLt
    simp only at h'
    omega

/-- **There are at most `2 ^ L` rows.** A family of pairwise
row-distinct vertices is therefore no longer than that, which is why the
representative scan never runs off the end of its table. -/
theorem le_two_pow_of_rowEq_inj {C : ℕ → ℕ → ℕ} {L n m : ℕ} {R : ℕ → ℕ}
    (hbit : ∀ c < L, ∀ v < n, C c v ≤ 1) (hRn : ∀ w < m, R w < n)
    (hinj : ∀ w < m, ∀ w' < m, RowEq C L (R w) (R w') → w = w') : m ≤ 2 ^ L := by
  classical
  have hf : Function.Injective (fun w : Fin m => fun c : Fin L => decide (C (c : ℕ) (R w) ≠ 0)) := by
    intro w w' hww
    refine Fin.ext (hinj w w.isLt w' w'.isLt fun c hc => ?_)
    have h := congrFun hww ⟨c, hc⟩
    simp only [decide_eq_decide] at h
    have h1 := hbit c hc (R w) (hRn w w.isLt)
    have h2 := hbit c hc (R w') (hRn w' w'.isLt)
    omega
  have h := Nat.card_le_card_of_injective _ hf
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using h

/-! ### The representative pass

`RamDriver.reprCom` is a scan of the carrier inside which a scan of the
table already built decides whether the vertex's row has been seen. The
outer invariant is **the rep table holds one representative of every row
realized below the counter, and its entries are pairwise row-distinct**;
the second half is what bounds the table's length, by
`le_two_pow_of_rowEq_inj`, and hence what makes the recording store have
a derivation at all. -/

/-- The invariant of the representative scan. -/
def ReprInv (n L jd : ℕ) (C : ℕ → ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "z" ≤ n ∧ σ.vars "rp" ≤ 2 ^ L ∧
    (∀ c < L, σ.arrs (colName jd c) = arrOf n (C c)) ∧
    ∃ R : ℕ → ℕ, σ.arrs "rep" = arrOf (2 ^ L) R ∧
      (∀ w < σ.vars "rp", R w < n) ∧
      (∀ w < σ.vars "rp", ∀ w' < σ.vars "rp", RowEq C L (R w) (R w') → w = w') ∧
      (∀ v < σ.vars "z", ∃ w < σ.vars "rp", RowEq C L v (R w))

/-- The invariant of the inner scan of one turn: the hit flag is the
disjunction over the table entries passed. -/
def SeenInv (n L jd : ℕ) (C : ℕ → ℕ → ℕ) (z₀ rp₀ : ℕ) (R : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "z" = z₀ ∧ σ.vars "rp" = rp₀ ∧ σ.vars "rw" ≤ rp₀ ∧
    (∀ c < L, σ.arrs (colName jd c) = arrOf n (C c)) ∧ σ.arrs "rep" = arrOf (2 ^ L) R ∧
    σ.vars "seen" ≤ 1 ∧ (σ.vars "seen" ≠ 0 ↔ ∃ w < σ.vars "rw", RowEq C L z₀ (R w))

/-- The size of the disjunction bit. -/
theorem size_orBitExpr (e f : Expr) : (orBitExpr e f).size = e.size + f.size + 7 := by
  rw [orBitExpr]
  simp only [size_bin, size_lit]
  omega

/-- The cost of one turn of the inner scan. -/
def scanCost (jd L : ℕ) : ℕ :=
  (orBitExpr (.var "seen") (rowEqExpr jd L "z" "rv")).size + 8

/-- The cost of one turn of the representative scan. -/
def reprBodyCost (jd L : ℕ) : ℕ := (scanCost jd L + 4) * 2 ^ L + 23

/-- The cost of the representative pass. -/
def reprCost (jd L n : ℕ) : ℕ := (reprBodyCost jd L + 4) * n + 8

/-- **One turn of the inner scan**: read the next recorded vertex, test
its row against the vertex being scanned, accumulate. -/
theorem repr_scan_body {B n L jd z₀ rp₀ : ℕ} {C : ℕ → ℕ → ℕ} {R : ℕ → ℕ}
    (hB : 1 < B) (hn : n < B) (hL : 2 ^ L < B) (hbit : ∀ c < L, ∀ v < n, C c v ≤ 1)
    (hz₀ : z₀ < n) (hrpL : rp₀ ≤ 2 ^ L) (hRn : ∀ w < rp₀, R w < n) :
    Spec B (fun σ => SeenInv n L jd C z₀ rp₀ R σ ∧ σ.vars "rw" < rp₀)
      (.seq (.assign "rv" (.get "rep" (.var "rw")))
        (.seq (.assign "seen" (orBitExpr (.var "seen") (rowEqExpr jd L "z" "rv")))
          (.assign "rw" (.add (.var "rw") (.lit 1)))))
      (fun σ σ' => SeenInv n L jd C z₀ rp₀ R σ' ∧ σ'.vars "rw" = σ.vars "rw" + 1)
      (scanCost jd L) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hnn, hz, hrp, hrwle, hcol, hrep, hseen1, hseeniff⟩, hrwlt⟩ := hσ
  have hbnd : ∀ c < L, ∀ v < n, C c v < B := fun c hc v hv =>
    lt_of_le_of_lt (hbit c hc v hv) hB
  have hrwB : σ.vars "rw" < B := by omega
  have hRlt : R (σ.vars "rw") < n := hRn _ (by omega)
  -- the recorded vertex
  have hidx : (Expr.get "rep" (.var "rw")).evalB B σ = some (R (σ.vars "rw")) := by
    refine evalB_get (evalB_var hrwB) ?_ (by omega)
    rw [hrep]
    exact getElem?_arrOf _ (by omega)
  set σ₁ := σ.setVar "rv" (R (σ.vars "rw")) with hσ₁def
  have hrun1 := Run.assign (B := B) (x := "rv") hidx
  -- the row test
  have hz₁ : σ₁.vars "z" = z₀ := by rw [hσ₁def, vars_setVar, if_neg (by decide)]; exact hz
  have hrv₁ : σ₁.vars "rv" = R (σ.vars "rw") := by rw [hσ₁def, vars_setVar, if_pos rfl]
  have hseen₁ : σ₁.vars "seen" = σ.vars "seen" := by
    rw [hσ₁def, vars_setVar, if_neg (by decide)]
  obtain ⟨u, hu1, hueval, huiff⟩ :=
    evalB_rowEqExpr (B := B) (n := n) (j := jd) (L := L) (C := C) (x := "z") (y := "rv")
      (σ := σ₁) hB (by rw [hz₁]; exact hz₀) (by rw [hrv₁]; exact hRlt) hn
      (fun c hc => by rw [hσ₁def, arrs_setVar]; exact hcol c hc) hbnd
  rw [hz₁, hrv₁] at huiff
  obtain ⟨t, ht1, hteval, htiff⟩ :=
    evalB_orBitExpr (B := B) (σ := σ₁) hB (show σ₁.vars "seen" ≤ 1 by omega) hu1
      (evalB_var (by omega)) hueval
  set σ₂ := σ₁.setVar "seen" t with hσ₂def
  have hrun2 := Run.assign (B := B) (x := "seen") hteval
  -- the counter
  have hrw₂ : σ₂.vars "rw" = σ.vars "rw" := by
    rw [hσ₂def, vars_setVar, if_neg (by decide), hσ₁def, vars_setVar, if_neg (by decide)]
  have hstep : (Expr.add (.var "rw") (.lit 1)).evalB B σ₂ = some (σ.vars "rw" + 1) := by
    have h := evalB_bin (B := B) (op := .add) (σ := σ₂)
      (evalB_var (x := "rw") (by rw [hrw₂]; omega))
      (evalB_lit (show 1 < B by omega)) (by simp only [Bop.apply_add, hrw₂]; omega)
    simpa [hrw₂] using h
  set σ₃ := σ₂.setVar "rw" (σ.vars "rw" + 1) with hσ₃def
  have hrun3 := Run.assign (B := B) (x := "rw") hstep
  refine ⟨σ₃, _, hrun1.seq (hrun2.seq hrun3), by simp [scanCost]; omega, ⟨?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ?_⟩
  · rw [hσ₃def, vars_setVar, if_neg (by decide), hσ₂def, vars_setVar, if_neg (by decide),
      hσ₁def, vars_setVar, if_neg (by decide)]
    exact hnn
  · rw [hσ₃def, vars_setVar, if_neg (by decide), hσ₂def, vars_setVar, if_neg (by decide)]
    exact hz₁
  · rw [hσ₃def, vars_setVar, if_neg (by decide), hσ₂def, vars_setVar, if_neg (by decide),
      hσ₁def, vars_setVar, if_neg (by decide)]
    exact hrp
  · rw [hσ₃def, vars_setVar, if_pos rfl]
    omega
  · intro c hc
    rw [hσ₃def, arrs_setVar, hσ₂def, arrs_setVar, hσ₁def, arrs_setVar]
    exact hcol c hc
  · rw [hσ₃def, arrs_setVar, hσ₂def, arrs_setVar, hσ₁def, arrs_setVar]
    exact hrep
  · rw [hσ₃def, vars_setVar, if_neg (by decide), hσ₂def, vars_setVar, if_pos rfl]
    exact ht1
  · have hv3seen : σ₃.vars "seen" = t := by
      rw [hσ₃def, vars_setVar, if_neg (by decide), hσ₂def, vars_setVar, if_pos rfl]
    have hv3rw : σ₃.vars "rw" = σ.vars "rw" + 1 := by
      rw [hσ₃def, vars_setVar, if_pos rfl]
    rw [hv3seen, hv3rw, htiff, hseen₁, hseeniff, huiff]
    constructor
    · rintro (⟨w, hw, hrow⟩ | hrow)
      · exact ⟨w, by omega, hrow⟩
      · exact ⟨σ.vars "rw", by omega, hrow⟩
    · rintro ⟨w, hw, hrow⟩
      rcases Nat.lt_or_ge w (σ.vars "rw") with h | h
      · exact Or.inl ⟨w, h, hrow⟩
      · have : w = σ.vars "rw" := by omega
        exact Or.inr (this ▸ hrow)
  · rw [hσ₃def, vars_setVar, if_pos rfl]

/-- **One turn of the representative scan.** The inner scan decides
whether the vertex's row has been recorded; if it has not, the vertex is
recorded, and the table is long enough for it because its entries are
pairwise row-distinct. -/
theorem repr_turn_spec {B n L jd : ℕ} {C : ℕ → ℕ → ℕ}
    (hB : 1 < B) (hn : n < B) (hL : 2 ^ L < B) (hbit : ∀ c < L, ∀ v < n, C c v ≤ 1) :
    Spec B (fun σ => ReprInv n L jd C σ ∧ σ.vars "z" < n)
      (.seq (.assign "seen" (.lit 0))
        (.seq (.assign "rw" (.lit 0))
          (.seq (.while (.lt (.var "rw") (.var "rp"))
                  (.seq (.assign "rv" (.get "rep" (.var "rw")))
                    (.seq (.assign "seen" (orBitExpr (.var "seen") (rowEqExpr jd L "z" "rv")))
                      (.assign "rw" (.add (.var "rw") (.lit 1))))))
            (.seq (.ite (.lt (.lit 0) (.var "seen")) .skip
                    (.seq (.store "rep" (.var "rp") (.var "z"))
                      (.assign "rp" (.add (.var "rp") (.lit 1)))))
              (.assign "z" (.add (.var "z") (.lit 1)))))))
      (fun σ σ' => ReprInv n L jd C σ' ∧ σ'.vars "z" = σ.vars "z" + 1)
      (reprBodyCost jd L) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hnn, hzle, hrple, hcol, R, hrep, hRn, hinj, hcov⟩, hzlt⟩ := hσ
  -- the two initializations
  have hrun1 := Run.assign (B := B) (x := "seen") (e := .lit 0) (σ := σ)
    (evalB_lit (show 0 < B by omega))
  set σ₁ := σ.setVar "seen" 0 with hσ₁def
  have hrun2 := Run.assign (B := B) (x := "rw") (e := .lit 0) (σ := σ₁)
    (evalB_lit (show 0 < B by omega))
  set σ₂ := σ₁.setVar "rw" 0 with hσ₂def
  have hI₂ : SeenInv n L jd C (σ.vars "z") (σ.vars "rp") R σ₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ₂def, vars_setVar, if_neg (by decide), hσ₁def, vars_setVar, if_neg (by decide)]
      exact hnn
    · rw [hσ₂def, vars_setVar, if_neg (by decide), hσ₁def, vars_setVar, if_neg (by decide)]
    · rw [hσ₂def, vars_setVar, if_neg (by decide), hσ₁def, vars_setVar, if_neg (by decide)]
    · rw [hσ₂def, vars_setVar, if_pos rfl]; omega
    · intro c hc
      rw [hσ₂def, arrs_setVar, hσ₁def, arrs_setVar]
      exact hcol c hc
    · rw [hσ₂def, arrs_setVar, hσ₁def, arrs_setVar]; exact hrep
    · rw [hσ₂def, vars_setVar, if_neg (by decide), hσ₁def, vars_setVar, if_pos rfl]; omega
    · have h1 : σ₂.vars "seen" = 0 := by
        rw [hσ₂def, vars_setVar, if_neg (by decide), hσ₁def, vars_setVar, if_pos rfl]
      have h2 : σ₂.vars "rw" = 0 := by rw [hσ₂def, vars_setVar, if_pos rfl]
      rw [h1, h2]
      simp
  -- the inner scan
  obtain ⟨σ₃, hrun3, hI₃, hrw₃⟩ :=
    (Spec.forRange (B := B) "rw" "rp" (SeenInv n L jd C (σ.vars "z") (σ.vars "rp") R)
      (σ.vars "rp") (scanCost jd L) ((scanCost jd L + 4) * 2 ^ L + 4)
      (fun τ hτ => by have := hτ.2.2.2.1; have := hτ.2.2.1; omega)
      (fun τ hτ => by have := hτ.2.2.1; omega)
      (fun τ hτ => hτ.2.2.1) (fun τ hτ => hτ.2.2.2.1)
      (repr_scan_body hB hn hL hbit hzlt hrple hRn) (fun τ hτ => hτ)
      (fun τ hτ => by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 4)).run hI₂
  obtain ⟨hn₃, hz₃, hrp₃, -, hcol₃, hrep₃, hseen₃, hseeniff₃⟩ := hI₃
  rw [hrw₃] at hseeniff₃
  have hseenB : σ₃.vars "seen" < B := by omega
  have hcond : (Cond.lt (.lit 0) (.var "seen")).evalB B σ₃ = some (decide (0 < σ₃.vars "seen")) :=
    evalB_condLt (evalB_lit (by omega)) (evalB_var hseenB)
  -- the recording step
  obtain ⟨σ₄, hrun4, hI₄, hz₄⟩ :
      ∃ σ₄, Run B (.ite (.lt (.lit 0) (.var "seen")) .skip
          (.seq (.store "rep" (.var "rp") (.var "z"))
            (.assign "rp" (.add (.var "rp") (.lit 1))))) σ₃ σ₄ 11 ∧
        ReprInv n L jd C (σ₄.setVar "z" (σ.vars "z" + 1)) ∧ σ₄.vars "z" = σ.vars "z" := by
    by_cases hseen : σ₃.vars "seen" = 0
    · -- a new row: record it
      have hnew : ¬ ∃ w < σ.vars "rp", RowEq C L (σ.vars "z") (R w) := by
        rw [← hseeniff₃]; simp [hseen]
      set R₁ : ℕ → ℕ := fun k => if k = σ.vars "rp" then σ.vars "z" else R k with hR₁def
      have hR₁lt : ∀ w < σ.vars "rp" + 1, R₁ w < n := by
        intro w hw
        rw [hR₁def]
        by_cases hwp : w = σ.vars "rp"
        · simpa [hwp] using hzlt
        · simp only [if_neg hwp]
          exact hRn w (by omega)
      have hR₁inj : ∀ w < σ.vars "rp" + 1, ∀ w' < σ.vars "rp" + 1,
          RowEq C L (R₁ w) (R₁ w') → w = w' := by
        intro w hw w' hw' hrow
        by_cases hwp : w = σ.vars "rp"
        · by_cases hw'p : w' = σ.vars "rp"
          · rw [hwp, hw'p]
          · refine absurd ⟨w', by omega, ?_⟩ hnew
            have : R₁ w = σ.vars "z" := by rw [hR₁def]; simp [hwp]
            have h' : R₁ w' = R w' := by rw [hR₁def]; simp [hw'p]
            rw [this, h'] at hrow
            exact hrow
        · by_cases hw'p : w' = σ.vars "rp"
          · refine absurd ⟨w, by omega, ?_⟩ hnew
            have : R₁ w' = σ.vars "z" := by rw [hR₁def]; simp [hw'p]
            have h' : R₁ w = R w := by rw [hR₁def]; simp [hwp]
            rw [this, h'] at hrow
            exact hrow.symm
          · have h1 : R₁ w = R w := by rw [hR₁def]; simp [hwp]
            have h2 : R₁ w' = R w' := by rw [hR₁def]; simp [hw'p]
            rw [h1, h2] at hrow
            exact hinj w (by omega) w' (by omega) hrow
      have hrplt : σ.vars "rp" < 2 ^ L := by
        have := le_two_pow_of_rowEq_inj (C := C) (L := L) (n := n) (R := R₁) hbit hR₁lt hR₁inj
        omega
      have hlen : σ.vars "rp" < (σ₃.arrs "rep").length := by
        rw [hrep₃, length_arrOf]; exact hrplt
      have hst := Run.store (B := B) (a := "rep") (i := .var "rp") (e := .var "z")
        (by rw [evalB_var (by omega), hrp₃]) (by rw [evalB_var (by omega), hz₃]) hlen
      set σ₃' := σ₃.setArr "rep" (σ.vars "rp") (σ.vars "z") with hσ₃'def
      have hrpv : σ₃'.vars "rp" = σ.vars "rp" := by rw [hσ₃'def, vars_setArr, hrp₃]
      have hrpeval : (Expr.add (.var "rp") (.lit 1)).evalB B σ₃' = some (σ.vars "rp" + 1) := by
        have h := evalB_bin (B := B) (op := .add) (σ := σ₃')
          (evalB_var (x := "rp") (by rw [hrpv]; omega)) (evalB_lit (show 1 < B by omega))
          (by simp only [Bop.apply_add, hrpv]; omega)
        simpa [hrpv] using h
      have hincr := Run.assign (B := B) (x := "rp") (σ := σ₃') hrpeval
      refine ⟨σ₃'.setVar "rp" (σ.vars "rp" + 1), (Run.ite_false (by rw [hcond, hseen]; simp)
        (hst.seq hincr)).mono (by simp), ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, R₁, ?_, ?_, ?_, ?_⟩
        · rw [vars_setVar, if_neg (by decide), vars_setVar, if_neg (by decide), hσ₃'def,
            vars_setArr]
          exact hn₃
        · rw [vars_setVar, if_pos rfl]; omega
        · rw [vars_setVar, if_neg (by decide), vars_setVar, if_pos rfl]; omega
        · intro c hc
          rw [arrs_setVar, arrs_setVar, hσ₃'def, arrs_setArr,
            if_neg (by simp [colName, String.ext_iff])]
          exact hcol₃ c hc
        · rw [arrs_setVar, arrs_setVar, hσ₃'def, arrs_setArr, if_pos rfl, hrep₃, set_arrOf]
        · rw [vars_setVar, if_neg (by decide), vars_setVar, if_pos rfl]; exact hR₁lt
        · rw [vars_setVar, if_neg (by decide), vars_setVar, if_pos rfl]; exact hR₁inj
        · have hz' : ((σ₃'.setVar "rp" (σ.vars "rp" + 1)).setVar "z" (σ.vars "z" + 1)).vars "z"
              = σ.vars "z" + 1 := by rw [vars_setVar, if_pos rfl]
          have hrp' : ((σ₃'.setVar "rp" (σ.vars "rp" + 1)).setVar "z" (σ.vars "z" + 1)).vars "rp"
              = σ.vars "rp" + 1 := by
            rw [vars_setVar, if_neg (by decide), vars_setVar, if_pos rfl]
          rw [hz', hrp']
          intro v hv
          rcases Nat.lt_or_ge v (σ.vars "z") with h | h
          · obtain ⟨w, hw, hrow⟩ := hcov v h
            refine ⟨w, by omega, ?_⟩
            have : R₁ w = R w := by rw [hR₁def]; simp [Nat.ne_of_lt hw]
            rw [this]
            exact hrow
          · refine ⟨σ.vars "rp", by omega, ?_⟩
            have : R₁ (σ.vars "rp") = σ.vars "z" := by rw [hR₁def]; simp
            rw [this, show v = σ.vars "z" by omega]
            exact rowEq_refl C L _
      · rw [vars_setVar, if_neg (by decide), hσ₃'def, vars_setArr]; exact hz₃
    · -- the row is already recorded
      refine ⟨σ₃, (Run.ite_true (by rw [hcond]; simp; omega) Run.skip).mono (by simp), ?_, hz₃⟩
      refine ⟨?_, ?_, ?_, ?_, R, ?_, ?_, ?_, ?_⟩
      · rw [vars_setVar, if_neg (by decide)]; exact hn₃
      · rw [vars_setVar, if_pos rfl]; omega
      · rw [vars_setVar, if_neg (by decide), hrp₃]; exact hrple
      · intro c hc; rw [arrs_setVar]; exact hcol₃ c hc
      · rw [arrs_setVar]; exact hrep₃
      · rw [vars_setVar, if_neg (by decide), hrp₃]; exact hRn
      · rw [vars_setVar, if_neg (by decide), hrp₃]; exact hinj
      · have hz' : (σ₃.setVar "z" (σ.vars "z" + 1)).vars "z" = σ.vars "z" + 1 := by
          rw [vars_setVar, if_pos rfl]
        have hrp' : (σ₃.setVar "z" (σ.vars "z" + 1)).vars "rp" = σ.vars "rp" := by
          rw [vars_setVar, if_neg (by decide)]; exact hrp₃
        rw [hz', hrp']
        intro v hv
        rcases Nat.lt_or_ge v (σ.vars "z") with h | h
        · exact hcov v h
        · obtain ⟨w, hw, hrow⟩ := hseeniff₃.mp hseen
          exact ⟨w, hw, by rw [show v = σ.vars "z" by omega]; exact hrow⟩
  -- the counter
  have hzeval : (Expr.add (.var "z") (.lit 1)).evalB B σ₄ = some (σ.vars "z" + 1) := by
    have h := evalB_bin (B := B) (op := .add) (σ := σ₄)
      (evalB_var (x := "z") (by rw [hz₄]; omega)) (evalB_lit (show 1 < B by omega))
      (by simp only [Bop.apply_add, hz₄]; omega)
    simpa [hz₄] using h
  have hzstep := Run.assign (B := B) (x := "z") (σ := σ₄) hzeval
  refine ⟨σ₄.setVar "z" (σ.vars "z" + 1), _,
    hrun1.seq (hrun2.seq (hrun3.seq (hrun4.seq hzstep))), ?_, hI₄, ?_⟩
  · simp only [reprBodyCost, size_lit, size_add, size_var]
    omega
  · rw [vars_setVar, if_pos rfl]

/-- **The representative pass, walked.** What it leaves is a table of
`rp` vertices of pairwise distinct rows — the second half of the
invariant, spent on the table's own length and not exported — such that
every vertex of the carrier has a companion of its own row among them.
That is the constructive content of `BotEval.exists_offRepr`, read off
the program. -/
theorem repr_spec {B n L jd : ℕ} {C : ℕ → ℕ → ℕ}
    (hB : 1 < B) (hn : n < B) (hL : 2 ^ L < B) (hbit : ∀ c < L, ∀ v < n, C c v ≤ 1) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ (∀ c < L, σ.arrs (colName jd c) = arrOf n (C c)) ∧
        ∃ g : ℕ → ℕ, σ.arrs "rep" = arrOf (2 ^ L) g)
      (reprCom jd L)
      (fun _ σ' => σ'.vars "rp" ≤ 2 ^ L ∧
        ∃ R : ℕ → ℕ, σ'.arrs "rep" = arrOf (2 ^ L) R ∧ (∀ w < σ'.vars "rp", R w < n) ∧
          ∀ v < n, ∃ w < σ'.vars "rp", RowEq C L v (R w))
      (reprCost jd L n) := by
  refine (Spec.seq
    (Spec.assign (B := B) (x := "rp") (e := .lit 0) (f := fun _ => 0)
      (fun σ _ => evalB_lit (by omega)))
    (Spec.forRangeZero (B := B) "z" "n" (ReprInv n L jd C) n (reprBodyCost jd L) hn
      (fun τ hτ => hτ.2.1) (fun τ hτ => hτ.1) (repr_turn_spec hB hn hL hbit))
    ?_ ?_).mono ?_
  · rintro σ σ' ⟨hnn, hcol, g, hg⟩ rfl
    have hvn : ((σ.setVar "rp" 0).setVar "z" 0).vars "n" = n := by
      rw [vars_setVar, if_neg (by decide), vars_setVar, if_neg (by decide)]; exact hnn
    have hvz : ((σ.setVar "rp" 0).setVar "z" 0).vars "z" = 0 := by rw [vars_setVar, if_pos rfl]
    have hvrp : ((σ.setVar "rp" 0).setVar "z" 0).vars "rp" = 0 := by
      rw [vars_setVar, if_neg (by decide), vars_setVar, if_pos rfl]
    refine ⟨hvn, by rw [hvz]; exact Nat.zero_le n, by rw [hvrp]; exact Nat.zero_le _, ?_,
      g, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [arrs_setVar, arrs_setVar]
      exact hcol c hc
    · rw [arrs_setVar, arrs_setVar]; exact hg
    · rw [hvrp]; omega
    · rw [hvrp]; omega
    · rw [hvz]; omega
  · rintro σ σ' σ'' - - ⟨⟨-, -, hrp, -, R, hrep, hRn, -, hcov⟩, hz⟩
    exact ⟨hrp, R, hrep, hRn, by rw [← hz]; exact hcov⟩
  · rw [reprCost]
    simp only [size_lit]
    omega

/-! ### The fresh names of the generated evaluator

`RamDriver.botCom` names the scratch of a fragment by extending the
fragment's own output name with one character per level, so the names of
two sibling fragments are incomparable and the name of an enclosing
fragment is not one of its body's. That is the whole of the frame
discipline, and — the extension being by *append* — it is decided by
`List.IsPrefix` and needs none of the digit machinery of
`RamDriverBase`: only the environment slots, whose names carry a
number, are compared through `toString`. -/

/-- `y` is a name the generated code may create below `out`. -/
def Ext (out y : String) : Prop := out.toList <+: y.toList

theorem ext_refl (out : String) : Ext out out := List.prefix_rfl

/-- On two literal names the relation is decided. -/
theorem ext_of_prefix {out y : String} (h : out.toList <+: y.toList) : Ext out y := h

theorem not_ext_of_not_prefix {out y : String} (h : ¬ (out.toList <+: y.toList)) :
    ¬ Ext out y := h

theorem Ext.trans {a b c : String} (h : Ext a b) (h' : Ext b c) : Ext a c :=
  List.IsPrefix.trans h h'

/-- Appending goes below. -/
theorem ext_append (out s : String) : Ext out (out ++ s) := by
  rw [Ext, String.toList_append]
  exact List.prefix_append _ _

/-- Two sibling fragments are incomparable, one character at a time. -/
theorem not_ext_append_of_ne {out s t : String} (h : ¬ (s.toList <+: t.toList)) :
    ¬ Ext (out ++ s) (out ++ t) := by
  rw [Ext, String.toList_append, String.toList_append]
  intro hc
  exact h ((List.prefix_append_right_inj _).mp hc)

/-- A fragment's own name is not below its body's. -/
theorem not_ext_append_left {out s : String} (hs : s.toList ≠ []) : ¬ Ext (out ++ s) out := by
  intro hc
  have h := hc.length_le
  rw [String.toList_append, List.length_append] at h
  have : 0 < s.toList.length := List.length_pos_iff.mpr hs
  omega

/-- Every generated name of the base evaluator begins with the letter
its top-level output name begins with. -/
theorem not_ext_of_fresh {out y : String} (hout : Ext "b" out) (hy : ¬ Ext "b" y) : ¬ Ext out y :=
  fun hc => hy (hout.trans hc)

theorem ext_b_append {out : String} (h : Ext "b" out) (s : String) : Ext "b" (out ++ s) :=
  h.trans (ext_append out s)

/-- A name beginning with another letter is not one of them. -/
theorem not_ext_b_of_cons {y : String} {c : Char} {t : List Char} (h : y.toList = c :: t)
    (hc : c ≠ 'b') : ¬ Ext "b" y := by
  rintro ⟨s, hs⟩
  rw [h, show "b".toList = ['b'] from rfl, List.cons_append, List.nil_append] at hs
  exact hc (List.cons.inj hs).1.symm

theorem not_ext_b_envName (i : ℕ) : ¬ Ext "b" (envName i) :=
  not_ext_b_of_cons (y := envName i) (by rw [envName, String.toList_append]; rfl) (by decide)

theorem not_ext_b_colName (j c : ℕ) : ¬ Ext "b" (colName j c) :=
  not_ext_b_of_cons (y := colName j c)
    (by rw [colName, String.toList_append, String.toList_append, String.toList_append]; rfl)
    (by decide)

theorem not_ext_b_tabName (j i : ℕ) : ¬ Ext "b" (tabName j i) :=
  not_ext_b_of_cons (y := tabName j i)
    (by rw [tabName, String.toList_append, String.toList_append, String.toList_append]; rfl)
    (by decide)

theorem not_ext_b_alvName (j : ℕ) : ¬ Ext "b" (alvName j) :=
  not_ext_b_of_cons (y := alvName j) (by rw [alvName, String.toList_append]; rfl) (by decide)

theorem not_ext_b_gamName (j : ℕ) : ¬ Ext "b" (gamName j) :=
  not_ext_b_of_cons (y := gamName j) (by rw [gamName, String.toList_append]; rfl) (by decide)

/-- A name below another is not that other. -/
theorem append_ne_self {out s : String} (hs : s.toList ≠ []) : out ++ s ≠ out := by
  intro h
  have hlen : (out ++ s).toList.length = out.toList.length := by rw [h]
  rw [String.toList_append, List.length_append] at hlen
  have : 0 < s.toList.length := List.length_pos_iff.mpr hs
  omega

/-- Two sibling names differ. -/
theorem append_ne_append {out s t : String} (h : ¬ (s.toList <+: t.toList)) :
    out ++ s ≠ out ++ t := by
  intro he
  refine h ?_
  have h2 : (out ++ s).toList <+: (out ++ t).toList := by rw [he]
  rw [String.toList_append, String.toList_append] at h2
  exact (List.prefix_append_right_inj _).mp h2

/-- A generated name is not an environment slot. -/
theorem ne_envName_of_ext {out y : String} (hout : Ext "b" out) (hy : Ext out y) (i : ℕ) :
    y ≠ envName i := by
  intro he
  refine not_ext_b_envName i ?_
  rw [← he]
  exact hout.trans hy

/-- A generated name is not a colour array. -/
theorem ne_colName_of_ext {out y : String} (hout : Ext "b" out) (hy : Ext out y) (jd c : ℕ) :
    y ≠ colName jd c := by
  intro he
  refine not_ext_b_colName jd c ?_
  rw [← he]
  exact hout.trans hy

/-- The environment slots are addressed injectively. -/
theorem envName_inj {i i' : ℕ} (h : envName i = envName i') : i = i' := by
  refine toString_inj (String.ext ?_)
  have h' := congrArg String.toList h
  rw [envName, envName, String.toList_append, String.toList_append] at h'
  exact List.append_cancel_left h'

/-! ### What a fragment writes

Read off the syntax: a fragment assigns to names below its own output
name and to the environment slots at or above its arity, and it stores
only into arrays below its output name. The unrestricted quantifier is
the one case that leaves the discipline — it assigns the scan variable
of the representative table — and it is also the one case a *local*
formula never reaches. -/

/-- The stores of a guard load address one array. -/
theorem warrs_guardFold (arr : String) :
    ∀ (l : List ℕ) (p : ℕ),
      (foldIdx (fun q (i : ℕ) => Com.store arr (.lit q) (.var (envName i))) p l).warrs ⊆ [arr] := by
  intro l
  induction l with
  | nil => intro p b hb; exact absurd hb List.not_mem_nil
  | cons x xs ih =>
    intro p b hb
    have he : (foldIdx (fun q (i : ℕ) => Com.store arr (.lit q) (.var (envName i))) p (x :: xs))
        = .seq (Com.store arr (.lit p) (.var (envName x)))
            (foldIdx (fun q (i : ℕ) => Com.store arr (.lit q) (.var (envName i))) (p + 1) xs) :=
      rfl
    rw [he, Com.warrs] at hb
    rcases List.mem_append.mp hb with h | h
    · rw [Com.warrs] at h; exact h
    · exact ih (p + 1) h

/-- A guard load assigns only its counter. -/
theorem wvars_guardFold (arr : String) :
    ∀ (l : List ℕ) (p : ℕ),
      (foldIdx (fun q (i : ℕ) => Com.store arr (.lit q) (.var (envName i))) p l).wvars = [] := by
  intro l
  induction l with
  | nil => intro p; rfl
  | cons x xs ih =>
    intro p
    have he : (foldIdx (fun q (i : ℕ) => Com.store arr (.lit q) (.var (envName i))) p (x :: xs))
        = .seq (Com.store arr (.lit p) (.var (envName x)))
            (foldIdx (fun q (i : ℕ) => Com.store arr (.lit q) (.var (envName i))) (p + 1) xs) :=
      rfl
    rw [he, Com.wvars, ih (p + 1), Com.wvars]
    rfl

/-- **What a fragment of the generated evaluator assigns to.** -/
theorem wvars_botCom {L jd : ℕ} : ∀ {k : ℕ} (ψ : DistFO L k), IsLocal ψ → ∀ out y : String,
    y ∈ (botCom jd ψ out).wvars → Ext out y ∨ ∃ i, k ≤ i ∧ y = envName i := by
  intro k ψ
  induction ψ with
  | adj i j =>
    intro _ out y hy
    have he : (botCom jd (DistFO.adj (L := L) i j) out).wvars = [out] := rfl
    rw [he, List.mem_singleton] at hy
    exact Or.inl (by rw [hy]; exact ext_refl out)
  | eq i j =>
    intro _ out y hy
    have he : (botCom jd (DistFO.eq (L := L) i j) out).wvars = [out] ++ [out] := rfl
    rw [he] at hy
    simp only [List.mem_append, List.mem_singleton, or_self] at hy
    exact Or.inl (by rw [hy]; exact ext_refl out)
  | color c i =>
    intro _ out y hy
    have he : (botCom jd (DistFO.color c i) out).wvars = [out] ++ [out] := rfl
    rw [he] at hy
    simp only [List.mem_append, List.mem_singleton, or_self] at hy
    exact Or.inl (by rw [hy]; exact ext_refl out)
  | distLe r i j =>
    intro _ out y hy
    have he : (botCom jd (DistFO.distLe (L := L) r i j) out).wvars = [out] ++ [out] := rfl
    rw [he] at hy
    simp only [List.mem_append, List.mem_singleton, or_self] at hy
    exact Or.inl (by rw [hy]; exact ext_refl out)
  | distColorLt r c i =>
    intro _ out y hy
    refine Or.inl ?_
    by_cases hr : r = 0
    · have he : botCom jd (DistFO.distColorLt r c i) out = .assign out (.lit 0) := by
        rw [botCom, if_pos hr]
      rw [he, Com.wvars, List.mem_singleton] at hy
      rw [hy]; exact ext_refl out
    · have he : botCom jd (DistFO.distColorLt r c i) out =
          .ite (.lt (.lit 0) (.get (colName jd (c : ℕ)) (.var (envName (i : ℕ)))))
            (.assign out (.lit 1)) (.assign out (.lit 0)) := by
        rw [botCom, if_neg hr]
      rw [he, Com.wvars, Com.wvars, Com.wvars] at hy
      simp only [List.mem_append, List.mem_singleton, or_self] at hy
      rw [hy]; exact ext_refl out
  | not ψ ih =>
    intro hloc out y hy
    have he : (botCom jd (DistFO.not ψ) out).wvars =
        (botCom jd ψ (out ++ "a")).wvars ++ [out] := rfl
    rw [he] at hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | hy
    · rcases ih ((isLocal_not ψ).mp hloc) (out ++ "a") y hy with h | h
      · exact Or.inl ((ext_append out "a").trans h)
      · exact Or.inr h
    · exact Or.inl (by rw [hy]; exact ext_refl out)
  | and ψ χ ihψ ihχ =>
    intro hloc out y hy
    have he : (botCom jd (DistFO.and ψ χ) out).wvars =
        (botCom jd ψ (out ++ "a")).wvars ++ ((botCom jd χ (out ++ "b")).wvars ++ [out]) := rfl
    obtain ⟨hlψ, hlχ⟩ := (isLocal_and ψ χ).mp hloc
    rw [he] at hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | hy | hy
    · rcases ihψ hlψ (out ++ "a") y hy with h | h
      · exact Or.inl ((ext_append out "a").trans h)
      · exact Or.inr h
    · rcases ihχ hlχ (out ++ "b") y hy with h | h
      · exact Or.inl ((ext_append out "b").trans h)
      · exact Or.inr h
    · exact Or.inl (by rw [hy]; exact ext_refl out)
  | exU ψ ih => intro hloc; exact absurd hloc ((isLocal_exU ψ).mp)
  | exL r g ψ ih =>
    intro hloc out y hy
    have he : (botCom jd (DistFO.exL r g ψ) out).wvars =
        (guardLoad g.toList (out ++ "g") (out ++ "m")).wvars ++
          ([out] ++ ([out ++ "w"] ++
            ([envName _] ++ ((botCom jd ψ (out ++ "a")).wvars ++
              ([out] ++ [out ++ "w"]))))) := rfl
    have hg : (guardLoad g.toList (out ++ "g") (out ++ "m")).wvars = [out ++ "m"] := by
      rw [guardLoad, Com.wvars, wvars_guardFold, Com.wvars, List.nil_append]
    rw [he, hg] at hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy | hy | hy | hy
    · exact Or.inl (by rw [hy]; exact ext_append out "m")
    · exact Or.inl (by rw [hy]; exact ext_refl out)
    · exact Or.inl (by rw [hy]; exact ext_append out "w")
    · exact Or.inr ⟨_, le_rfl, hy⟩
    · rcases ih ((isLocal_exL r g ψ).mp hloc) (out ++ "a") y hy with h | ⟨i, hik, hyi⟩
      · exact Or.inl ((ext_append out "a").trans h)
      · exact Or.inr ⟨i, by omega, hyi⟩
    · exact Or.inl (by rw [hy]; exact ext_refl out)
    · exact Or.inl (by rw [hy]; exact ext_append out "w")

/-- **What a fragment of the generated evaluator stores into**: its own
candidate array, and those of the fragments below it. -/
theorem warrs_botCom {L jd : ℕ} : ∀ {k : ℕ} (ψ : DistFO L k), IsLocal ψ → ∀ out a : String,
    a ∈ (botCom jd ψ out).warrs → Ext out a := by
  intro k ψ
  induction ψ with
  | adj i j =>
    intro _ out a ha
    have he : (botCom jd (DistFO.adj (L := L) i j) out).warrs = [] := rfl
    rw [he] at ha
    exact absurd ha List.not_mem_nil
  | eq i j =>
    intro _ out a ha
    have he : (botCom jd (DistFO.eq (L := L) i j) out).warrs = [] ++ [] := rfl
    rw [he, List.append_nil] at ha
    exact absurd ha List.not_mem_nil
  | color c i =>
    intro _ out a ha
    have he : (botCom jd (DistFO.color c i) out).warrs = [] ++ [] := rfl
    rw [he, List.append_nil] at ha
    exact absurd ha List.not_mem_nil
  | distLe r i j =>
    intro _ out a ha
    have he : (botCom jd (DistFO.distLe (L := L) r i j) out).warrs = [] ++ [] := rfl
    rw [he, List.append_nil] at ha
    exact absurd ha List.not_mem_nil
  | distColorLt r c i =>
    intro _ out a ha
    by_cases hr : r = 0
    · have he : botCom jd (DistFO.distColorLt r c i) out = .assign out (.lit 0) := by
        rw [botCom, if_pos hr]
      rw [he, Com.warrs] at ha
      exact absurd ha List.not_mem_nil
    · have he : botCom jd (DistFO.distColorLt r c i) out =
          .ite (.lt (.lit 0) (.get (colName jd (c : ℕ)) (.var (envName (i : ℕ)))))
            (.assign out (.lit 1)) (.assign out (.lit 0)) := by
        rw [botCom, if_neg hr]
      rw [he, Com.warrs, Com.warrs, Com.warrs, List.append_nil] at ha
      exact absurd ha List.not_mem_nil
  | not ψ ih =>
    intro hloc out a ha
    have he : (botCom jd (DistFO.not ψ) out).warrs =
        (botCom jd ψ (out ++ "a")).warrs ++ [] := rfl
    rw [he, List.append_nil] at ha
    exact (ext_append out "a").trans (ih ((isLocal_not ψ).mp hloc) (out ++ "a") a ha)
  | and ψ χ ihψ ihχ =>
    intro hloc out a ha
    have he : (botCom jd (DistFO.and ψ χ) out).warrs =
        (botCom jd ψ (out ++ "a")).warrs ++ ((botCom jd χ (out ++ "b")).warrs ++ []) := rfl
    obtain ⟨hlψ, hlχ⟩ := (isLocal_and ψ χ).mp hloc
    rw [he, List.append_nil] at ha
    rcases List.mem_append.mp ha with h | h
    · exact (ext_append out "a").trans (ihψ hlψ (out ++ "a") a h)
    · exact (ext_append out "b").trans (ihχ hlχ (out ++ "b") a h)
  | exU ψ ih => intro hloc; exact absurd hloc ((isLocal_exU ψ).mp)
  | exL r g ψ ih =>
    intro hloc out a ha
    have he : (botCom jd (DistFO.exL r g ψ) out).warrs =
        (guardLoad g.toList (out ++ "g") (out ++ "m")).warrs ++
          ([] ++ ([] ++ ((botCom jd ψ (out ++ "a")).warrs ++ ([] ++ [])))) := rfl
    have hg : (guardLoad g.toList (out ++ "g") (out ++ "m")).warrs ⊆ [out ++ "g"] := by
      rw [guardLoad, Com.warrs, Com.warrs, List.append_nil]
      exact warrs_guardFold _ _ 0
    rw [he] at ha
    simp only [List.append_nil, List.nil_append, List.mem_append] at ha
    rcases ha with h | h
    · have hmem := hg h
      rw [List.mem_singleton] at hmem
      rw [hmem]
      exact ext_append out "g"
    · exact (ext_append out "a").trans (ih ((isLocal_exL r g ψ).mp hloc) (out ++ "a") a h)

/-! ### The generated evaluator

`RamDriver.botCom ℓ ψ out` is `Lax3Proofs.BotEval` read as code, and its
walk is the induction that generated it. Three things travel with it:
the depth's colour arrays, which it only reads; the environment slots
below its arity, which it only reads; and the candidate array of every
local quantifier inside it, which it writes. The first two are framed by
the name discipline above, and the third is the one clause the walk asks
of its caller.

The unrestricted quantifier is not walked, and cannot be: its
representative table is one vertex per row of the *whole* arena, while
`BotEval.sat_exU_bot_of_repr` asks for one per row realized *off the
environment*, and a row realized only by an entry of the environment and
by one vertex outside it is a counterexample to the program as written.
It is also never reached — every tabled formula is local, by
`FormulaTables.tableRank_of_mem_tablesAt` — so the walk carries
`IsLocal` and discharges that case by `SyntaxLemmas.isLocal_exU`. -/

/-- What a fragment reads and never writes: the depth's colour arrays. -/
def BotEnv (n L jd : ℕ) (C : ℕ → ℕ → ℕ) (σ : Env) : Prop :=
  ∀ c < L, σ.arrs (colName jd c) = arrOf n (C c)

/-! `RamDriver.BotMem` is the memory clause of the generated evaluator —
the candidate array of every local quantifier, at the width its guard
set is loaded at. It lives at the surface rather than here because it is
a *precondition* of `RamDriver.BaseImplements`, and `RamDriver.BaseArrs`
packages it with the representative table. `RamDriver.botMem_of_length`
is that it survives any run. -/

/-- The cost of a fragment: a constant per connective, and one turn of a
guard scan per guard entry. -/
def botCost {L : ℕ} : {k : ℕ} → DistFO L k → ℕ
  | _, .adj _ _ => 10
  | _, .eq _ _ => 10
  | _, .color _ _ => 10
  | _, .distLe _ _ _ => 10
  | _, .distColorLt _ _ _ => 10
  | _, .not ψ => botCost ψ + 10
  | _, .and ψ χ => botCost ψ + botCost χ + 10
  | _, .exU ψ => botCost ψ + 10
  | _, .exL _ g ψ => (botCost ψ + 30) * (g.card + 1) + 30

/-- A fragment always costs something. -/
theorem one_le_botCost {L k : ℕ} (ψ : DistFO L k) : 1 ≤ botCost ψ := by
  induction ψ with
  | adj i j => rw [botCost]; omega
  | eq i j => rw [botCost]; omega
  | color c i => rw [botCost]; omega
  | distLe r i j => rw [botCost]; omega
  | distColorLt r c i => rw [botCost]; omega
  | not ψ ih => rw [botCost]; omega
  | and ψ χ ihψ ihχ => rw [botCost]; omega
  | exU ψ ih => rw [botCost]; omega
  | exL r g ψ ih => rw [botCost]; omega

/-- An environment slot is not a name below a fragment's output. -/
theorem not_ext_envName {out : String} (hout : Ext "b" out) (i : ℕ) : ¬ Ext out (envName i) :=
  not_ext_of_fresh hout (not_ext_b_envName i)

/-- The environment slots below a fragment's arity are not the ones it
assigns. -/
theorem envName_ne_of_lt {i i' : ℕ} (h : i < i') : envName i ≠ envName i' :=
  fun hc => absurd (envName_inj hc) (by omega)

/-- **The frame of one fragment**, as its caller consumes it: names not
below its output name and not its own environment slots are where they
were, and no array changed length. -/
theorem bot_framed {B K L jd k : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {ψ : DistFO L k}
    {out : String} (hloc : IsLocal ψ) (h : Spec B P (botCom jd ψ out) Q K) :
    Spec B P (botCom jd ψ out)
      (fun σ σ' => Q σ σ' ∧
        (∀ y, ¬ Ext out y → (∀ i, k ≤ i → y ≠ envName i) → σ'.vars y = σ.vars y) ∧
        (∀ a, ¬ Ext out a → σ'.arrs a = σ.arrs a) ∧
        (∀ a, (σ'.arrs a).length = (σ.arrs a).length)) K := by
  intro σ hσ
  obtain ⟨σ', hrun, hq⟩ := h σ hσ
  refine ⟨σ', hrun, hq, ?_, ?_, fun a => run_length_arrs hrun a⟩
  · intro y hy hy'
    refine hrun.frame_var y fun hm => ?_
    rcases wvars_botCom ψ hloc out y hm with h1 | ⟨i, hik, hyi⟩
    · exact hy h1
    · exact hy' i hik hyi
  · intro a ha
    exact hrun.frame_arr a fun hm => ha (warrs_botCom ψ hloc out a hm)

/-! The guard set arrives as a list of variables and is addressed as a
list of slot numbers; these three are that coercion, read off its own
recursion. -/

theorem length_coe_list {k : ℕ} (gs : List (Fin k)) : (↑gs : List ℕ).length = gs.length := by
  induction gs with
  | nil => rfl
  | cons x xs ih => exact congrArg (· + 1) ih

theorem getElem_coe_list {k : ℕ} : ∀ (gs : List (Fin k)) (q : ℕ)
    (hq : q < (↑gs : List ℕ).length) (hq' : q < gs.length),
    (↑gs : List ℕ)[q] = ((gs[q] : Fin k) : ℕ) := by
  intro gs
  induction gs with
  | nil => intro q _ hq'; exact absurd hq' (by simp)
  | cons x xs ih =>
    intro q hq hq'
    cases q with
    | zero => rfl
    | succ q => exact ih q (by simpa using hq) (by simpa using hq')

theorem mem_coe_list {k : ℕ} : ∀ (gs : List (Fin k)) (a : ℕ),
    a ∈ (↑gs : List ℕ) → ∃ i ∈ gs, (i : ℕ) = a := by
  intro gs
  induction gs with
  | nil => intro a ha; exact absurd ha List.not_mem_nil
  | cons x xs ih =>
    intro a ha
    have ha' : a ∈ ((x : ℕ) :: (↑xs : List ℕ)) := ha
    rcases List.mem_cons.mp ha' with rfl | h
    · exact ⟨x, List.mem_cons_self, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := ih a h
      exact ⟨i, List.mem_cons_of_mem _ hi, rfl⟩

/-- **The guard load.** A straight line of stores puts the entries the
guard set names into the fragment's candidate array. -/
theorem guardFold_spec {B : ℕ} (arr : String) (len : ℕ) :
    ∀ (l : List ℕ) (p : ℕ) (Gv : ℕ → ℕ),
      Spec B (fun σ => σ.arrs arr = arrOf len Gv ∧ p + l.length ≤ len ∧ p + l.length < B ∧
          ∀ i ∈ l, σ.vars (envName i) < B)
        (foldIdx (fun q (i : ℕ) => Com.store arr (.lit q) (.var (envName i))) p l)
        (fun σ σ' => σ'.vars = σ.vars ∧ (∀ b, b ≠ arr → σ'.arrs b = σ.arrs b) ∧
          ∃ Gv' : ℕ → ℕ, σ'.arrs arr = arrOf len Gv' ∧ (∀ j < p, Gv' j = Gv j) ∧
            ∀ (q : ℕ) (hq : q < l.length), Gv' (p + q) = σ.vars (envName l[q]))
        (3 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro p Gv
    refine Spec.of_exists fun σ hσ => ?_
    exact ⟨σ, 1, Run.skip, by simp, rfl, fun b _ => rfl, Gv, hσ.1, fun j _ => rfl,
      fun q hq => absurd hq (by simp)⟩
  | cons x xs ih =>
    intro p Gv
    refine Spec.of_exists fun σ hσ => ?_
    obtain ⟨harr, hlen, hlenB, hval⟩ := hσ
    have hxB : σ.vars (envName x) < B := hval x List.mem_cons_self
    have hplen : p < len := by rw [List.length_cons] at hlen; omega
    have hpB : p < B := by rw [List.length_cons] at hlenB; omega
    have hst := Run.store (B := B) (a := arr) (i := .lit p) (e := .var (envName x)) (σ := σ)
      (evalB_lit hpB) (evalB_var hxB) (by rw [harr, length_arrOf]; exact hplen)
    have hGv₁ : (σ.setArr arr p (σ.vars (envName x))).arrs arr =
        arrOf len (fun j => if j = p then σ.vars (envName x) else Gv j) := by
      rw [arrs_setArr, if_pos rfl, harr, set_arrOf]
    obtain ⟨σ₂, hrun₂, hvars₂, harrs₂, Gv₂, hGv₂, hlow₂, hval₂⟩ :=
      (ih (p + 1) (fun j => if j = p then σ.vars (envName x) else Gv j)).run
        (σ := σ.setArr arr p (σ.vars (envName x)))
        ⟨hGv₁, by rw [List.length_cons] at hlen; omega,
          by rw [List.length_cons] at hlenB; omega,
          fun i hi => by rw [vars_setArr]; exact hval i (List.mem_cons_of_mem _ hi)⟩
    refine ⟨σ₂, _, hst.seq hrun₂, by simp only [List.length_cons, size_lit, size_var]; omega,
      ?_, ?_, Gv₂, hGv₂, ?_, ?_⟩
    · rw [hvars₂, vars_setArr]
    · intro b hb
      rw [harrs₂ b hb, arrs_setArr, if_neg hb]
    · intro j hj
      rw [hlow₂ j (by omega)]
      simp only [if_neg (by omega : j ≠ p)]
    · intro q hq
      rcases Nat.eq_zero_or_pos q with rfl | hq0
      · have h := hlow₂ p (by omega)
        rw [Nat.add_zero, h, if_pos rfl]
        rfl
      · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        have hq' : q' < xs.length := by simp only [List.length_cons] at hq; omega
        have hidx : p + (q' + 1) = p + 1 + q' := by omega
        rw [hidx, hval₂ q' hq', vars_setArr]
        rfl

/-- **The shape of every atom of the generated evaluator**: a test, and
the bit it leaves. -/
theorem test_spec {B : ℕ} {b : Cond} {out : String} {P : Env → Prop} {p : Prop}
    (hB : 1 < B) (hdef : ∀ σ, P σ → ∃ v, b.evalB B σ = some v ∧ (v = true ↔ p)) :
    Spec B P (.ite b (.assign out (.lit 1)) (.assign out (.lit 0)))
      (fun _ σ' => σ'.vars out ≤ 1 ∧ (σ'.vars out ≠ 0 ↔ p)) (1 + b.size + 2) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨v, hv, hviff⟩ := hdef σ hσ
  cases v with
  | true =>
    refine ⟨σ.setVar out 1, _, Run.ite_true hv (Run.assign (evalB_lit hB)), by simp, ?_, ?_⟩
    · rw [vars_setVar, if_pos rfl]
    · rw [vars_setVar, if_pos rfl]
      simp only [ne_eq, one_ne_zero, not_false_eq_true, true_iff]
      exact hviff.mp rfl
  | false =>
    refine ⟨σ.setVar out 0, _, Run.ite_false hv (Run.assign (evalB_lit (show 0 < B by omega))),
      by simp, ?_, ?_⟩
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [vars_setVar, if_pos rfl]
      simp only [ne_eq, not_true_eq_false, false_iff]
      intro hp
      exact absurd (hviff.mpr hp) (by simp)

/-- **The generated evaluator, walked.** At the end of a fragment its
output scalar holds the truth value of the fragment's formula on the
edgeless arena, at the environment the slots hold and the colouring the
depth's arrays hold. -/
theorem bot_spec {B n L jd : ℕ} {C : ℕ → ℕ → ℕ} (hB : 1 < B) (hn : n < B)
    (hbit : ∀ c < L, ∀ v < n, C c v ≤ 1) :
    ∀ {k : ℕ} (ψ : DistFO L k), IsLocal ψ → ∀ out : String, Ext "b" out →
      ∀ m : Fin k → Fin n,
        Spec B
          (fun σ => BotEnv n L jd C σ ∧
            (∀ i : Fin k, σ.vars (envName (i : ℕ)) = ((m i : Fin n) : ℕ)) ∧ BotMem B ψ out σ)
          (botCom jd ψ out)
          (fun _ σ' => σ'.vars out ≤ 1 ∧
            (σ'.vars out ≠ 0 ↔ Sat (⊥ : SimpleGraph (Fin n)) (colRead n C L) m ψ))
          (botCost ψ) := by
  have hbnd : ∀ c < L, ∀ v < n, C c v < B := fun c hc v hv => lt_of_le_of_lt (hbit c hc v hv) hB
  intro k ψ
  induction ψ with
  | adj i j =>
    intro _ out _ m
    have he : botCom jd (DistFO.adj (L := L) i j) out = .assign out (.lit 0) := rfl
    rw [he]
    refine Spec.of_exists fun σ hσ => ?_
    refine ⟨σ.setVar out 0, _, Run.assign (evalB_lit (show 0 < B by omega)), ?_, ?_, ?_⟩
    · rw [botCost]; simp
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [vars_setVar, if_pos rfl, BotEval.sat_adj_bot i j]
      simp
  | eq i j =>
    intro _ out _ m
    have he : botCom jd (DistFO.eq (L := L) i j) out =
        .ite (.eq (.var (envName (i : ℕ))) (.var (envName (j : ℕ))))
          (.assign out (.lit 1)) (.assign out (.lit 0)) := rfl
    rw [he]
    refine (test_spec (p := Sat (⊥ : SimpleGraph (Fin n)) (colRead n C L) m (.eq i j))
      hB ?_).mono ?_
    · rintro σ ⟨-, henv, -⟩
      have hiB : σ.vars (envName (i : ℕ)) < B := by rw [henv i]; exact lt_trans (m i).isLt hn
      have hjB : σ.vars (envName (j : ℕ)) < B := by rw [henv j]; exact lt_trans (m j).isLt hn
      refine ⟨_, evalB_condEq (evalB_var hiB) (evalB_var hjB), ?_⟩
      rw [BotEval.sat_eq_bot i j, beq_iff_eq, henv i, henv j]
      exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
    · rw [botCost]; simp
  | color c i =>
    intro _ out _ m
    have he : botCom jd (DistFO.color c i) out =
        .ite (.lt (.lit 0) (.get (colName jd (c : ℕ)) (.var (envName (i : ℕ)))))
          (.assign out (.lit 1)) (.assign out (.lit 0)) := rfl
    rw [he]
    refine (test_spec (p := Sat (⊥ : SimpleGraph (Fin n)) (colRead n C L) m (.color c i))
      hB ?_).mono ?_
    · rintro σ ⟨hcol, henv, -⟩
      have hiB : σ.vars (envName (i : ℕ)) < B := by rw [henv i]; exact lt_trans (m i).isLt hn
      have hcell : (σ.arrs (colName jd (c : ℕ)))[σ.vars (envName (i : ℕ))]? =
          some (C (c : ℕ) ((m i : Fin n) : ℕ)) := by
        rw [hcol (c : ℕ) c.isLt, henv i]
        exact getElem?_arrOf _ (m i).isLt
      refine ⟨_, evalB_condLt (evalB_lit (show 0 < B by omega))
        (evalB_get (evalB_var hiB) hcell (hbnd _ c.isLt _ (m i).isLt)), ?_⟩
      rw [BotEval.sat_color_bot c i, mem_colRead]
      simp only [decide_eq_true_eq]
      omega
    · rw [botCost]; simp
  | distLe r i j =>
    intro _ out _ m
    have he : botCom jd (DistFO.distLe (L := L) r i j) out =
        .ite (.eq (.var (envName (i : ℕ))) (.var (envName (j : ℕ))))
          (.assign out (.lit 1)) (.assign out (.lit 0)) := rfl
    rw [he]
    refine (test_spec (p := Sat (⊥ : SimpleGraph (Fin n)) (colRead n C L) m (.distLe r i j))
      hB ?_).mono ?_
    · rintro σ ⟨-, henv, -⟩
      have hiB : σ.vars (envName (i : ℕ)) < B := by rw [henv i]; exact lt_trans (m i).isLt hn
      have hjB : σ.vars (envName (j : ℕ)) < B := by rw [henv j]; exact lt_trans (m j).isLt hn
      refine ⟨_, evalB_condEq (evalB_var hiB) (evalB_var hjB), ?_⟩
      rw [BotEval.sat_distLe_bot r i j, beq_iff_eq, henv i, henv j]
      exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
    · rw [botCost]; simp
  | distColorLt r c i =>
    intro _ out _ m
    by_cases hr : r = 0
    · have he : botCom jd (DistFO.distColorLt r c i) out = .assign out (.lit 0) := by
        rw [botCom, if_pos hr]
      rw [he]
      refine Spec.of_exists fun σ hσ => ?_
      refine ⟨σ.setVar out 0, _, Run.assign (evalB_lit (show 0 < B by omega)), ?_, ?_, ?_⟩
      · rw [botCost]; simp
      · rw [vars_setVar, if_pos rfl]; omega
      · rw [vars_setVar, if_pos rfl, BotEval.sat_distColorLt_bot r c i, hr]
        simp
    · have he : botCom jd (DistFO.distColorLt r c i) out =
          .ite (.lt (.lit 0) (.get (colName jd (c : ℕ)) (.var (envName (i : ℕ)))))
            (.assign out (.lit 1)) (.assign out (.lit 0)) := by
        rw [botCom, if_neg hr]
      rw [he]
      refine (test_spec (p := Sat (⊥ : SimpleGraph (Fin n)) (colRead n C L) m
        (.distColorLt r c i)) hB ?_).mono ?_
      · rintro σ ⟨hcol, henv, -⟩
        have hiB : σ.vars (envName (i : ℕ)) < B := by rw [henv i]; exact lt_trans (m i).isLt hn
        have hcell : (σ.arrs (colName jd (c : ℕ)))[σ.vars (envName (i : ℕ))]? =
            some (C (c : ℕ) ((m i : Fin n) : ℕ)) := by
          rw [hcol (c : ℕ) c.isLt, henv i]
          exact getElem?_arrOf _ (m i).isLt
        refine ⟨_, evalB_condLt (evalB_lit (show 0 < B by omega))
          (evalB_get (evalB_var hiB) hcell (hbnd _ c.isLt _ (m i).isLt)), ?_⟩
        rw [BotEval.sat_distColorLt_bot r c i, mem_colRead]
        simp only [decide_eq_true_eq]
        constructor
        · intro h
          exact ⟨by omega, by omega⟩
        · rintro ⟨-, h⟩
          omega
      · rw [botCost]; simp
  | not ψ ih =>
    intro hloc out hout m
    have hlψ := (isLocal_not ψ).mp hloc
    have he : botCom jd (DistFO.not ψ) out =
        .seq (botCom jd ψ (out ++ "a")) (.assign out (.sub (.lit 1) (.var (out ++ "a")))) := rfl
    rw [he]
    refine Spec.of_exists fun σ hσ => ?_
    obtain ⟨σ₁, hrun₁, ⟨hb1, hbiff⟩, -, -, -⟩ :=
      (bot_framed hlψ (ih hlψ (out ++ "a") (ext_b_append hout "a") m)).run
        (σ := σ) ⟨hσ.1, hσ.2.1, hσ.2.2⟩
    have hval : (Expr.sub (.lit 1) (.var (out ++ "a"))).evalB B σ₁ =
        some (1 - σ₁.vars (out ++ "a")) := by
      have h := evalB_bin (B := B) (op := .sub) (σ := σ₁) (evalB_lit hB)
        (evalB_var (x := out ++ "a") (by omega)) (by simp only [Bop.apply_sub]; omega)
      simpa using h
    refine ⟨σ₁.setVar out (1 - σ₁.vars (out ++ "a")), _, hrun₁.seq (Run.assign hval), ?_, ?_, ?_⟩
    · rw [botCost]; simp
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [vars_setVar, if_pos rfl, sat_not ψ, ← hbiff]
      omega
  | and ψ χ ihψ ihχ =>
    intro hloc out hout m
    obtain ⟨hlψ, hlχ⟩ := (isLocal_and ψ χ).mp hloc
    have he : botCom jd (DistFO.and ψ χ) out =
        .seq (botCom jd ψ (out ++ "a"))
          (.seq (botCom jd χ (out ++ "b"))
            (.assign out (.mul (.var (out ++ "a")) (.var (out ++ "b"))))) := rfl
    rw [he]
    refine Spec.of_exists fun σ hσ => ?_
    obtain ⟨hcol, henv, hmemψ, hmemχ⟩ : BotEnv n L jd C σ ∧
        (∀ i : Fin _, σ.vars (envName (i : ℕ)) = ((m i : Fin n) : ℕ)) ∧
        BotMem B ψ (out ++ "a") σ ∧ BotMem B χ (out ++ "b") σ :=
      ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2⟩
    obtain ⟨σ₁, hrun₁, ⟨hb1, hbiff1⟩, hfv₁, hfa₁, hlen₁⟩ :=
      (bot_framed hlψ (ihψ hlψ (out ++ "a") (ext_b_append hout "a") m)).run
        (σ := σ) ⟨hcol, henv, hmemψ⟩
    have hcol₁ : BotEnv n L jd C σ₁ := fun c hc => by
      rw [hfa₁ (colName jd c) (not_ext_of_fresh (ext_b_append hout "a") (not_ext_b_colName jd c))]
      exact hcol c hc
    have henv₁ : ∀ i : Fin _, σ₁.vars (envName (i : ℕ)) = ((m i : Fin n) : ℕ) := fun i => by
      rw [hfv₁ (envName (i : ℕ)) (not_ext_envName (ext_b_append hout "a") _)
        (fun i' hi' => envName_ne_of_lt (by omega))]
      exact henv i
    obtain ⟨σ₂, hrun₂, ⟨hb2, hbiff2⟩, hfv₂, hfa₂, hlen₂⟩ :=
      (bot_framed hlχ (ihχ hlχ (out ++ "b") (ext_b_append hout "b") m)).run
        (σ := σ₁) ⟨hcol₁, henv₁, botMem_of_length hlen₁ χ (out ++ "b") hmemχ⟩
    have hkeep : σ₂.vars (out ++ "a") = σ₁.vars (out ++ "a") :=
      hfv₂ (out ++ "a") (not_ext_append_of_ne (by decide))
        (fun i' _ => not_ext_b_envName i' ∘ (fun h => h ▸ ext_b_append hout "a"))
    have hval : (Expr.mul (.var (out ++ "a")) (.var (out ++ "b"))).evalB B σ₂ =
        some (σ₂.vars (out ++ "a") * σ₂.vars (out ++ "b")) := by
      have h := evalB_bin (B := B) (op := .mul) (σ := σ₂)
        (evalB_var (x := out ++ "a") (by omega)) (evalB_var (x := out ++ "b") (by omega))
        (by simp only [Bop.apply_mul]; have : σ₂.vars (out ++ "a") ≤ 1 := by omega
            nlinarith)
      simpa using h
    refine ⟨σ₂.setVar out (σ₂.vars (out ++ "a") * σ₂.vars (out ++ "b")), _,
      hrun₁.seq (hrun₂.seq (Run.assign hval)), ?_, ?_, ?_⟩
    · rw [botCost]; simp only [size_var, size_bin]; omega
    · rw [vars_setVar, if_pos rfl]
      have : σ₂.vars (out ++ "a") ≤ 1 := by omega
      nlinarith
    · rw [vars_setVar, if_pos rfl, sat_and ψ χ, ← hbiff2, ← hbiff1, ← hkeep]
      constructor
      · intro h
        exact ⟨fun hc => h (by rw [hc, Nat.zero_mul]), fun hc => h (by rw [hc, Nat.mul_zero])⟩
      · rintro ⟨h1, h2⟩
        exact Nat.mul_ne_zero h1 h2
  | exU ψ ih => intro hloc; exact absurd hloc ((isLocal_exU ψ).mp)
  | exL r g ψ ih =>
    rename_i k'
    intro hloc out hout m
    have hlψ := (isLocal_exL r g ψ).mp hloc
    -- the names of the fragment
    have hEa : Ext "b" (out ++ "a") := ext_b_append hout "a"
    have h_o_w : out ≠ out ++ "w" := Ne.symm (append_ne_self (by decide))
    have h_o_m : out ≠ out ++ "m" := Ne.symm (append_ne_self (by decide))
    have h_w_o : out ++ "w" ≠ out := append_ne_self (by decide)
    have h_m_o : out ++ "m" ≠ out := append_ne_self (by decide)
    have h_w_m : out ++ "w" ≠ out ++ "m" := append_ne_append (by decide)
    have h_m_w : out ++ "m" ≠ out ++ "w" := append_ne_append (by decide)
    have h_o_e : ∀ i, out ≠ envName i := fun i => ne_envName_of_ext hout (ext_refl out) i
    have h_w_e : ∀ i, out ++ "w" ≠ envName i :=
      fun i => ne_envName_of_ext hout (ext_append out "w") i
    have h_m_e : ∀ i, out ++ "m" ≠ envName i :=
      fun i => ne_envName_of_ext hout (ext_append out "m") i
    have he : botCom jd (DistFO.exL r g ψ) out =
        .seq (guardLoad g.toList (out ++ "g") (out ++ "m"))
          (.seq (.assign out (.lit 0))
            (.seq (.assign (out ++ "w") (.lit 0))
              (.while (.lt (.var (out ++ "w")) (.var (out ++ "m")))
                (.seq (.assign (envName k') (.get (out ++ "g") (.var (out ++ "w"))))
                  (.seq (botCom jd ψ (out ++ "a"))
                    (.seq (.assign out (orBitExpr (.var out) (.var (out ++ "a"))))
                      (.assign (out ++ "w") (.add (.var (out ++ "w")) (.lit 1))))))))) := rfl
    have hgl : (guardLoad g.toList (out ++ "g") (out ++ "m")) =
        .seq (foldIdx (fun q (i : ℕ) => Com.store (out ++ "g") (.lit q) (.var (envName i))) 0
          (↑g.toList : List ℕ)) (.assign (out ++ "m") (.lit g.toList.length)) := rfl
    rw [he, hgl]
    refine Spec.of_exists fun σ hσ => ?_
    obtain ⟨hcol, henv, hcardB, hcardlen, hmemψ⟩ : BotEnv n L jd C σ ∧
        (∀ i : Fin k', σ.vars (envName (i : ℕ)) = ((m i : Fin n) : ℕ)) ∧
        g.card < B ∧ g.card ≤ (σ.arrs (out ++ "g")).length ∧ BotMem B ψ (out ++ "a") σ :=
      ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2⟩
    have hNcard : g.toList.length = g.card := Finset.length_toList g
    have hNcoe : (↑g.toList : List ℕ).length = g.card := by
      rw [length_coe_list]; exact hNcard
    -- the guard load
    have hslots : ∀ i ∈ (↑g.toList : List ℕ), σ.vars (envName i) < B := by
      intro i hi
      obtain ⟨j, -, rfl⟩ := mem_coe_list g.toList i hi
      rw [henv j]
      exact lt_trans (m j).isLt hn
    obtain ⟨Gv₀, hGv₀⟩ := exists_arrOf (n := (σ.arrs (out ++ "g")).length) rfl
    obtain ⟨σ₁, hrun₁, hvars₁, harrs₁, Gv, hGv, -, hGvval⟩ :=
      (guardFold_spec (B := B) (out ++ "g") (σ.arrs (out ++ "g")).length
        (↑g.toList : List ℕ) 0 Gv₀).run (σ := σ)
        ⟨hGv₀, by rw [hNcoe]; omega, by rw [hNcoe]; omega, hslots⟩
    -- the guard count and the accumulator
    have hcnt := Run.assign (B := B) (x := out ++ "m") (σ := σ₁)
      (evalB_lit (show g.toList.length < B by rw [hNcard]; omega))
    have hacc := Run.assign (B := B) (x := out) (σ := σ₁.setVar (out ++ "m") g.toList.length)
      (e := .lit 0) (evalB_lit (show 0 < B by omega))
    set σ₃ := (σ₁.setVar (out ++ "m") g.toList.length).setVar out 0 with hσ₃def
    -- the loop invariant
    set I : Env → Prop := fun τ => BotEnv n L jd C τ ∧
      (∀ i : Fin k', τ.vars (envName (i : ℕ)) = ((m i : Fin n) : ℕ)) ∧
      τ.vars (out ++ "m") = g.card ∧
      τ.arrs (out ++ "g") = arrOf (σ.arrs (out ++ "g")).length Gv ∧
      BotMem B ψ (out ++ "a") τ ∧ τ.vars (out ++ "w") ≤ g.card ∧ τ.vars out ≤ 1 ∧
      (τ.vars out ≠ 0 ↔ ∃ i ∈ g.toList.take (τ.vars (out ++ "w")),
        Sat (⊥ : SimpleGraph (Fin n)) (colRead n C L) (Fin.snoc m (m i)) ψ) with hIdef
    -- one turn
    have hbody : Spec B (fun τ => I τ ∧ τ.vars (out ++ "w") < g.card)
        (.seq (.assign (envName k') (.get (out ++ "g") (.var (out ++ "w"))))
          (.seq (botCom jd ψ (out ++ "a"))
            (.seq (.assign out (orBitExpr (.var out) (.var (out ++ "a"))))
              (.assign (out ++ "w") (.add (.var (out ++ "w")) (.lit 1))))))
        (fun τ τ' => I τ' ∧ τ'.vars (out ++ "w") = τ.vars (out ++ "w") + 1)
        (botCost ψ + 17) := by
      refine Spec.of_exists fun τ hτ => ?_
      obtain ⟨⟨hcolτ, henvτ, hmτ, hgτ, hmemτ, hwτ, hoτ, hiffτ⟩, hwlt⟩ := hτ
      have hwl : τ.vars (out ++ "w") < g.toList.length := by rw [hNcard]; exact hwlt
      have hwl' : τ.vars (out ++ "w") < (↑g.toList : List ℕ).length := by
        rw [hNcoe]; exact hwlt
      have hvtx : Gv (τ.vars (out ++ "w")) =
          ((m g.toList[τ.vars (out ++ "w")] : Fin n) : ℕ) := by
        have h := hGvval (τ.vars (out ++ "w")) hwl'
        rw [Nat.zero_add, getElem_coe_list g.toList _ hwl' hwl, henv] at h
        exact h
      -- the candidate
      have hwB : τ.vars (out ++ "w") < B := by omega
      have hcell : (τ.arrs (out ++ "g"))[τ.vars (out ++ "w")]? =
          some (Gv (τ.vars (out ++ "w"))) := by
        rw [hgτ]
        exact getElem?_arrOf _ (by omega)
      have hcand := Run.assign (B := B) (x := envName k') (σ := τ)
        (evalB_get (evalB_var hwB) hcell (by rw [hvtx]; exact lt_trans (m _).isLt hn))
      set τ₁ := τ.setVar (envName k') (Gv (τ.vars (out ++ "w"))) with hτ₁def
      -- the fragment
      have henv₁ : ∀ i : Fin (k' + 1), τ₁.vars (envName (i : ℕ)) =
          (((Fin.snoc m (m g.toList[τ.vars (out ++ "w")]) :
            Fin (k' + 1) → Fin n) i : Fin n) : ℕ) := by
        intro i
        refine Fin.lastCases ?_ ?_ i
        · rw [Fin.snoc_last, Fin.val_last, hτ₁def, vars_setVar, if_pos rfl, hvtx]
        · intro j
          rw [Fin.snoc_castSucc, Fin.val_castSucc, hτ₁def, vars_setVar,
            if_neg (envName_ne_of_lt j.isLt)]
          exact henvτ j
      obtain ⟨τ₂, hrun₂, ⟨hb2, hbiff2⟩, hfv₂, hfa₂, hlen₂⟩ :=
        (bot_framed hlψ (ih hlψ (out ++ "a") hEa
          (Fin.snoc m (m g.toList[τ.vars (out ++ "w")])))).run (σ := τ₁)
          ⟨fun c hc => by rw [hτ₁def, arrs_setVar]; exact hcolτ c hc, henv₁,
            botMem_of_length (fun a => by rw [hτ₁def, arrs_setVar]) ψ (out ++ "a") hmemτ⟩
      -- what the fragment left alone
      have hkeep : ∀ y : String, ¬ Ext (out ++ "a") y → (∀ i, y ≠ envName i) →
          y ≠ envName k' → τ₂.vars y = τ.vars y := by
        intro y hy hye hyk
        rw [hfv₂ y hy (fun i _ => hye i), hτ₁def, vars_setVar, if_neg hyk]
      have hoτ₂ : τ₂.vars out = τ.vars out :=
        hkeep out (not_ext_append_left (by decide)) h_o_e (h_o_e k')
      have hwτ₂ : τ₂.vars (out ++ "w") = τ.vars (out ++ "w") :=
        hkeep (out ++ "w") (not_ext_append_of_ne (by decide)) h_w_e (h_w_e k')
      have hmτ₂ : τ₂.vars (out ++ "m") = τ.vars (out ++ "m") :=
        hkeep (out ++ "m") (not_ext_append_of_ne (by decide)) h_m_e (h_m_e k')
      -- the accumulation
      obtain ⟨t, ht1, hteval, htiff⟩ :=
        evalB_orBitExpr (B := B) (σ := τ₂) hB (u := τ₂.vars out) (by omega) hb2
          (evalB_var (by omega)) (evalB_var (by omega))
      have hor := Run.assign (B := B) (x := out) (σ := τ₂) hteval
      set τ₃ := τ₂.setVar out t with hτ₃def
      have hw₃ : τ₃.vars (out ++ "w") = τ.vars (out ++ "w") := by
        rw [hτ₃def, vars_setVar, if_neg h_w_o]; exact hwτ₂
      have hstepeval : (Expr.add (.var (out ++ "w")) (.lit 1)).evalB B τ₃ =
          some (τ.vars (out ++ "w") + 1) := by
        have h := evalB_bin (B := B) (op := .add) (σ := τ₃)
          (evalB_var (x := out ++ "w") (by rw [hw₃]; omega)) (evalB_lit (show 1 < B by omega))
          (by simp only [Bop.apply_add, hw₃]; omega)
        simpa [hw₃] using h
      have hstepw := Run.assign (B := B) (x := out ++ "w") (σ := τ₃) hstepeval
      set τ₄ := τ₃.setVar (out ++ "w") (τ.vars (out ++ "w") + 1) with hτ₄def
      -- the projections of the final state
      have hp_out : τ₄.vars out = t := by
        rw [hτ₄def, vars_setVar, if_neg h_o_w, hτ₃def, vars_setVar, if_pos rfl]
      have hp_w : τ₄.vars (out ++ "w") = τ.vars (out ++ "w") + 1 := by
        rw [hτ₄def, vars_setVar, if_pos rfl]
      have hp_m : τ₄.vars (out ++ "m") = τ.vars (out ++ "m") := by
        rw [hτ₄def, vars_setVar, if_neg h_m_w, hτ₃def, vars_setVar, if_neg h_m_o]
        exact hmτ₂
      have hp_arrs : ∀ a, τ₄.arrs a = τ₂.arrs a := by
        intro a
        rw [hτ₄def, arrs_setVar, hτ₃def, arrs_setVar]
      refine ⟨τ₄, _, hcand.seq (hrun₂.seq (hor.seq hstepw)), ?_,
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [size_get, size_var, size_lit, size_bin, size_orBitExpr]
        omega
      · intro c hc
        rw [hp_arrs, hfa₂ (colName jd c) (not_ext_of_fresh hEa (not_ext_b_colName jd c)),
          hτ₁def, arrs_setVar]
        exact hcolτ c hc
      · intro i
        rw [hτ₄def, vars_setVar, if_neg (Ne.symm (h_w_e (i : ℕ))),
          hτ₃def, vars_setVar, if_neg (Ne.symm (h_o_e (i : ℕ))),
          hfv₂ (envName (i : ℕ)) (not_ext_envName hEa _)
            (fun i' hi' => envName_ne_of_lt (by omega)),
          hτ₁def, vars_setVar, if_neg (envName_ne_of_lt i.isLt)]
        exact henvτ i
      · rw [hp_m]; exact hmτ
      · rw [hp_arrs, hfa₂ (out ++ "g") (not_ext_append_of_ne (by decide)), hτ₁def, arrs_setVar]
        exact hgτ
      · exact botMem_of_length (fun a => by rw [hp_arrs, hlen₂ a, hτ₁def, arrs_setVar])
          ψ (out ++ "a") hmemτ
      · rw [hp_w]; omega
      · rw [hp_out]; exact ht1
      · rw [hp_out, hp_w, htiff, hoτ₂, hiffτ, hbiff2]
        have hsplit : g.toList.take (τ.vars (out ++ "w") + 1) =
            g.toList.take (τ.vars (out ++ "w")) ++ [g.toList[τ.vars (out ++ "w")]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hwl]
          rfl
        rw [hsplit]
        constructor
        · rintro (⟨i, hi, hsat⟩ | hsat)
          · exact ⟨i, List.mem_append_left _ hi, hsat⟩
          · exact ⟨g.toList[τ.vars (out ++ "w")], List.mem_append_right _ List.mem_cons_self, hsat⟩
        · rintro ⟨i, hi, hsat⟩
          rcases List.mem_append.mp hi with h | h
          · exact Or.inl ⟨i, h, hsat⟩
          · rw [List.mem_singleton] at h
            exact Or.inr (h ▸ hsat)
      · rw [hp_w]
    -- the loop's entry state
    have hstart : I (σ₃.setVar (out ++ "w") 0) := by
      have hq_arrs : ∀ a, (σ₃.setVar (out ++ "w") 0).arrs a = σ₁.arrs a := by
        intro a
        rw [arrs_setVar, hσ₃def, arrs_setVar, arrs_setVar]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro c hc
        rw [hq_arrs, harrs₁ (colName jd c) (Ne.symm (ne_colName_of_ext hout
          (ext_append out "g") jd c))]
        exact hcol c hc
      · intro i
        rw [vars_setVar, if_neg (Ne.symm (h_w_e (i : ℕ))), hσ₃def, vars_setVar,
          if_neg (Ne.symm (h_o_e (i : ℕ))), vars_setVar, if_neg (Ne.symm (h_m_e (i : ℕ))),
          hvars₁]
        exact henv i
      · rw [vars_setVar, if_neg h_m_w, hσ₃def, vars_setVar, if_neg h_m_o, vars_setVar,
          if_pos rfl]
        exact hNcard
      · rw [hq_arrs]; exact hGv
      · refine botMem_of_length (fun a => ?_) ψ (out ++ "a") hmemψ
        rw [hq_arrs]
        by_cases hag : a = out ++ "g"
        · rw [hag, hGv, length_arrOf, hGv₀, length_arrOf]
        · rw [harrs₁ a hag]
      · rw [vars_setVar, if_pos rfl]; omega
      · rw [vars_setVar, if_neg h_o_w, hσ₃def, vars_setVar, if_pos rfl]; omega
      · rw [vars_setVar, if_neg h_o_w, hσ₃def, vars_setVar, if_pos rfl, vars_setVar,
          if_pos rfl]
        simp
    obtain ⟨σ₄, hrun₄, hI₄, hw₄⟩ :=
      (Spec.forRangeZero (B := B) (out ++ "w") (out ++ "m") I g.card (botCost ψ + 17)
        (by omega) (fun τ hτ => hτ.2.2.2.2.2.1) (fun τ hτ => hτ.2.2.1) hbody).run
        (σ := σ₃) hstart
    -- the assembly
    obtain ⟨-, -, -, -, -, -, hb4, hiff4⟩ := hI₄
    refine ⟨σ₄, _, (hrun₁.seq hcnt).seq (hacc.seq hrun₄), ?_, hb4, ?_⟩
    · rw [botCost, hNcoe]
      have h1 : 3 * g.card + (botCost ψ + 17 + 4) * g.card = (botCost ψ + 24) * g.card := by ring
      have h2 : (botCost ψ + 24) * g.card ≤ (botCost ψ + 30) * g.card :=
        Nat.mul_le_mul_right _ (by omega)
      have h3 : (botCost ψ + 30) * g.card ≤ (botCost ψ + 30) * (g.card + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [size_lit]
      omega
    · rw [hiff4, hw₄, List.take_of_length_le (by rw [hNcard]), BotEval.sat_exL_bot r g ψ]
      constructor
      · rintro ⟨i, hi, hsat⟩
        exact ⟨i, Finset.mem_toList.mp hi, hsat⟩
      · rintro ⟨i, hi, hsat⟩
        exact ⟨i, Finset.mem_toList.mpr hi, hsat⟩

/-! ### The base pass

`RamDriver.baseCom` is the representative scan followed by a walk of the
carrier that evaluates every formula of the bottom table at every
vertex. The walk of one vertex is a straight line of fragments, one per
tabled formula, each followed by the store of its bit. -/

/-- Two names with different first letters are different names. -/
theorem ne_of_head_ne {y z : String} {c d : Char}
    (hy : ∃ t, y.toList = c :: t) (hz : ∃ u, z.toList = d :: u) (h : c ≠ d) : y ≠ z := by
  obtain ⟨t, hy⟩ := hy
  obtain ⟨u, hz⟩ := hz
  intro he
  rw [he, hz] at hy
  exact h (List.cons.inj hy).1.symm

theorem head_colName (j c : ℕ) : ∃ t, (colName j c).toList = 'c' :: t :=
  ⟨_, by rw [colName, String.toList_append, String.toList_append, String.toList_append]; rfl⟩

theorem head_tabName (j i : ℕ) : ∃ t, (tabName j i).toList = 't' :: t :=
  ⟨_, by rw [tabName, String.toList_append, String.toList_append, String.toList_append]; rfl⟩

theorem head_alvName (j : ℕ) : ∃ t, (alvName j).toList = 'a' :: t :=
  ⟨_, by rw [alvName, String.toList_append]; rfl⟩

theorem head_gamName (j : ℕ) : ∃ t, (gamName j).toList = 'g' :: t :=
  ⟨_, by rw [gamName, String.toList_append]; rfl⟩

theorem head_envName (i : ℕ) : ∃ t, (envName i).toList = 'e' :: t :=
  ⟨_, by rw [envName, String.toList_append]; rfl⟩

theorem colName_ne_tabName (j c j' i : ℕ) : colName j c ≠ tabName j' i :=
  ne_of_head_ne (head_colName j c) (head_tabName j' i) (by decide)

theorem alvName_ne_tabName (j j' i : ℕ) : alvName j ≠ tabName j' i :=
  ne_of_head_ne (head_alvName j) (head_tabName j' i) (by decide)

theorem gamName_ne_tabName (j j' i : ℕ) : gamName j ≠ tabName j' i :=
  ne_of_head_ne (head_gamName j) (head_tabName j' i) (by decide)

theorem colName_ne_rep (j c : ℕ) : colName j c ≠ "rep" :=
  ne_of_head_ne (head_colName j c) ⟨_, rfl⟩ (by decide)

theorem alvName_ne_rep (j : ℕ) : alvName j ≠ "rep" :=
  ne_of_head_ne (head_alvName j) ⟨_, rfl⟩ (by decide)

theorem gamName_ne_rep (j : ℕ) : gamName j ≠ "rep" :=
  ne_of_head_ne (head_gamName j) ⟨_, rfl⟩ (by decide)

theorem lit_ne_envName {q : String} {c : Char} (hq : ∃ t, q.toList = c :: t)
    (hc : c ≠ 'e') (i : ℕ) : q ≠ envName i :=
  ne_of_head_ne hq (head_envName i) hc

/-- The cells of one table of the bottom depth, up to a per-formula
bound. -/
def BaseTabOk (q_top cap mb ℓ n : ℕ) (φ : Lax3.FirstOrder.FO 0) (C : ℕ → ℕ → ℕ)
    (bd : ℕ → ℕ) (σ : Env) : Prop :=
  ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ ℓ).length), ∃ Tb : ℕ → ℕ,
    σ.arrs (tabName ℓ i) = arrOf n Tb ∧
    ∀ v : Fin n, (v : ℕ) < bd i → Tb (v : ℕ) ≤ 1 ∧
      (Tb (v : ℕ) ≠ 0 ↔ Sat (⊥ : SimpleGraph (Fin n)) (colRead n C (sigL cap mb ℓ)) (fun _ => v)
        (tablesAt q_top cap mb φ ℓ)[i])

/-- Everything the base pass reads and never writes, together with what
it has written so far. -/
def BaseBase (B n q_top cap mb ℓ : ℕ) (C : ℕ → ℕ → ℕ) (φ : Lax3.FirstOrder.FO 0)
    (σ : Env) : Prop :=
  σ.vars "n" = n ∧ BotEnv n (sigL cap mb ℓ) ℓ C σ ∧ BaseMem B q_top cap mb ℓ φ σ

/-- The cost of the straight line of fragments of one vertex. -/
noncomputable def blockCost {L : ℕ} : List (DistFO L 1) → ℕ
  | [] => 1
  | β :: l => botCost β + 3 + blockCost l

theorem one_le_blockCost {L : ℕ} (l : List (DistFO L 1)) : 1 ≤ blockCost l := by
  induction l with
  | nil => rw [blockCost]
  | cons β l ih => rw [blockCost]; omega

/-- **One vertex of the base pass**: a straight line of fragments, one
per tabled formula, each followed by the store of its bit. -/
theorem base_block_spec {B n q_top cap mb ℓ : ℕ} {C : ℕ → ℕ → ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hB : 1 < B) (hn : n < B) (hbit : ∀ c < sigL cap mb ℓ, ∀ v < n, C c v ≤ 1)
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ ℓ, IsLocal β) {z₀ : ℕ} (hz₀ : z₀ < n) :
    ∀ (l : List (DistFO (sigL cap mb ℓ) 1)) (p : ℕ), l = (tablesAt q_top cap mb φ ℓ).drop p →
      Spec B
        (fun σ => BaseBase B n q_top cap mb ℓ C φ σ ∧ σ.vars "z" = z₀ ∧
          σ.vars (envName 0) = z₀ ∧
          BaseTabOk q_top cap mb ℓ n φ C (fun i => if i < p then z₀ + 1 else z₀) σ)
        (foldIdx (fun i β => .seq (botCom ℓ β "bb") (.store (tabName ℓ i) (.var "z") (.var "bb")))
          p l)
        (fun _ σ' => BaseBase B n q_top cap mb ℓ C φ σ' ∧ σ'.vars "z" = z₀ ∧
          σ'.vars (envName 0) = z₀ ∧
          BaseTabOk q_top cap mb ℓ n φ C (fun i => if i < p + l.length then z₀ + 1 else z₀) σ')
        (blockCost l) := by
  have hEbb : Ext "b" "bb" := ext_of_prefix (by decide)
  intro l
  induction l with
  | nil =>
    intro p _
    refine Spec.of_exists fun σ hσ => ?_
    exact ⟨σ, 1, Run.skip, by rw [blockCost], hσ.1, hσ.2.1, hσ.2.2.1, by
      simpa using hσ.2.2.2⟩
  | cons β l ih =>
    intro p hl
    have hp : p < (tablesAt q_top cap mb φ ℓ).length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hl
      exact absurd hl (by simp)
    rw [List.drop_eq_getElem_cons hp] at hl
    obtain ⟨hβ, hltail⟩ := List.cons.inj hl
    subst hβ
    have hloc : IsLocal (tablesAt q_top cap mb φ ℓ)[p] := hlocal _ (List.getElem_mem hp)
    refine Spec.of_exists fun σ hσ => ?_
    obtain ⟨⟨hvn, hcol, hmem⟩, hz, hev, htab⟩ := hσ
    -- the fragment
    obtain ⟨σ₁, hrun₁, ⟨hb1, hbiff1⟩, hfv₁, hfa₁, hlen₁⟩ :=
      (bot_framed hloc (bot_spec (jd := ℓ) hB hn hbit (tablesAt q_top cap mb φ ℓ)[p] hloc "bb"
        hEbb (fun _ => (⟨z₀, hz₀⟩ : Fin n)))).run (σ := σ)
        ⟨hcol, fun i => by
          rw [show (i : ℕ) = 0 from by omega, hev], hmem p hp⟩
    have hkeep : ∀ y : String, ¬ Ext "bb" y → (∀ i, 1 ≤ i → y ≠ envName i) →
        σ₁.vars y = σ.vars y := fun y hy hy' => hfv₁ y hy hy'
    have hvn₁ : σ₁.vars "n" = n := by
      rw [hkeep "n" (not_ext_of_not_prefix (by decide))
        (fun i _ => lit_ne_envName ⟨_, rfl⟩ (by decide) i)]
      exact hvn
    have hz₁ : σ₁.vars "z" = z₀ := by
      rw [hkeep "z" (not_ext_of_not_prefix (by decide))
        (fun i _ => lit_ne_envName ⟨_, rfl⟩ (by decide) i)]
      exact hz
    have hev₁ : σ₁.vars (envName 0) = z₀ := by
      rw [hkeep (envName 0) (not_ext_envName hEbb 0) (fun i hi => envName_ne_of_lt (by omega))]
      exact hev
    have hcol₁ : BotEnv n (sigL cap mb ℓ) ℓ C σ₁ := fun c hc => by
      rw [hfa₁ (colName ℓ c) (not_ext_of_fresh hEbb (not_ext_b_colName ℓ c))]
      exact hcol c hc
    have htab₁ : BaseTabOk q_top cap mb ℓ n φ C (fun i => if i < p then z₀ + 1 else z₀) σ₁ := by
      intro i hi
      obtain ⟨Tb, hTb, hTbval⟩ := htab i hi
      refine ⟨Tb, ?_, hTbval⟩
      rw [hfa₁ (tabName ℓ i) (not_ext_of_fresh hEbb (not_ext_b_tabName ℓ i))]
      exact hTb
    -- the store
    obtain ⟨Tp, hTp, hTpval⟩ := htab₁ p hp
    have hst := Run.store (B := B) (a := tabName ℓ p) (i := .var "z") (e := .var "bb") (σ := σ₁)
      (by rw [evalB_var (by omega), hz₁]) (by rw [evalB_var (by omega)])
      (by rw [hTp, length_arrOf]; exact hz₀)
    set σ₂ := σ₁.setArr (tabName ℓ p) z₀ (σ₁.vars "bb") with hσ₂def
    have hlen₂ : ∀ a, (σ₂.arrs a).length = (σ₁.arrs a).length := fun a => by
      rw [hσ₂def]; exact length_arrs_setArr ..
    have htab₂ : BaseTabOk q_top cap mb ℓ n φ C (fun i => if i < p + 1 then z₀ + 1 else z₀) σ₂ := by
      intro i hi
      by_cases hip : i = p
      · subst hip
        refine ⟨fun k => if k = z₀ then σ₁.vars "bb" else Tp k, ?_, ?_⟩
        · rw [hσ₂def, arrs_setArr, if_pos rfl, hTp, set_arrOf]
        · intro v hv
          dsimp only
          by_cases hvz : (v : ℕ) = z₀
          · refine ⟨by rw [if_pos hvz]; exact hb1, ?_⟩
            rw [if_pos hvz, hbiff1]
            have hveq : v = (⟨z₀, hz₀⟩ : Fin n) := Fin.ext hvz
            rw [hveq]
          · rw [if_neg hvz]
            refine hTpval v ?_
            show (v : ℕ) < (if i < i then z₀ + 1 else z₀)
            replace hv : (v : ℕ) < (if i < i + 1 then z₀ + 1 else z₀) := hv
            rw [if_neg (lt_irrefl _)]
            rw [if_pos (by omega : i < i + 1)] at hv
            omega
      · obtain ⟨Tb, hTb, hTbval⟩ := htab₁ i hi
        refine ⟨Tb, by rw [hσ₂def, arrs_setArr, if_neg (tabName_ne_of_ne ℓ hip)]; exact hTb, ?_⟩
        intro v hv
        refine hTbval v ?_
        show (v : ℕ) < (if i < p then z₀ + 1 else z₀)
        replace hv : (v : ℕ) < (if i < p + 1 then z₀ + 1 else z₀) := hv
        by_cases hlt : i < p
        · rw [if_pos hlt]
          rw [if_pos (by omega : i < p + 1)] at hv
          exact hv
        · rw [if_neg hlt]
          rw [if_neg (by omega : ¬ i < p + 1)] at hv
          exact hv
    -- the rest of the block
    obtain ⟨σ₃, hrun₃, hbase₃, hz₃, hev₃, htab₃⟩ :=
      (ih (p + 1) hltail).run (σ := σ₂)
        ⟨⟨by rw [hσ₂def, vars_setArr]; exact hvn₁,
          fun c hc => by
            rw [hσ₂def, arrs_setArr, if_neg (colName_ne_tabName ℓ c ℓ p)]; exact hcol₁ c hc,
          fun i hi => botMem_of_length hlen₂ _ "bb"
            (botMem_of_length hlen₁ _ "bb" (hmem i hi))⟩,
          by rw [hσ₂def, vars_setArr]; exact hz₁,
          by rw [hσ₂def, vars_setArr]; exact hev₁, htab₂⟩
    refine ⟨σ₃, _, (hrun₁.seq hst).seq hrun₃, ?_, hbase₃, hz₃, hev₃, ?_⟩
    · rw [blockCost]
      simp only [size_var]
      omega
    · intro i hi
      obtain ⟨Tb, hTb, hTbval⟩ := htab₃ i hi
      refine ⟨Tb, hTb, fun v hv => hTbval v ?_⟩
      show (v : ℕ) < (if i < p + 1 + l.length then z₀ + 1 else z₀)
      replace hv : (v : ℕ) < (if i < p + (l.length + 1) then z₀ + 1 else z₀) := hv
      rwa [show p + 1 + l.length = p + (l.length + 1) from by omega]

/-- The invariant of the base pass: the tables are right at every vertex
the counter has passed. -/
def BaseInv (B n q_top cap mb ℓ : ℕ) (C : ℕ → ℕ → ℕ) (φ : Lax3.FirstOrder.FO 0)
    (σ : Env) : Prop :=
  BaseBase B n q_top cap mb ℓ C φ σ ∧ σ.vars "z" ≤ n ∧
    BaseTabOk q_top cap mb ℓ n φ C (fun _ => σ.vars "z") σ

/-- The cost of one vertex of the base pass. -/
noncomputable def turnCost (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  blockCost (tablesAt q_top cap mb φ ℓ) + 6

/-- The cost of the base pass. -/
noncomputable def baseCost (q_top cap mb ℓ n : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  reprCost ℓ (sigL cap mb ℓ) n + ((turnCost q_top cap mb ℓ φ + 4) * n + 6)

/-- **One vertex of the base pass.** -/
theorem base_turn_spec {B n q_top cap mb ℓ : ℕ} {C : ℕ → ℕ → ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hB : 1 < B) (hn : n < B) (hbit : ∀ c < sigL cap mb ℓ, ∀ v < n, C c v ≤ 1)
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ ℓ, IsLocal β) :
    Spec B (fun σ => BaseInv B n q_top cap mb ℓ C φ σ ∧ σ.vars "z" < n)
      (.seq (.assign (envName 0) (.var "z"))
        (.seq (foldIdx (fun i β =>
            .seq (botCom ℓ β "bb") (.store (tabName ℓ i) (.var "z") (.var "bb"))) 0
            (tablesAt q_top cap mb φ ℓ))
          (.assign "z" (.add (.var "z") (.lit 1)))))
      (fun σ σ' => BaseInv B n q_top cap mb ℓ C φ σ' ∧ σ'.vars "z" = σ.vars "z" + 1)
      (turnCost q_top cap mb ℓ φ) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨⟨hvn, hcol, hmem⟩, hzle, htab⟩, hzlt⟩ := hσ
  -- the environment slot
  have hev := Run.assign (B := B) (x := envName 0) (σ := σ)
    (evalB_var (x := "z") (show σ.vars "z" < B by omega))
  set σ₁ := σ.setVar (envName 0) (σ.vars "z") with hσ₁def
  have hz₁ : σ₁.vars "z" = σ.vars "z" := by
    rw [hσ₁def, vars_setVar, if_neg (lit_ne_envName ⟨_, rfl⟩ (by decide) 0)]
  have htab₁ : BaseTabOk q_top cap mb ℓ n φ C
      (fun i => if i < 0 then σ.vars "z" + 1 else σ.vars "z") σ₁ := by
    intro i hi
    obtain ⟨Tb, hTb, hTbval⟩ := htab i hi
    refine ⟨Tb, by rw [hσ₁def, arrs_setVar]; exact hTb, fun v hv => hTbval v ?_⟩
    show (v : ℕ) < σ.vars "z"
    replace hv : (v : ℕ) < (if i < 0 then σ.vars "z" + 1 else σ.vars "z") := hv
    rw [if_neg (by omega)] at hv
    exact hv
  -- the block
  obtain ⟨σ₂, hrun₂, ⟨hvn₂, hcol₂, hmem₂⟩, hz₂, -, htab₂⟩ :=
    (base_block_spec hB hn hbit hlocal hzlt (tablesAt q_top cap mb φ ℓ) 0
      (by rw [List.drop_zero])).run (σ := σ₁)
      ⟨⟨by rw [hσ₁def, vars_setVar, if_neg (lit_ne_envName ⟨_, rfl⟩ (by decide) 0)]; exact hvn,
        fun c hc => by rw [hσ₁def, arrs_setVar]; exact hcol c hc,
        fun i hi => botMem_of_length (fun a => by rw [hσ₁def, arrs_setVar]) _ "bb" (hmem i hi)⟩,
        hz₁, by rw [hσ₁def, vars_setVar, if_pos rfl], htab₁⟩
  · -- the counter
    have hstep : (Expr.add (.var "z") (.lit 1)).evalB B σ₂ = some (σ.vars "z" + 1) := by
      have h := evalB_bin (B := B) (op := .add) (σ := σ₂)
        (evalB_var (x := "z") (by rw [hz₂]; omega)) (evalB_lit (show 1 < B by omega))
        (by simp only [Bop.apply_add, hz₂]; omega)
      simpa [hz₂] using h
    have hcnt := Run.assign (B := B) (x := "z") (σ := σ₂) hstep
    refine ⟨σ₂.setVar "z" (σ.vars "z" + 1), _, hev.seq (hrun₂.seq hcnt), ?_,
      ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [turnCost]
      simp only [size_var, size_lit, size_bin]
      omega
    · rw [vars_setVar, if_neg (by decide)]; exact hvn₂
    · intro c hc; rw [arrs_setVar]; exact hcol₂ c hc
    · exact fun i hi => botMem_of_length (fun a => by rw [arrs_setVar]) _ "bb" (hmem₂ i hi)
    · rw [vars_setVar, if_pos rfl]; omega
    · intro i hi
      obtain ⟨Tb, hTb, hTbval⟩ := htab₂ i hi
      refine ⟨Tb, by rw [arrs_setVar]; exact hTb, fun v hv => hTbval v ?_⟩
      show (v : ℕ) < (if i < 0 + (tablesAt q_top cap mb φ ℓ).length then σ.vars "z" + 1
        else σ.vars "z")
      rw [if_pos (by omega)]
      rw [vars_setVar, if_pos rfl] at hv
      exact hv
    · rw [vars_setVar, if_pos rfl]

/-- The two syntactic frames of the representative pass. -/
theorem warrs_reprCom (jd L : ℕ) : (reprCom jd L).warrs = ["rep"] := by
  simp [reprCom, Com.warrs]

theorem wvars_reprCom (jd L : ℕ) : (reprCom jd L).wvars =
    ["rp", "z", "seen", "rw", "rv", "seen", "rw", "rp", "z"] := by
  simp [reprCom, Com.wvars]

/-- **The base pass, walked.** After it, every table of the bottom depth
holds, at every vertex, the truth value of its formula on the edgeless
arena. -/
theorem base_spec {B n q_top cap mb ℓ : ℕ} {C : ℕ → ℕ → ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hB : 1 < B) (hn : n < B) (hL : 2 ^ sigL cap mb ℓ < B)
    (hbit : ∀ c < sigL cap mb ℓ, ∀ v < n, C c v ≤ 1)
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ ℓ, IsLocal β) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ BotEnv n (sigL cap mb ℓ) ℓ C σ ∧
        BaseMem B q_top cap mb ℓ φ σ ∧
        (∃ g : ℕ → ℕ, σ.arrs "rep" = arrOf (2 ^ sigL cap mb ℓ) g) ∧
        ∀ (i : ℕ), i < (tablesAt q_top cap mb φ ℓ).length →
          ∃ Tb : ℕ → ℕ, σ.arrs (tabName ℓ i) = arrOf n Tb)
      (baseCom q_top cap mb ℓ φ)
      (fun _ σ' => BaseTabOk q_top cap mb ℓ n φ C (fun _ => n) σ')
      (baseCost q_top cap mb ℓ n φ) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hvn, hcol, hmem, hrep, htabs⟩ := hσ
  -- the representative pass
  obtain ⟨σ₁, hrun₁, -, hfv₁, hfa₁, -, -⟩ :=
    (repr_spec (jd := ℓ) hB hn hL hbit).frame.run (σ := σ) ⟨hvn, hcol, hrep⟩
  have hlen₁ : ∀ a, (σ₁.arrs a).length = (σ.arrs a).length := fun a => run_length_arrs hrun₁ a
  have hvn₁ : σ₁.vars "n" = n := by
    rw [hfv₁ "n" (by rw [wvars_reprCom]; decide)]; exact hvn
  have hcol₁ : BotEnv n (sigL cap mb ℓ) ℓ C σ₁ := fun c hc => by
    rw [hfa₁ (colName ℓ c) (by rw [warrs_reprCom, List.mem_singleton]; exact colName_ne_rep ℓ c)]
    exact hcol c hc
  have hmem₁ : BaseMem B q_top cap mb ℓ φ σ₁ :=
    fun i hi => botMem_of_length hlen₁ _ "bb" (hmem i hi)
  have hnotrep : ∀ i : ℕ, tabName ℓ i ∉ (reprCom ℓ (sigL cap mb ℓ)).warrs := by
    intro i
    rw [warrs_reprCom, List.mem_singleton]
    exact tabName_ne_lit ℓ i (by decide)
  have htabs₁ : ∀ (i : ℕ), i < (tablesAt q_top cap mb φ ℓ).length →
      ∃ Tb : ℕ → ℕ, σ₁.arrs (tabName ℓ i) = arrOf n Tb := by
    intro i hi
    obtain ⟨Tb, hTb⟩ := htabs i hi
    refine ⟨Tb, ?_⟩
    rw [hfa₁ (tabName ℓ i) (hnotrep i)]
    exact hTb
  have hstart : BaseTabOk q_top cap mb ℓ n φ C (fun _ => (σ₁.setVar "z" 0).vars "z")
      (σ₁.setVar "z" 0) := by
    intro i hi
    obtain ⟨Tb, hTb⟩ := htabs₁ i hi
    refine ⟨Tb, by rw [arrs_setVar]; exact hTb, fun v hv => ?_⟩
    exfalso
    replace hv : (v : ℕ) < (σ₁.setVar "z" 0).vars "z" := hv
    rw [vars_setVar, if_pos rfl] at hv
    omega
  -- the walk of the carrier
  obtain ⟨σ₂, hrun₂, ⟨-, -, htab₂⟩, hz₂⟩ :=
    (Spec.forRangeZero (B := B) "z" "n" (BaseInv B n q_top cap mb ℓ C φ) n
      (turnCost q_top cap mb ℓ φ) hn (fun τ hτ => hτ.2.1) (fun τ hτ => hτ.1.1)
      (base_turn_spec hB hn hbit hlocal)).run (σ := σ₁)
      ⟨⟨by rw [vars_setVar, if_neg (by decide)]; exact hvn₁,
        fun c hc => by rw [arrs_setVar]; exact hcol₁ c hc,
        fun i hi => botMem_of_length (fun a => by rw [arrs_setVar]) _ "bb" (hmem₁ i hi)⟩,
        by rw [vars_setVar, if_pos rfl]; omega, hstart⟩
  refine ⟨σ₂, _, hrun₁.seq hrun₂, ?_, ?_⟩
  · rw [baseCost]
  · intro i hi
    obtain ⟨Tb, hTb, hTbval⟩ := htab₂ i hi
    exact ⟨Tb, hTb, fun v hv => hTbval v (by rw [hz₂]; exact v.isLt)⟩

/-! ### The obligation

`RamDriver.BaseImplements` is the base case's obligation. What is
proved below is that obligation with two hypotheses on its parameters,
in the manner of `RamDriverBase.readbackStep`:

* **the colour cells are bits.** The representative scan compares two
  vertices by comparing colour *cells*, so the rows it distinguishes are
  the numeric ones, and its table is `2 ^ sigL cap mb ℓ` long — which
  bounds the scan only if a cell is `0` or `1`. Every pass that writes a
  colour array writes a bit, so this is a clause missing from those
  passes' postconditions rather than a property missing from the
  program;
* **the base evaluator's memory.** `RamDriver.botCom` stores the guard
  set of every local quantifier into a candidate array of its own name,
  and no precondition of `BaseImplements` says those arrays are there:
  the clause `Sized [("rep", 2 ^ sigL cap mb ℓ)]` sizes the
  representative table and nothing else. `BaseMem` is the missing
  clause, and it enters here as the hypothesis that the obligation's own
  precondition implies it — which is where the surface has to grow. -/

/-- The output tape is not touched by a guard load. -/
theorem noWrite_guardFold (arr : String) : ∀ (l : List ℕ) (p : ℕ),
    (foldIdx (fun q (i : ℕ) => Com.store arr (.lit q) (.var (envName i))) p l).NoWrite := by
  intro l
  induction l with
  | nil => intro p; exact Com.noWrite_skip
  | cons x xs ih =>
    intro p
    have he : (foldIdx (fun q (i : ℕ) => Com.store arr (.lit q) (.var (envName i))) p (x :: xs))
        = .seq (Com.store arr (.lit p) (.var (envName x)))
            (foldIdx (fun q (i : ℕ) => Com.store arr (.lit q) (.var (envName i))) (p + 1) xs) :=
      rfl
    rw [he]
    exact ⟨trivial, ih (p + 1)⟩

/-- Nor a flat pass over a range. -/
theorem noWrite_foldRange (f : ℕ → Com) (hf : ∀ i, (f i).NoWrite) (m : ℕ) :
    (foldRange f m).NoWrite := by
  rw [foldRange]
  induction (List.range m) with
  | nil => exact Com.noWrite_skip
  | cons x xs ih => exact ⟨hf x, ih⟩

/-- Nor the environment load. -/
theorem noWrite_envLoad (k : ℕ) (arr cnt : String) : (envLoad k arr cnt).NoWrite :=
  ⟨noWrite_foldRange (fun i => Com.store arr (.lit i) (.var (envName i))) (fun _ => trivial) k,
    trivial, trivial, trivial, trivial, trivial⟩

/-- A fragment of the generated evaluator writes nothing to the tape. -/
theorem noWrite_botCom {L jd : ℕ} : ∀ {k : ℕ} (ψ : DistFO L k) (out : String),
    (botCom jd ψ out).NoWrite := by
  intro k ψ
  induction ψ with
  | adj i j => intro out; exact trivial
  | eq i j => intro out; exact ⟨trivial, trivial⟩
  | color c i => intro out; exact ⟨trivial, trivial⟩
  | distLe r i j => intro out; exact ⟨trivial, trivial⟩
  | distColorLt r c i =>
    intro out
    by_cases hr : r = 0
    · rw [show botCom jd (DistFO.distColorLt r c i) out = .assign out (.lit 0) by
        rw [botCom, if_pos hr]]
      exact trivial
    · rw [show botCom jd (DistFO.distColorLt r c i) out =
        .ite (.lt (.lit 0) (.get (colName jd (c : ℕ)) (.var (envName (i : ℕ)))))
          (.assign out (.lit 1)) (.assign out (.lit 0)) by rw [botCom, if_neg hr]]
      exact ⟨trivial, trivial⟩
  | not ψ ih => intro out; exact ⟨ih (out ++ "a"), trivial⟩
  | and ψ χ ihψ ihχ => intro out; exact ⟨ihψ (out ++ "a"), ihχ (out ++ "b"), trivial⟩
  | exU ψ ih =>
    intro out
    exact ⟨noWrite_envLoad _ _ _, trivial, trivial, trivial, ih (out ++ "a"), trivial, trivial⟩
  | exL r g ψ ih =>
    intro out
    exact ⟨⟨noWrite_guardFold _ _ _, trivial⟩, trivial, trivial, trivial,
      ih (out ++ "a"), trivial, trivial⟩

/-- The base pass writes nothing to the tape. -/
theorem noWrite_baseFold {L : ℕ} (ℓ : ℕ) : ∀ (l : List (DistFO L 1)) (p : ℕ),
    (foldIdx (fun i β =>
      Com.seq (botCom ℓ β "bb") (.store (tabName ℓ i) (.var "z") (.var "bb"))) p l).NoWrite := by
  intro l
  induction l with
  | nil => exact fun p => Com.noWrite_skip
  | cons β l ih =>
    intro p
    have he : (foldIdx (fun i β =>
        Com.seq (botCom ℓ β "bb") (.store (tabName ℓ i) (.var "z") (.var "bb"))) p (β :: l))
        = .seq (.seq (botCom ℓ β "bb") (.store (tabName ℓ p) (.var "z") (.var "bb")))
            (foldIdx (fun i β =>
              Com.seq (botCom ℓ β "bb") (.store (tabName ℓ i) (.var "z") (.var "bb")))
              (p + 1) l) := rfl
    rw [he]
    exact ⟨⟨noWrite_botCom β "bb", trivial⟩, ih (p + 1)⟩

theorem noWrite_reprCom (jd L : ℕ) : (reprCom jd L).NoWrite := by
  simp [reprCom, Com.NoWrite]

theorem noWrite_baseCom (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    (baseCom q_top cap mb ℓ φ).NoWrite :=
  ⟨noWrite_reprCom ℓ _, trivial, trivial, noWrite_baseFold ℓ _ 0, trivial⟩

/-! #### What the base pass writes -/

theorem warrs_baseFold {L : ℕ} (ℓ : ℕ) : ∀ (l : List (DistFO L 1)) (p : ℕ),
    (∀ β ∈ l, IsLocal β) → ∀ a ∈ (foldIdx (fun i β =>
      Com.seq (botCom ℓ β "bb") (.store (tabName ℓ i) (.var "z") (.var "bb"))) p l).warrs,
      (∃ i, a = tabName ℓ i) ∨ Ext "bb" a := by
  intro l
  induction l with
  | nil => intro p _ a ha; exact absurd ha List.not_mem_nil
  | cons β l ih =>
    intro p hloc a ha
    have he : (foldIdx (fun i β =>
        Com.seq (botCom ℓ β "bb") (.store (tabName ℓ i) (.var "z") (.var "bb"))) p (β :: l))
        = .seq (.seq (botCom ℓ β "bb") (.store (tabName ℓ p) (.var "z") (.var "bb")))
            (foldIdx (fun i β =>
              Com.seq (botCom ℓ β "bb") (.store (tabName ℓ i) (.var "z") (.var "bb")))
              (p + 1) l) := rfl
    rw [he, Com.warrs, Com.warrs] at ha
    rcases List.mem_append.mp ha with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact Or.inr (warrs_botCom β (hloc β List.mem_cons_self) "bb" a h')
      · rw [Com.warrs, List.mem_singleton] at h'
        exact Or.inl ⟨p, h'⟩
    · exact ih (p + 1) (fun γ hγ => hloc γ (List.mem_cons_of_mem _ hγ)) a h

theorem wvars_baseFold {L : ℕ} (ℓ : ℕ) : ∀ (l : List (DistFO L 1)) (p : ℕ),
    (∀ β ∈ l, IsLocal β) → ∀ y ∈ (foldIdx (fun i β =>
      Com.seq (botCom ℓ β "bb") (.store (tabName ℓ i) (.var "z") (.var "bb"))) p l).wvars,
      Ext "bb" y ∨ ∃ i, 1 ≤ i ∧ y = envName i := by
  intro l
  induction l with
  | nil => intro p _ y hy; exact absurd hy List.not_mem_nil
  | cons β l ih =>
    intro p hloc y hy
    have he : (foldIdx (fun i β =>
        Com.seq (botCom ℓ β "bb") (.store (tabName ℓ i) (.var "z") (.var "bb"))) p (β :: l))
        = .seq (.seq (botCom ℓ β "bb") (.store (tabName ℓ p) (.var "z") (.var "bb")))
            (foldIdx (fun i β =>
              Com.seq (botCom ℓ β "bb") (.store (tabName ℓ i) (.var "z") (.var "bb")))
              (p + 1) l) := rfl
    rw [he, Com.wvars, Com.wvars] at hy
    rcases List.mem_append.mp hy with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact wvars_botCom β (hloc β List.mem_cons_self) "bb" y h'
      · exact absurd h' (by rw [Com.wvars]; simp)
    · exact ih (p + 1) (fun γ hγ => hloc γ (List.mem_cons_of_mem _ hγ)) y h

theorem warrs_baseCom {q_top cap mb ℓ : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ ℓ, IsLocal β) :
    ∀ a ∈ (baseCom q_top cap mb ℓ φ).warrs,
      a = "rep" ∨ (∃ i, a = tabName ℓ i) ∨ Ext "bb" a := by
  intro a ha
  rw [show (baseCom q_top cap mb ℓ φ).warrs =
    (reprCom ℓ (sigL cap mb ℓ)).warrs ++ ([] ++ ([] ++ ((foldIdx (fun i β =>
      Com.seq (botCom ℓ β "bb") (.store (tabName ℓ i) (.var "z") (.var "bb"))) 0
      (tablesAt q_top cap mb φ ℓ)).warrs ++ []))) from rfl] at ha
  simp only [List.append_nil, List.nil_append, List.mem_append] at ha
  rcases ha with h | h
  · rw [warrs_reprCom, List.mem_singleton] at h
    exact Or.inl h
  · exact Or.inr (warrs_baseFold ℓ _ 0 hlocal a h)

theorem wvars_baseCom {q_top cap mb ℓ : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ ℓ, IsLocal β) :
    ∀ y ∈ (baseCom q_top cap mb ℓ φ).wvars,
      y ∈ ["rp", "z", "seen", "rw", "rv"] ∨ (∃ i, y = envName i) ∨ Ext "bb" y := by
  intro y hy
  rw [show (baseCom q_top cap mb ℓ φ).wvars =
    (reprCom ℓ (sigL cap mb ℓ)).wvars ++ (["z"] ++ ([envName 0] ++ ((foldIdx (fun i β =>
      Com.seq (botCom ℓ β "bb") (.store (tabName ℓ i) (.var "z") (.var "bb"))) 0
      (tablesAt q_top cap mb φ ℓ)).wvars ++ ["z"]))) from rfl] at hy
  simp only [List.mem_append, List.mem_singleton] at hy
  rcases hy with h | h | h | h | h
  · rw [wvars_reprCom] at h
    refine Or.inl ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    tauto
  · exact Or.inl (by simp [h])
  · exact Or.inr (Or.inl ⟨0, h⟩)
  · rcases wvars_baseFold ℓ _ 0 hlocal y h with h' | ⟨i, -, h'⟩
    · exact Or.inr (Or.inr h')
    · exact Or.inr (Or.inl ⟨i, h'⟩)
  · exact Or.inl (by simp [h])

end Lax3Proofs.RamDriverBot
