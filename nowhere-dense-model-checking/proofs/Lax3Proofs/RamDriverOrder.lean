import Lax3Proofs.RamDriverCluster
import Lax3Proofs.RamAugment

/-!
The **ordering-phase walks** of `Lax3Proofs.RamDriver`: the cover pass,
the augmentation round, and the phase that composes them.
-/

namespace Lax3Proofs.RamDriverOrder

open Lax3.ColoredGraphs Lax3.NeighborhoodCovers
open Lax12.ColoringNumbers Lax12.UniformQuasiWideness
open Lax3Proofs.WalkDistance Lax3Proofs.CoverConstruction
open Lax3Proofs.RamBfs (masked masked_def CsrGraph)
open Lax3Proofs.RamCover (CoverInv CoverState CoverOut CoverPre CoverPost OrdersBy)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n ns : ℕ} {G : SimpleGraph (Fin n)} {A₀ O T ord : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)} {r : ℕ}

/-! ### The word clauses the cover pass's invariant omits

`RamCover.CoverState` pins the four arrays the pass writes and the
three it reads, but says of no array that its cells are *words*. Three
of them have to be, and none follows from anything the invariant
carries.

* `alv` is read by the search — its very first act is
  `.get "alv" (.var "src")` — so the search's `halv` is asked of
  the mask the turn runs against, which is `A₀` with some cells zeroed
  and therefore *not* pinned by `RamCover.CoverInv.mask`: that clause
  says only which cells are zero.
* `dist` is read by the emission scan, at every vertex, and the
  search's postcondition characterizes its cells only *below the cap*
  — a cell holding the sentinel is left unbounded, even though the fill
  in fact put `2r + 1` there.
* `q`, since rebase P1, because the tower export's `Ir.StateBound` is
  state-global: it asks the *entering* cells of both scratch arrays to
  be words, where the hand-walked baseline bounded only what its run
  evaluated (ledger P1/B-d).

All three are `∀ v ∈ σ.arrs a, v < B`, the shape `RamDriver.LevelMem`
already uses, and all three are preserved by *any* bounded run
(`RamDriver.run_mem_arrs_lt`), so carrying them costs one line per
phase. At the driver they are free: `RamDriver.LevelMem` is the `dist`
and `q` halves verbatim and `RamDriver.LevelPre`'s `∀ z < n, M z < B`
becomes the `alv` half the moment `RamDriver.copyCom` has run.

The consequence for the surface is recorded at `coverTurnImplements`. -/

/-- The three word clauses the cover pass needs: the mask, the distance
array and — since the tower search's precondition is state-global
(ledger P1/B-d) — the search's other scratch array all hold words. -/
def CoverWords (B : ℕ) (σ : Env) : Prop :=
  (∀ v ∈ σ.arrs "alv", v < B) ∧ (∀ v ∈ σ.arrs "dist", v < B) ∧
    (∀ v ∈ σ.arrs "q", v < B)

/-- All three clauses survive any bounded run, since a bounded run
stores only words. -/
theorem CoverWords.run {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (hr : Run B c σ σ' K)
    (h : CoverWords B σ) : CoverWords B σ' :=
  ⟨RamDriver.run_mem_arrs_lt hr "alv" h.1, RamDriver.run_mem_arrs_lt hr "dist" h.2.1,
    RamDriver.run_mem_arrs_lt hr "q" h.2.2⟩

/-- And no clause is about a scalar. -/
theorem CoverWords.setVar {B : ℕ} {σ : Env} (x : String) (v : ℕ) (h : CoverWords B σ) :
    CoverWords B (σ.setVar x v) := h

/-- A cell of an array whose cells are all words is a word. -/
theorem lt_of_mem_words {B N k : ℕ} {a : String} {g : ℕ → ℕ} {σ : Env}
    (h : ∀ v ∈ σ.arrs a, v < B) (hg : σ.arrs a = arrOf N g) (hk : k < N) : g k < B :=
  h (g k) (by rw [hg]; exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)

/-! ### The emission scan

`RamCover.emitLoop` walks the carrier once, reading the one distance
array at the two radii of the pass. `EmitInv` is what it carries: the
cluster arena filled from the entering write pointer `xp₀` up to the
current one, holding exactly the vertices *below the counter* that the
search put within `2r`, and the assignment array rewritten at exactly
the vertices below the counter, by the rule
`RamCover.CoverInv.step`'s `hasg` names.

At the exit the counter is the carrier's size and the three clauses are
`RamCover.CoverInv.step`'s `hkeep`, `hblock` and `hasg` verbatim. -/

/-- **The cell the scan leaves behind it.** A vertex some earlier centre
has already claimed keeps its claim; an unclaimed one the current centre
catches records the centre's position; and an unclaimed one it does not
catch keeps the sentinel. This is `RamCover.CoverInv.step`'s `hasg`,
named. -/
def emitCell (D asg : ℕ → ℕ) (c n r w : ℕ) : ℕ :=
  if asg w < n then asg w else if D w ≤ r then c else n

/-- A vertex the centre does not catch keeps what it had, sentinel or
claim. -/
theorem emitCell_of_not_catch {n : ℕ} {D asg : ℕ → ℕ} {c r z : ℕ}
    (hasg : asg z ≤ n) (h : ¬ D z ≤ r) : emitCell D asg c n r z = asg z := by
  rw [emitCell, if_neg h]
  split
  · rfl
  · omega

/-- A vertex already claimed keeps its claim, caught or not. -/
theorem emitCell_of_claimed {n : ℕ} {D asg : ℕ → ℕ} {c r z : ℕ} (h : asg z < n) :
    emitCell D asg c n r z = asg z := by rw [emitCell, if_pos h]

/-- And an unclaimed vertex the centre catches records the centre. -/
theorem emitCell_of_first {n : ℕ} {D asg : ℕ → ℕ} {c r z : ℕ} (h : ¬ asg z < n)
    (h' : D z ≤ r) : emitCell D asg c n r z = c := by rw [emitCell, if_neg h, if_pos h']

/-- What the emission scan of one centre carries at its counter. `Xmem`
and `asg` are the arena and the assignment as the turn found them,
`xp₀` the write pointer it started at, and `D` the distances the search
left. -/
def EmitInv (n : ℕ) (D Xmem asg : ℕ → ℕ) (c xp₀ r : ℕ) (σ : Env) : Prop :=
  ∃ Xm as : ℕ → ℕ,
    σ.vars "n" = n ∧ σ.vars "c" = c ∧
    σ.arrs "dist" = arrOf n D ∧ σ.arrs "asg" = arrOf n as ∧
    σ.arrs "xmem" = arrOf (n * n) Xm ∧
    σ.vars "z" ≤ n ∧ xp₀ ≤ σ.vars "xp" ∧ σ.vars "xp" ≤ xp₀ + σ.vars "z" ∧
    (∀ p < xp₀, Xm p = Xmem p) ∧
    (∀ w, (∃ p, xp₀ ≤ p ∧ p < σ.vars "xp" ∧ Xm p = w) ↔ (w < σ.vars "z" ∧ D w ≤ 2 * r)) ∧
    (∀ p q, xp₀ ≤ p → p < q → q < σ.vars "xp" → Xm p < Xm q) ∧
    (∀ w < n, as w = if w < σ.vars "z" then emitCell D asg c n r w else asg w)

/-- **The assignment clause, one vertex on.** The array is rewritten at
the counter and nowhere else, so the invariant's rule extends by one
provided the new cell at the counter is the one the rule names. -/
theorem rule_extend {n : ℕ} {D asg as as' : ℕ → ℕ} {c z r : ℕ}
    (hrule : ∀ w < n, as w = if w < z then emitCell D asg c n r w else asg w)
    (hne : ∀ w < n, w ≠ z → as' w = as w) (hfix : as' z = emitCell D asg c n r z) :
    ∀ w < n, as' w = if w < z + 1 then emitCell D asg c n r w else asg w := by
  intro w hw
  by_cases hwz : w = z
  · rw [hwz, if_pos (show z < z + 1 by omega)]; exact hfix
  · rw [hne w hw hwz, hrule w hw]
    rcases Nat.lt_or_ge w z with h | h
    · rw [if_pos h, if_pos (show w < z + 1 by omega)]
    · rw [if_neg (show ¬ w < z by omega), if_neg (show ¬ w < z + 1 by omega)]

/-- **The arena clause when the vertex is emitted.** The block grows by
one slot, holding the counter. -/
theorem block_extend_emit {D Xm : ℕ → ℕ} {xp₀ xp z r : ℕ} (hxpa : xp₀ ≤ xp)
    (hblock : ∀ w, (∃ p, xp₀ ≤ p ∧ p < xp ∧ Xm p = w) ↔ (w < z ∧ D w ≤ 2 * r))
    (hle : D z ≤ 2 * r) :
    ∀ w, (∃ p, xp₀ ≤ p ∧ p < xp + 1 ∧ upd Xm xp z p = w) ↔ (w < z + 1 ∧ D w ≤ 2 * r) := by
  intro w
  constructor
  · rintro ⟨p, hp₁, hp₂, hp₃⟩
    rcases Nat.lt_or_ge p xp with hp | hp
    · rw [upd_of_ne _ (show p ≠ xp by omega)] at hp₃
      exact ⟨by have := (hblock w).mp ⟨p, hp₁, hp, hp₃⟩; omega, ((hblock w).mp ⟨p, hp₁, hp, hp₃⟩).2⟩
    · have hpe : p = xp := by omega
      subst hpe
      rw [upd_self] at hp₃
      exact ⟨by omega, by rw [← hp₃]; exact hle⟩
  · rintro ⟨hw₁, hw₂⟩
    rcases Nat.lt_or_ge w z with hw | hw
    · obtain ⟨p, hp₁, hp₂, hp₃⟩ := (hblock w).mpr ⟨hw, hw₂⟩
      exact ⟨p, hp₁, by omega, by rw [upd_of_ne _ (show p ≠ xp by omega)]; exact hp₃⟩
    · exact ⟨xp, hxpa, by omega, by rw [upd_self]; omega⟩

/-- **The block is filled in increasing order** (rebase B6/D1). The
emission scan walks the carrier upwards and appends, so the value at a
later slot of the block is a larger vertex than the value at an earlier
one — which is `RamCover.CoverInv.block_inj` in the form the walk can
carry, and `inj_of_strictMono` is the projection. -/
theorem mono_extend_emit {D Xm : ℕ → ℕ} {xp₀ xp z r : ℕ}
    (hblock : ∀ w, (∃ p, xp₀ ≤ p ∧ p < xp ∧ Xm p = w) ↔ (w < z ∧ D w ≤ 2 * r))
    (hmono : ∀ p q, xp₀ ≤ p → p < q → q < xp → Xm p < Xm q) :
    ∀ p q, xp₀ ≤ p → p < q → q < xp + 1 → upd Xm xp z p < upd Xm xp z q := by
  intro p q hp hpq hq
  rcases Nat.lt_or_ge q xp with h | h
  · rw [upd_of_ne _ (show p ≠ xp by omega), upd_of_ne _ (show q ≠ xp by omega)]
    exact hmono p q hp hpq h
  · have hqe : q = xp := by omega
    subst hqe
    rw [upd_self, upd_of_ne _ (show p ≠ q by omega)]
    exact ((hblock (Xm p)).mp ⟨p, hp, by omega, rfl⟩).1

/-- **Strict monotonicity is injectivity**, in the form
`RamCover.CoverInv.step` asks for. -/
theorem inj_of_strictMono {Xm : ℕ → ℕ} {a b : ℕ}
    (h : ∀ p q, a ≤ p → p < q → q < b → Xm p < Xm q) :
    ∀ p q, a ≤ p → p < b → a ≤ q → q < b → Xm p = Xm q → p = q := by
  intro p q hp₁ hp₂ hq₁ hq₂ he
  rcases Nat.lt_trichotomy p q with h' | h' | h'
  · exact absurd he (Nat.ne_of_lt (h p q hp₁ h' hq₂))
  · exact h'
  · exact absurd he.symm (Nat.ne_of_lt (h q p hq₁ h' hp₂))

/-- **And when it is not.** A vertex outside the cluster adds nothing,
and cannot be the one the extended clause asks about. -/
theorem block_extend_skip {D Xm : ℕ → ℕ} {xp₀ xp z r : ℕ}
    (hblock : ∀ w, (∃ p, xp₀ ≤ p ∧ p < xp ∧ Xm p = w) ↔ (w < z ∧ D w ≤ 2 * r))
    (hle : ¬ D z ≤ 2 * r) :
    ∀ w, (∃ p, xp₀ ≤ p ∧ p < xp ∧ Xm p = w) ↔ (w < z + 1 ∧ D w ≤ 2 * r) := by
  intro w
  rw [hblock w]
  refine ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨?_, h.2⟩⟩
  rcases Nat.lt_or_ge w z with h' | h'
  · exact h'
  · have : w = z := by omega
    subst this
    exact absurd h.2 hle

/-- **One vertex of the emission scan.** The distance is read once and
tested at the two radii: the wider test emits into the cluster arena,
the sharper one records a first catch. The four cases of the walk are
the four the invariant's two rewritten clauses distinguish. -/
theorem emitSlot_spec {B n : ℕ} {D Xmem asg : ℕ → ℕ} {c xp₀ r : ℕ}
    (hc : c < n) (hnnB : n * n < B) (hrB : 2 * r + 1 < B)
    (hasg : ∀ w < n, asg w ≤ n) (hDB : ∀ w < n, D w < B) (hxp₀ : xp₀ + n ≤ n * n) :
    Spec B (fun σ => EmitInv n D Xmem asg c xp₀ r σ ∧ σ.vars "z" < n)
      (RamCover.emitSlot r)
      (fun σ σ' => EmitInv n D Xmem asg c xp₀ r σ' ∧ σ'.vars "z" = σ.vars "z" + 1)
      30 := by
  have hnB : n < B := lt_of_le_of_lt (RamDriver.le_mul_self n) hnnB
  refine Spec.of_exists fun τ hτ => ?_
  obtain ⟨⟨Xm, as, hnv, hcv, hdist, has, hxmem, hzle, hxpa, hxpb, hkeep, hblock, hmono,
    hrule⟩, hz⟩ := hτ
  -- the two array reads of the body, and the bounds they need
  have hasle : ∀ w, w < n → as w ≤ n := by
    intro w hw
    rw [hrule w hw, emitCell]
    split
    · split
      · omega
      · split
        · omega
        · exact le_rfl
    · exact hasg w hw
  have hzB : τ.vars "z" < B := by omega
  have hDzB : D (τ.vars "z") < B := hDB _ hz
  have hxplt : τ.vars "xp" < n * n := by omega
  have hxpB : τ.vars "xp" < B := by omega
  have hcB : c < B := by omega
  have hasz : as (τ.vars "z") = asg (τ.vars "z") := by
    rw [hrule _ hz, if_neg (show ¬ τ.vars "z" < τ.vars "z" by omega)]
  -- `dz := dist[z]`
  have h1 : Run B (.assign "dz" (.get "dist" (.var "z"))) τ
      (τ.setVar "dz" (D (τ.vars "z"))) (1 + (Expr.get "dist" (.var "z")).size) :=
    Run.assign (evalB_get (evalB_var hzB) (by rw [hdist, getElem?_arrOf D hz]) hDzB)
  set τ₁ := τ.setVar "dz" (D (τ.vars "z")) with hτ₁
  have hdz : τ₁.vars "dz" = D (τ.vars "z") := by simp [hτ₁]
  have hdzB : τ₁.vars "dz" < B := by rw [hdz]; exact hDzB
  -- the conditional, in the four cases
  have hmid : ∃ (τ₂ : Env) (K₂ : ℕ) (Xm' as' : ℕ → ℕ),
      Run B (.ite (.lt (.var "dz") (.lit (2 * r + 1)))
        (.seq (.store "xmem" (.var "xp") (.var "z"))
          (.seq (.assign "xp" (.add (.var "xp") (.lit 1)))
            (.ite (.lt (.var "dz") (.lit (r + 1)))
              (.ite (.lt (.get "asg" (.var "z")) (.var "n"))
                .skip
                (.store "asg" (.var "z") (.var "c")))
              .skip)))
        .skip) τ₁ τ₂ K₂ ∧ K₂ ≤ 23 ∧
      τ₂.vars "n" = n ∧ τ₂.vars "c" = c ∧ τ₂.vars "z" = τ.vars "z" ∧
      τ₂.arrs "dist" = arrOf n D ∧ τ₂.arrs "asg" = arrOf n as' ∧
      τ₂.arrs "xmem" = arrOf (n * n) Xm' ∧
      xp₀ ≤ τ₂.vars "xp" ∧ τ₂.vars "xp" ≤ xp₀ + (τ.vars "z" + 1) ∧
      (∀ p < xp₀, Xm' p = Xmem p) ∧
      (∀ w, (∃ p, xp₀ ≤ p ∧ p < τ₂.vars "xp" ∧ Xm' p = w) ↔
        (w < τ.vars "z" + 1 ∧ D w ≤ 2 * r)) ∧
      (∀ p q, xp₀ ≤ p → p < q → q < τ₂.vars "xp" → Xm' p < Xm' q) ∧
      (∀ w < n, as' w = if w < τ.vars "z" + 1 then emitCell D asg c n r w else asg w) := by
    have e1 : τ₁.vars "n" = n := by simp [hτ₁, hnv]
    have e2 : τ₁.vars "c" = c := by simp [hτ₁, hcv]
    have e3 : τ₁.vars "z" = τ.vars "z" := by simp [hτ₁]
    have e4 : τ₁.vars "xp" = τ.vars "xp" := by simp [hτ₁]
    have e5 : τ₁.arrs "dist" = arrOf n D := by simp [hτ₁, hdist]
    have e6 : τ₁.arrs "asg" = arrOf n as := by simp [hτ₁, has]
    have e7 : τ₁.arrs "xmem" = arrOf (n * n) Xm := by simp [hτ₁, hxmem]
    have hcond := evalB_condLt (B := B) (σ := τ₁) (evalB_var hdzB) (evalB_lit hrB)
    rw [hdz] at hcond
    by_cases hle : D (τ.vars "z") ≤ 2 * r
    · -- the vertex is in the cluster: it is emitted, and possibly caught
      rw [decide_eq_true (show D (τ.vars "z") < 2 * r + 1 by omega)] at hcond
      have hs1 : Run B (.store "xmem" (.var "xp") (.var "z")) τ₁
          (τ₁.setArr "xmem" (τ.vars "xp") (τ.vars "z")) (1 + 1 + 1) := by
        have h := Run.store (B := B) (σ := τ₁) (a := "xmem") (i := .var "xp") (e := .var "z")
          (evalB_var (by rw [e4]; exact hxpB)) (evalB_var (by rw [e3]; exact hzB))
          (by rw [e7, length_arrOf, e4]; exact hxplt)
        rw [e4, e3] at h
        simpa using h
      set τa := τ₁.setArr "xmem" (τ.vars "xp") (τ.vars "z") with hτa
      have f4 : τa.vars "xp" = τ.vars "xp" := by rw [hτa, vars_setArr]; exact e4
      have hs2 : Run B (.assign "xp" (.add (.var "xp") (.lit 1))) τa
          (τa.setVar "xp" (τ.vars "xp" + 1)) (1 + 3) := by
        have h := Run.assign (B := B) (σ := τa) (x := "xp") (e := .add (.var "xp") (.lit 1))
          (evalB_bin (evalB_var (by rw [f4]; exact hxpB)) (evalB_lit (show 1 < B by omega))
            (by simp only [Bop.apply_add]; rw [f4]; omega))
        rw [Bop.apply_add, f4] at h
        simpa using h
      set τb := τa.setVar "xp" (τ.vars "xp" + 1) with hτb
      -- the state after the emission, read off the two updates
      have hnb : τb.vars "n" = n := by
        rw [hτb, vars_setVar, if_neg (by decide), hτa, vars_setArr]; exact e1
      have hcb : τb.vars "c" = c := by
        rw [hτb, vars_setVar, if_neg (by decide), hτa, vars_setArr]; exact e2
      have hzb : τb.vars "z" = τ.vars "z" := by
        rw [hτb, vars_setVar, if_neg (by decide), hτa, vars_setArr]; exact e3
      have hxb : τb.vars "xp" = τ.vars "xp" + 1 := by rw [hτb, vars_setVar, if_pos rfl]
      have hdb : τb.arrs "dist" = arrOf n D := by
        rw [hτb, arrs_setVar, hτa, arrs_setArr, if_neg (by decide)]; exact e5
      have hasb : τb.arrs "asg" = arrOf n as := by
        rw [hτb, arrs_setVar, hτa, arrs_setArr, if_neg (by decide)]; exact e6
      have hxmemb : τb.arrs "xmem" = arrOf (n * n) (upd Xm (τ.vars "xp") (τ.vars "z")) := by
        rw [hτb, arrs_setVar, hτa, arrs_setArr, if_pos rfl, e7, set_arrOf_eq_upd]
      have hblockb := block_extend_emit (D := D) hxpa hblock hle
      have hmonob := mono_extend_emit (D := D) (z := τ.vars "z") hblock hmono
      have hkeepb : ∀ p < xp₀, upd Xm (τ.vars "xp") (τ.vars "z") p = Xmem p := by
        intro p hp
        rw [upd_of_ne _ (show p ≠ τ.vars "xp" by omega)]
        exact hkeep p hp
      have hdzb : τb.vars "dz" = D (τ.vars "z") := by
        rw [hτb, vars_setVar, if_neg (by decide), hτa, vars_setArr]; exact hdz
      have hcond' := evalB_condLt (B := B) (σ := τb)
        (evalB_var (x := "dz") (by rw [hdzb]; exact hDzB)) (evalB_lit (show r + 1 < B by omega))
      rw [hdzb] at hcond'
      by_cases hler : D (τ.vars "z") ≤ r
      · -- and it is caught: the assignment is recorded if nothing has claimed it
        rw [decide_eq_true (show D (τ.vars "z") < r + 1 by omega)] at hcond'
        have hcond'' := evalB_condLt (B := B) (σ := τb)
          (evalB_get (a := "asg") (evalB_var (by rw [hzb]; exact hzB))
            (by rw [hasb, hzb, getElem?_arrOf as hz]) (by have := hasle _ hz; omega))
          (evalB_var (by rw [hnb]; exact hnB))
        rw [hnb] at hcond''
        by_cases hset : as (τ.vars "z") < n
        · -- something already claimed it: nothing happens
          rw [decide_eq_true hset] at hcond''
          refine ⟨τb, _, upd Xm (τ.vars "xp") (τ.vars "z"), as,
            Run.ite_true hcond (hs1.seq (hs2.seq (Run.ite_true hcond'
              (Run.ite_true hcond'' Run.skip)))), by simp, hnb, hcb, hzb, hdb, hasb, hxmemb,
            by omega, by omega, hkeepb, by rw [hxb]; exact hblockb,
            by rw [hxb]; exact hmonob, ?_⟩
          exact rule_extend hrule (fun _ _ _ => rfl)
            (by rw [hasz]; exact (emitCell_of_claimed (by rw [← hasz]; exact hset)).symm)
        · -- nothing had: this centre is the first catcher
          rw [decide_eq_false (by simpa using hset)] at hcond''
          have hsa : Run B (.store "asg" (.var "z") (.var "c")) τb
              (τb.setArr "asg" (τ.vars "z") c) (1 + 1 + 1) := by
            have h := Run.store (B := B) (σ := τb) (a := "asg") (i := .var "z") (e := .var "c")
              (evalB_var (by rw [hzb]; exact hzB)) (evalB_var (by rw [hcb]; exact hcB))
              (by rw [hasb, length_arrOf, hzb]; exact hz)
            rw [hzb, hcb] at h
            simpa using h
          refine ⟨τb.setArr "asg" (τ.vars "z") c, _,
            upd Xm (τ.vars "xp") (τ.vars "z"), upd as (τ.vars "z") c,
            Run.ite_true hcond (hs1.seq (hs2.seq (Run.ite_true hcond'
              (Run.ite_false hcond'' hsa)))), by simp,
            by rw [vars_setArr]; exact hnb, by rw [vars_setArr]; exact hcb,
            by rw [vars_setArr]; exact hzb,
            by rw [arrs_setArr, if_neg (by decide)]; exact hdb,
            by rw [arrs_setArr, if_pos rfl, hasb, set_arrOf_eq_upd],
            by rw [arrs_setArr, if_neg (by decide)]; exact hxmemb,
            by rw [vars_setArr]; omega, by rw [vars_setArr]; omega,
            hkeepb, by rw [vars_setArr, hxb]; exact hblockb,
            by rw [vars_setArr, hxb]; exact hmonob, ?_⟩
          refine rule_extend hrule (fun w _ hw => upd_of_ne _ hw) ?_
          rw [upd_self]
          exact (emitCell_of_first (by rw [← hasz]; exact hset) hler).symm
      · -- in the cluster but not caught: only the emission happens
        rw [decide_eq_false (by simpa using hler)] at hcond'
        refine ⟨τb, _, upd Xm (τ.vars "xp") (τ.vars "z"), as,
          Run.ite_true hcond (hs1.seq (hs2.seq (Run.ite_false hcond' Run.skip))),
          by simp, hnb, hcb, hzb, hdb, hasb, hxmemb, by omega, by omega, hkeepb,
          by rw [hxb]; exact hblockb, by rw [hxb]; exact hmonob, ?_⟩
        exact rule_extend hrule (fun _ _ _ => rfl)
          (by rw [hasz]; exact (emitCell_of_not_catch (hasg _ hz) hler).symm)
    · -- the vertex is outside the cluster: nothing happens
      rw [decide_eq_false (by simpa using hle)] at hcond
      refine ⟨τ₁, _, Xm, as, Run.ite_false hcond Run.skip, by simp, e1, e2, e3, e5, e6, e7,
        by rw [e4]; exact hxpa, by rw [e4]; omega, hkeep,
        by rw [e4]; exact block_extend_skip hblock hle, by rw [e4]; exact hmono, ?_⟩
      exact rule_extend hrule (fun _ _ _ => rfl)
        (by rw [hasz]; exact (emitCell_of_not_catch (hasg _ hz) (by omega)).symm)
  obtain ⟨τ₂, K₂, Xm', as', h2, hK₂, hnv₂, hcv₂, hzv₂, hdist₂, has₂, hxmem₂,
    hxpa₂, hxpb₂, hkeep₂, hblock₂, hmono₂, hrule₂⟩ := hmid
  -- `z := z + 1`
  have h3 : Run B (.assign "z" (.add (.var "z") (.lit 1))) τ₂
      (τ₂.setVar "z" (τ.vars "z" + 1)) (1 + (Expr.add (.var "z") (.lit 1)).size) := by
    refine Run.congr (Run.assign (evalB_bin (evalB_var (show τ₂.vars "z" < B by omega))
      (evalB_lit (show 1 < B by omega))
      (show Bop.apply .add (τ₂.vars "z") 1 < B by simp only [Bop.apply_add]; omega))) ?_
    simp only [Bop.apply_add, hzv₂]
  refine ⟨τ₂.setVar "z" (τ.vars "z" + 1), _, h1.seq (h2.seq h3), ?_, ?_, by simp⟩
  · simp only [size_get, size_var, size_lit, size_add]
    omega
  · exact ⟨Xm', as', by simpa using hnv₂, by simpa using hcv₂, by simpa using hdist₂,
      by simpa using has₂, by simpa using hxmem₂, by simp; omega,
      by simpa using hxpa₂, by simpa using hxpb₂, hkeep₂,
      by simpa using hblock₂, by simpa using hmono₂, by simpa using hrule₂⟩

/-- **The emission scan**, the kit's counted scan over the carrier with
`emitSlot_spec` as its body. -/
theorem emitLoop_spec {B n : ℕ} {D Xmem asg : ℕ → ℕ} {c xp₀ r : ℕ}
    (hc : c < n) (hnnB : n * n < B) (hrB : 2 * r + 1 < B)
    (hasg : ∀ w < n, asg w ≤ n) (hDB : ∀ w < n, D w < B) (hxp₀ : xp₀ + n ≤ n * n) :
    Spec B (fun σ => EmitInv n D Xmem asg c xp₀ r (σ.setVar "z" 0))
      (RamCover.emitLoop r)
      (fun _ σ' => EmitInv n D Xmem asg c xp₀ r σ' ∧ σ'.vars "z" = n)
      (34 * n + 6) := by
  have hnB : n < B := lt_of_le_of_lt (RamDriver.le_mul_self n) hnnB
  refine (Spec.forRangeZero "z" "n" (EmitInv n D Xmem asg c xp₀ r) n 30 hnB
    (fun _ h => by obtain ⟨-, -, -, -, -, -, -, hzle, -⟩ := h; exact hzle)
    (fun _ h => by obtain ⟨-, -, hnv, -⟩ := h; exact hnv)
    (emitSlot_spec hc hnnB hrB hasg hDB hxp₀)).mono (by omega)

/-! ### One turn of the cover pass

The walk `RamCover.Implements` asks for: the source load, the search,
the emission scan, the kill, and the two commands that close the block.
Everything the turn's postcondition *means* is `RamCover.CoverInv.step`,
which is landed; what is here is the execution between the search's
postcondition and that step's hypotheses.

The two frames the composition needs are read off the syntax: the
search writes only its own scratch, and the emission scan only the
arena and the assignment. Both lists are computed by `rfl`, since
`Com.wvars` and `Com.warrs` do not look at the expressions and so are
concrete lists even at a symbolic radius.

Since rebase P1 the search is the refinement tower's synthesized queue
BFS behind `Refine.BfsBridge.bfsQCom`, whose bridge lemma
`Refine.BfsBridge.bfsQCom_spec` is `RamBfs.bfs_spec`'s statement
verbatim but for the two extra word clauses of ledger P1/B-d. The
arrays it writes are the same two, in the same order; the scalars it
writes are the tower's own sixteen, so `bfsQCom_wvars` grows and three
of its entries — `dv1`, `v1`, `k0` — carry a digit, which
`RamDriverWrites.belowVar_notMem_wvars_coverPhase` has to be told about
(ledger P1/B-f, recorded there). -/

theorem bfsQCom_wvars (d : ℕ) : (Refine.BfsBridge.bfsQCom d).wvars =
    ["sent", "d", "one", "i", "head", "a", "tl", "v", "dv", "dv1", "k0", "v1", "kend",
      "u", "au", "du",
      "i", "a", "tl", "tl", "v", "dv", "head", "dv1", "k0", "v1", "kend", "u", "au",
      "du", "tl", "k0"] := rfl

theorem bfsQCom_warrs (d : ℕ) : (Refine.BfsBridge.bfsQCom d).warrs =
    ["dist", "dist", "q", "dist", "q"] := rfl

theorem emitLoop_wvars (r : ℕ) : (RamCover.emitLoop r).wvars = ["z", "dz", "xp", "z"] := rfl

theorem emitLoop_warrs (r : ℕ) : (RamCover.emitLoop r).warrs = ["xmem", "asg"] := rfl

/-- **One centre.** The source load, the search, the emission scan, the
kill, and the two commands that close the block. -/
theorem centreStep_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hord : OrdersBy n π ord)
    (hB : n * n + ns + 2 * r + 2 < B) :
    Spec B (fun σ => CoverState B G A₀ π ns O T ord r σ ∧ σ.vars "c" < n)
      (RamCover.centreStep r)
      (fun σ σ' => CoverState B G A₀ π ns O T ord r σ' ∧ σ'.vars "c" = σ.vars "c" + 1)
      (RamCover.centreCost n ns) := by
  have hnnB : n * n < B := by omega
  have hnB : n < B := lt_of_le_of_lt (RamDriver.le_mul_self n) hnnB
  have hnsB : ns < B := by omega
  have hrB : 2 * r + 1 < B := by omega
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨Xoff, Xmem, asg, M, hn, hoff, htgt, hordarr, halv, ⟨gd, hdist⟩, ⟨gq, hq⟩,
    hasgarr, hxoffarr, hxmemarr, halvw, hdistw, hqw, hI⟩, hc⟩ := hσ
  have hW : CoverWords B σ := ⟨halvw, hdistw, hqw⟩
  have hv : ord (σ.vars "c") < n := hord.lt hc
  have hMB : ∀ z < n, M z < B := fun z hz => lt_of_mem_words hW.1 halv hz
  have hxp₀ : σ.vars "xp" + n ≤ n * n := by
    have h₁ := hI.ptr_le
    have h₂ : (σ.vars "c" + 1) * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
    have h₃ : (σ.vars "c" + 1) * n = σ.vars "c" * n + n := by ring
    omega
  -- `src := ord[c]`
  have h1 : Run B (.assign "src" (.get "ord" (.var "c"))) σ
      (σ.setVar "src" (ord (σ.vars "c"))) (1 + (Expr.get "ord" (.var "c")).size) :=
    Run.assign (evalB_get (evalB_var (by omega))
      (by rw [hordarr, getElem?_arrOf ord hc]) (by omega))
  set σ₁ := σ.setVar "src" (ord (σ.vars "c")) with hσ₁
  -- the search
  obtain ⟨σ₂, hrun₂, ⟨D, hdistD, hDspec⟩, hfv₂, hfa₂, -, -⟩ :=
    ((Refine.BfsBridge.bfsQCom_spec (G := G) (M := M) (ns := ns) (O := O) (T := T)
      (s := ord (σ.vars "c")) (d := 2 * r) hcsr hv hnB hnsB hrB hMB).frame).run (σ := σ₁)
      ⟨by simp [hσ₁, hn], by simp [hσ₁], by simp [hσ₁, hoff], by simp [hσ₁, htgt],
        by simp [hσ₁, halv], ⟨gd, by simp [hσ₁, hdist]⟩, ⟨gq, by simp [hσ₁, hq]⟩,
        by simpa [hσ₁] using (hW.run h1).2.1, by simpa [hσ₁] using (hW.run h1).2.2⟩
  have hW₂ : CoverWords B σ₂ := (hW.run h1).run hrun₂
  have hDB : ∀ w < n, D w < B := fun w hw => lt_of_mem_words hW₂.2.1 hdistD hw
  -- what the search left where it found it
  have b1 : σ₂.vars "n" = n := by
    rw [hfv₂ "n" (by rw [bfsQCom_wvars]; decide), hσ₁]; simpa using hn
  have b2 : σ₂.vars "c" = σ.vars "c" := by
    rw [hfv₂ "c" (by rw [bfsQCom_wvars]; decide), hσ₁]; simp
  have b3 : σ₂.vars "xp" = σ.vars "xp" := by
    rw [hfv₂ "xp" (by rw [bfsQCom_wvars]; decide), hσ₁]; simp
  have b4 : σ₂.vars "src" = ord (σ.vars "c") := by
    rw [hfv₂ "src" (by rw [bfsQCom_wvars]; decide), hσ₁]; simp
  have b5 : σ₂.arrs "asg" = arrOf n asg := by
    rw [hfa₂ "asg" (by rw [bfsQCom_warrs]; decide), hσ₁]; simpa using hasgarr
  have b6 : σ₂.arrs "xmem" = arrOf (n * n) Xmem := by
    rw [hfa₂ "xmem" (by rw [bfsQCom_warrs]; decide), hσ₁]; simpa using hxmemarr
  have b7 : σ₂.arrs "alv" = arrOf n M := by
    rw [hfa₂ "alv" (by rw [bfsQCom_warrs]; decide), hσ₁]; simpa using halv
  have b8 : σ₂.arrs "off" = arrOf (n + 1) O := by
    rw [hfa₂ "off" (by rw [bfsQCom_warrs]; decide), hσ₁]; simpa using hoff
  have b9 : σ₂.arrs "tgt" = arrOf ns T := by
    rw [hfa₂ "tgt" (by rw [bfsQCom_warrs]; decide), hσ₁]; simpa using htgt
  have b10 : σ₂.arrs "ord" = arrOf n ord := by
    rw [hfa₂ "ord" (by rw [bfsQCom_warrs]; decide), hσ₁]; simpa using hordarr
  have b11 : σ₂.arrs "xoff" = arrOf (n + 1) Xoff := by
    rw [hfa₂ "xoff" (by rw [bfsQCom_warrs]; decide), hσ₁]; simpa using hxoffarr
  -- the emission scan starts against the arena the search left untouched
  have hzero : (σ₂.setVar "z" 0).vars "z" = 0 := by simp
  have hxpz : (σ₂.setVar "z" 0).vars "xp" = σ.vars "xp" := by simp [b3]
  have hpre : EmitInv n D Xmem asg (σ.vars "c") (σ.vars "xp") r (σ₂.setVar "z" 0) := by
    refine ⟨Xmem, asg, by simpa using b1, by simpa using b2, by simpa using hdistD,
      by simpa using b5, by simpa using b6, by rw [hzero]; omega,
      by rw [hxpz], by rw [hxpz, hzero]; omega, fun _ _ => rfl, fun w => ?_,
      fun p q hp hpq hq => by rw [hxpz] at hq; omega,
      fun w _ => by rw [hzero, if_neg (by omega)]⟩
    rw [hxpz, hzero]
    exact ⟨fun h => by obtain ⟨p, h₁, h₂, -⟩ := h; omega, fun h => absurd h.1 (by omega)⟩
  obtain ⟨σ₃, hrun₃, ⟨⟨Xm', as', hn₃, hc₃, hdist₃, hasg₃, hxmem₃, -, hxpa₃, hxpb₃,
      hkeep₃, hblock₃, hmono₃, hrule₃⟩, hz₃⟩, hfv₃, hfa₃, -, -⟩ :=
    ((emitLoop_spec (B := B) (n := n) (D := D) (Xmem := Xmem) (asg := asg)
      (c := σ.vars "c") (xp₀ := σ.vars "xp") (r := r) hc hnnB hrB
      (fun w hw => hI.asg_le w hw) hDB hxp₀).frame).run (σ := σ₂) hpre
  -- what the scan left where it found it
  have c1 : σ₃.vars "src" = ord (σ.vars "c") := by
    rw [hfv₃ "src" (by rw [emitLoop_wvars]; decide)]; exact b4
  have c2 : σ₃.arrs "alv" = arrOf n M := by
    rw [hfa₃ "alv" (by rw [emitLoop_warrs]; decide)]; exact b7
  have c3 : σ₃.arrs "off" = arrOf (n + 1) O := by
    rw [hfa₃ "off" (by rw [emitLoop_warrs]; decide)]; exact b8
  have c4 : σ₃.arrs "tgt" = arrOf ns T := by
    rw [hfa₃ "tgt" (by rw [emitLoop_warrs]; decide)]; exact b9
  have c5 : σ₃.arrs "ord" = arrOf n ord := by
    rw [hfa₃ "ord" (by rw [emitLoop_warrs]; decide)]; exact b10
  have c6 : σ₃.arrs "xoff" = arrOf (n + 1) Xoff := by
    rw [hfa₃ "xoff" (by rw [emitLoop_warrs]; decide)]; exact b11
  have hxpB : σ₃.vars "xp" < B := by omega
  -- the kill
  have h4 : Run B (.store "alv" (.var "src") (.lit 0)) σ₃
      (σ₃.setArr "alv" (ord (σ.vars "c")) 0) (1 + 1 + 1) := by
    have h := Run.store (B := B) (σ := σ₃) (a := "alv") (i := .var "src") (e := .lit 0)
      (evalB_var (by rw [c1]; omega)) (evalB_lit (by omega))
      (by rw [c2, length_arrOf, c1]; exact hv)
    rw [c1] at h
    simpa using h
  set σ₄ := σ₃.setArr "alv" (ord (σ.vars "c")) 0 with hσ₄
  -- the counter, and the offset that closes the block
  have h5 : Run B (.assign "c" (.add (.var "c") (.lit 1))) σ₄
      (σ₄.setVar "c" (σ.vars "c" + 1)) (1 + 3) := by
    have h := Run.assign (B := B) (σ := σ₄) (x := "c") (e := .add (.var "c") (.lit 1))
      (evalB_bin (evalB_var (show σ₄.vars "c" < B by rw [hσ₄, vars_setArr, hc₃]; omega))
        (evalB_lit (show 1 < B by omega))
        (by simp only [Bop.apply_add, hσ₄, vars_setArr, hc₃]; omega))
    rw [Bop.apply_add, hσ₄, vars_setArr, hc₃] at h
    simpa using h
  set σ₅ := σ₄.setVar "c" (σ.vars "c" + 1) with hσ₅
  have h6 : Run B (.store "xoff" (.var "c") (.var "xp")) σ₅
      (σ₅.setArr "xoff" (σ.vars "c" + 1) (σ₃.vars "xp")) (1 + 1 + 1) := by
    have h := Run.store (B := B) (σ := σ₅) (a := "xoff") (i := .var "c") (e := .var "xp")
      (evalB_var (show σ₅.vars "c" < B by rw [hσ₅, vars_setVar, if_pos rfl]; omega))
      (evalB_var (show σ₅.vars "xp" < B by
        rw [hσ₅, vars_setVar, if_neg (by decide), hσ₄, vars_setArr]; exact hxpB))
      (by rw [hσ₅, arrs_setVar, hσ₄, arrs_setArr, if_neg (by decide), c6, length_arrOf,
        vars_setVar, if_pos rfl]; omega)
    rw [show σ₅.vars "c" = σ.vars "c" + 1 by rw [hσ₅, vars_setVar, if_pos rfl],
      show σ₅.vars "xp" = σ₃.vars "xp" by
        rw [hσ₅, vars_setVar, if_neg (by decide), hσ₄, vars_setArr]] at h
    simpa using h
  set σ₆ := σ₅.setArr "xoff" (σ.vars "c" + 1) (σ₃.vars "xp") with hσ₆
  -- the mathematics of the turn, at the data the walk produced
  have hstep := RamCover.CoverInv.step (G := G) (A₀ := A₀) (π := π) (ord := ord) (r := r)
    (M := M) (c := σ.vars "c") (xp := σ.vars "xp") (Xoff := Xoff) (Xmem := Xmem)
    (asg := asg) (D := D) (Xoff' := upd Xoff (σ.vars "c" + 1) (σ₃.vars "xp"))
    (Xmem' := Xm') (asg' := as') (M' := upd M (ord (σ.vars "c")) 0)
    (xp' := σ₃.vars "xp") hord hI hc hDspec
    (fun c' hc' => upd_of_ne _ (by omega)) (upd_self _ _ _) hkeep₃
    (by rw [hz₃] at hblock₃; exact hblock₃) hxpa₃ (by rw [hz₃] at hxpb₃; exact hxpb₃)
    (inj_of_strictMono hmono₃)
    (fun w hw => by rw [hrule₃ w hw, hz₃, if_pos hw, emitCell])
    (fun u _ => upd_apply _ _ _ _)
  -- the state the turn leaves
  have hW₆ : CoverWords B σ₆ :=
    hW.run (h1.seq (hrun₂.seq (hrun₃.seq (h4.seq (h5.seq h6)))))
  refine ⟨σ₆, _, h1.seq (hrun₂.seq (hrun₃.seq (h4.seq (h5.seq h6)))), ?_, ?_, ?_⟩
  · -- the tower search's `56n + 40ns + 33` and the setup block's `32` land inside the
    -- per-centre budget the pass has always charged (ledger P1/B-e)
    simp only [size_get, size_var, RamCover.centreCost, Refine.BfsBridge.bfsQCost,
      Lax13Proofs.Refine.BfsQSynth.bfsQK]
    omega
  · refine ⟨upd Xoff (σ.vars "c" + 1) (σ₃.vars "xp"), Xm', as', upd M (ord (σ.vars "c")) 0, ?_,
      ?_, ?_, ?_, ?_, ⟨D, ?_⟩, ?_, ?_, ?_, ?_, hW₆.1, hW₆.2.1, hW₆.2.2, ?_⟩
    · rw [hσ₆, vars_setArr, hσ₅, vars_setVar, if_neg (by decide), hσ₄, vars_setArr]; exact hn₃
    · rw [hσ₆, arrs_setArr, if_neg (by decide), hσ₅, arrs_setVar, hσ₄, arrs_setArr,
        if_neg (by decide)]; exact c3
    · rw [hσ₆, arrs_setArr, if_neg (by decide), hσ₅, arrs_setVar, hσ₄, arrs_setArr,
        if_neg (by decide)]; exact c4
    · rw [hσ₆, arrs_setArr, if_neg (by decide), hσ₅, arrs_setVar, hσ₄, arrs_setArr,
        if_neg (by decide)]; exact c5
    · rw [hσ₆, arrs_setArr, if_neg (by decide), hσ₅, arrs_setVar, hσ₄, arrs_setArr,
        if_pos rfl, c2, set_arrOf_eq_upd]
    · rw [hσ₆, arrs_setArr, if_neg (by decide), hσ₅, arrs_setVar, hσ₄, arrs_setArr,
        if_neg (by decide)]; exact hdist₃
    · exact RamDriver.exists_arrOf ((RamDriver.run_length_arrs
        (h1.seq (hrun₂.seq (hrun₃.seq (h4.seq (h5.seq h6))))) "q").trans
        (by rw [hq, length_arrOf]))
    · rw [hσ₆, arrs_setArr, if_neg (by decide), hσ₅, arrs_setVar, hσ₄, arrs_setArr,
        if_neg (by decide)]; exact hasg₃
    · rw [hσ₆, arrs_setArr, if_pos rfl, hσ₅, arrs_setVar, hσ₄, arrs_setArr,
        if_neg (by decide), c6, set_arrOf_eq_upd]
    · rw [hσ₆, arrs_setArr, if_neg (by decide), hσ₅, arrs_setVar, hσ₄, arrs_setArr,
        if_neg (by decide)]; exact hxmem₃
    · rw [show σ₆.vars "c" = σ.vars "c" + 1 by
        rw [hσ₆, vars_setArr, hσ₅, vars_setVar, if_pos rfl],
        show σ₆.vars "xp" = σ₃.vars "xp" by
        rw [hσ₆, vars_setArr, hσ₅, vars_setVar, if_neg (by decide), hσ₄, vars_setArr]]
      exact hstep
  · rw [hσ₆, vars_setArr, hσ₅, vars_setVar, if_pos rfl]

/-! ### The obligation, and the repair it names

`RamCover.Implements` is exactly this walk: the three word clauses are
now conjuncts of `RamCover.CoverState` itself, and they are there
because without them the obligation is **refutable**.

The mask clause is the sharp one. Take `n = 1`, `A₀ 0 = 1`, and a mask
array holding `B` at the single vertex: every other clause of
`RamCover.CoverState` holds, since its only statement about the mask —
`RamCover.CoverInv.mask` — says which cells are *zero* and this one is
not; and the search's first read of `alv` at the source then has no
bounded evaluation, so `RamCover.centreStep` has no `Run` from that
state at all and the `Spec` is false.

The `dist` clause is a gap of a different kind. The cells really are
words — the search's fill writes `2r + 1` into all of them before the
drain starts, and the drain only lowers them — but the search's
postcondition characterizes the distance array only *below the cap*, so
a cell holding the sentinel is left unbounded and the emission scan's
`.get "dist" (.var "z")` cannot be justified. Carrying it in the
invariant is one line; the alternative — the search specification
gaining `∀ w < n, D w ≤ d + 1` — touches every caller of the search.

The `q` clause is rebase P1's (ledger P1/B-d). It is not a gap at all
but a change of accounting: the tower export's `Ir.StateBound` is
state-global, so the *entering* cells of both scratch arrays have to be
words, where the hand-walked baseline bounded only what its own run
evaluated.

No clause costs the loop anything: all three are preserved by any
bounded run (`RamDriver.run_mem_arrs_lt`), `RamCover.CoverInv.step` and
`CoverInv.out` never mention the environment, and `RamCover.cover_spec`
establishes them at entry from its own `hA` and two hypotheses on
`dist` and `q`, which every caller has — at the driver they are
`RamDriver.LevelMem`'s own conjuncts. `CoverWords` survives above only
as the shorthand this walk carries its three clauses in. -/

/-- **The single-turn walk of the cover pass, discharged**: this is
`RamCover.Implements` itself, with no clause left over. -/
theorem coverTurnImplements (B n ns : ℕ) (G : SimpleGraph (Fin n)) (A₀ O T ord : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (r : ℕ) : RamCover.Implements B n ns G A₀ O T ord π r :=
  fun hcsr hord hB _ => centreStep_spec hcsr hord hB

/-! ### The whole pass

`RamCover.cover_spec` with its `Implements` hypothesis discharged: the
fill that clears the assignments, the two commands that open the cluster
arena, and the loop over the centres against `RamCover.CoverInv`. Since
the walk of the turn is now the obligation verbatim, this is one
application. -/

/-- **The cover pass of Grohe–Kreutzer–Siebertz §6, walked.** -/
theorem coverPass_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hord : OrdersBy n π ord)
    (hB : n * n + ns + 2 * r + 2 < B) (hA : ∀ z < n, A₀ z < B) :
    Spec B (fun σ => CoverPre n ns O T A₀ ord σ ∧ (∀ v ∈ σ.arrs "dist", v < B) ∧
        (∀ v ∈ σ.arrs "q", v < B))
      (RamCover.coverCom r) (CoverPost G A₀ π ord r) (RamCover.coverCost n ns) :=
  RamCover.cover_spec (coverTurnImplements B n ns G A₀ O T ord π r) hcsr hord hB hA

/-! ### A scan against an arbitrary bound

Every flat pass of the ordering phase is `RamDriver.fillUpto` at a bound
that is *not* a scalar: `n + 1` for the three offset arrays, `m + m` for
the level's own block structure, the literal `W` for the engines'
scratch. `Spec.forRangeZero` compares two scalars and so does not
apply, and `Lax13Proofs.Reasoning.Lib.Fill.loop_spec` and
`RamDriverCluster.fill_spec` both inherit that shape.

`forRangeZero'` is the kit's counted scan with the bound left as an
expression the invariant evaluates, and `fillUpto_spec` is the array
pass on top of it. The context a pass needs — the scalars its bound and
its cell expression read, and the arrays it reads and does not write —
enters as one abstract predicate `Q` with the two closure conditions
that say what the pass writes: the counter `"i"` and the array `a`.
That is what makes one lemma serve the copies, the fills and the
re-zeroing tail alike. -/

/-- **The counted scan from zero, at an arbitrary bound.** -/
theorem forRangeZero' {B : ℕ} {c : Com} (x : String) (bnd : Expr) (I : Env → Prop) (N Kb : ℕ)
    (hB : 0 < B) (hxB : ∀ σ, I σ → σ.vars x < B) (hbnd : ∀ σ, I σ → bnd.evalB B σ = some N)
    (hxN : ∀ σ, I σ → σ.vars x ≤ N)
    (hbody : Spec B (fun σ => I σ ∧ σ.vars x < N) c
      (fun σ σ' => I σ' ∧ σ'.vars x = σ.vars x + 1) Kb) :
    Spec B (fun σ => I (σ.setVar x 0))
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) bnd) c))
      (fun _ σ' => I σ' ∧ σ'.vars x = N) ((Kb + bnd.size + 3) * N + bnd.size + 5) := by
  have hsize : (Cond.lt (Expr.var x) bnd).size = bnd.size + 2 := by
    simp only [Cond.size, size_var]; omega
  have hloop : Spec B I (.while (.lt (.var x) bnd) c)
      (fun _ σ' => I σ' ∧ (Cond.lt (Expr.var x) bnd).evalB B σ' = some false)
      ((Kb + bnd.size + 3) * N + bnd.size + 3) := by
    refine Spec.while_potential I (fun σ => (Kb + bnd.size + 3) * (N - σ.vars x))
      (fun σ hI => ⟨_, evalB_condLt (evalB_var (hxB σ hI)) (hbnd σ hI)⟩) ?_ (fun _ h => h) ?_
    · intro σ hI hv
      have hlt : σ.vars x < N := by
        rw [evalB_condLt (evalB_var (hxB σ hI)) (hbnd σ hI)] at hv
        simpa using hv
      obtain ⟨σ', hr, hI', hx'⟩ := hbody σ ⟨hI, hlt⟩
      refine ⟨σ', Kb, hr, hI', ?_⟩
      show 1 + (Cond.lt (Expr.var x) bnd).size + Kb + (Kb + bnd.size + 3) * (N - σ'.vars x)
        ≤ (Kb + bnd.size + 3) * (N - σ.vars x)
      rw [hsize]
      have hdrop : N - σ'.vars x + 1 = N - σ.vars x := by rw [hx']; omega
      refine le_of_eq ?_
      rw [← hdrop]
      ring
    · intro σ hI
      show (Kb + bnd.size + 3) * (N - σ.vars x) + 1 + (Cond.lt (Expr.var x) bnd).size
        ≤ (Kb + bnd.size + 3) * N + bnd.size + 3
      rw [hsize]
      have : (Kb + bnd.size + 3) * (N - σ.vars x) ≤ (Kb + bnd.size + 3) * N :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      omega
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨σ', hr, hI', hfalse⟩ := hloop.run (σ := σ.setVar x 0) hσ
  refine ⟨σ', _, Run.seq (Run.assign (v := 0) (evalB_lit hB)) hr, ?_, hI', ?_⟩
  · simp only [size_lit]; omega
  · rw [evalB_condLt (evalB_var (hxB σ' hI')) (hbnd σ' hI')] at hfalse
    have := hxN σ' hI'
    simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hfalse
    omega

/-- **A flat pass over a prefix of an array, at an arbitrary bound.**
`Q` is the context the pass runs in: the scalars its bound and its cell
expression read, and the arrays it reads. The two closure conditions
are exactly what the pass writes — the counter and the array — so a
caller instantiates `Q` with its own frozen surface and owes nothing
else. -/
theorem fillUpto_spec {B : ℕ} (N : ℕ) (a : String) (bnd e : Expr) (F : ℕ → ℕ)
    (Q : Env → Prop) (hB : 0 < B) (hNB : N < B)
    (hQfr : ∀ σ σ', Q σ → (∀ y, y ≠ "i" → σ'.vars y = σ.vars y) →
      (∀ b, b ≠ a → σ'.arrs b = σ.arrs b) → Q σ')
    (hbnd : ∀ σ, Q σ → bnd.evalB B σ = some N)
    (he : ∀ σ, Q σ → (σ.arrs a).length = N → σ.vars "i" < N →
      e.evalB B σ = some (F (σ.vars "i"))) :
    Spec B (fun σ => (∃ g, σ.arrs a = arrOf N g) ∧ Q σ)
      (RamDriver.fillUpto a bnd e)
      (fun _ σ' => (∃ g, σ'.arrs a = arrOf N g ∧ ∀ j < N, g j = F j) ∧ σ'.vars "i" = N ∧ Q σ')
      ((e.size + bnd.size + 9) * N + bnd.size + 5) := by
  have hbody : Spec B (fun σ => (Fill.Below a "i" N F σ ∧ Q σ) ∧ σ.vars "i" < N)
      (Fill.put a "i" e)
      (fun σ σ' => (Fill.Below a "i" N F σ' ∧ Q σ') ∧ σ'.vars "i" = σ.vars "i" + 1)
      (6 + e.size) :=
    ((Fill.put_spec B N a "i" e F _ (fun _ hσ => ⟨hσ.1.1, hσ.2⟩) hNB
      (fun σ hσ => he σ hσ.1.2 hσ.1.1.length hσ.2)).frame).post
      (fun σ σ' hσ hq => ⟨⟨hq.1.1,
        hQfr σ σ' hσ.1.2 (fun y hy => hq.2.1 y (by simp [hy]))
          (fun b hb => hq.2.2.1 b (by simp [hb]))⟩, hq.1.2⟩)
  refine (((forRangeZero' "i" bnd (fun σ => Fill.Below a "i" N F σ ∧ Q σ) N (6 + e.size) hB
    (fun _ hσ => lt_of_le_of_lt hσ.1.le hNB) (fun _ hσ => hbnd _ hσ.2)
    (fun _ hσ => hσ.1.le) hbody).pre ?_).post ?_).mono (le_of_eq (by ring))
  · rintro σ ⟨⟨g, harr⟩, hQ⟩
    exact ⟨Fill.below_zero (by rw [arrs_setVar]; exact harr) (by simp),
      hQfr σ (σ.setVar "i" 0) hQ (fun y hy => by simp [hy]) (fun _ _ => rfl)⟩
  · exact fun _ σ' _ hq => ⟨hq.1.1.done hq.2, hq.2, hq.1.2⟩

/-- **A copy of a prefix of one array into another**, the shape
`RamDriver.saveCsr`, `RamDriver.restoreCsr` and the two copies of
`RamDriver.augRelinkCom` all have. -/
theorem copyUpto_spec {B : ℕ} (N Ns : ℕ) (src dst : String) (bnd : Expr) (g : ℕ → ℕ)
    (Q : Env → Prop) (hB : 0 < B) (hNB : N < B) (hNs : N ≤ Ns)
    (hQfr : ∀ σ σ', Q σ → (∀ y, y ≠ "i" → σ'.vars y = σ.vars y) →
      (∀ b, b ≠ dst → σ'.arrs b = σ.arrs b) → Q σ')
    (hbnd : ∀ σ, Q σ → bnd.evalB B σ = some N)
    (hsrc : ∀ σ, Q σ → σ.arrs src = arrOf Ns g) (hgB : ∀ k < N, g k < B) :
    Spec B (fun σ => (∃ h, σ.arrs dst = arrOf N h) ∧ Q σ)
      (RamDriver.copyUpto src dst bnd)
      (fun _ σ' => (∃ h, σ'.arrs dst = arrOf N h ∧ ∀ j < N, h j = g j) ∧
        σ'.vars "i" = N ∧ Q σ')
      ((bnd.size + 11) * N + bnd.size + 5) :=
  (fillUpto_spec N dst bnd (.get src (.var "i")) g Q hB hNB hQfr hbnd
    (fun σ hQ _ hlt => evalB_get (evalB_var (by omega))
      (by rw [hsrc σ hQ, getElem?_arrOf g (by omega)]) (hgB _ hlt))).mono
    (le_of_eq (by simp only [size_get, size_var]; ring))

/-- Two arrays that agree below their common length are the same
array. -/
theorem arrOf_congr {N : ℕ} {f g : ℕ → ℕ} (h : ∀ k < N, f k = g k) : arrOf N f = arrOf N g :=
  List.map_congr_left fun k hk => h k (List.mem_range.1 hk)

/-! ### The rank inversion

The last mathematical step of the ordering phase. The elimination
engine leaves a rank array — an injection of the carrier into its own
positions — and `RamDriver.ordCom` writes its inverse into `ord`, which
is what `RamCover.OrdersBy` is. The only content beyond the walk is
that an injection of a finite range into itself is onto, which is what
turns "every vertex has a position" into "every position has a
vertex". -/

/-- **An injection of an initial segment into itself is onto.** -/
theorem exists_preimage_of_inj {n : ℕ} {R : ℕ → ℕ} (hR : ∀ v < n, R v < n)
    (hinj : ∀ v < n, ∀ w < n, R v = R w → v = w) {c : ℕ} (hc : c < n) : ∃ v < n, R v = c := by
  have hsub : (Finset.range n).image R ⊆ Finset.range n := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_range.2 (hR v (Finset.mem_range.1 hv))
  have hcard : ((Finset.range n).image R).card = n := by
    rw [Finset.card_image_of_injOn (fun v hv w hw h =>
      hinj v (by simpa using hv) w (by simpa using hw) h), Finset.card_range]
  have himg : (Finset.range n).image R = Finset.range n :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
  have hmem : c ∈ (Finset.range n).image R := by rw [himg]; exact Finset.mem_range.2 hc
  obtain ⟨v, hv, hvc⟩ := Finset.mem_image.1 hmem
  exact ⟨v, Finset.mem_range.1 hv, hvc⟩

/-- **`RamDriver.ordCom` inverts the rank array into an ordering.** -/
theorem ordCom_spec {B n : ℕ} {R : ℕ → ℕ} (dst : String) (hdr : dst ≠ "rnk")
    (hnB : n < B) (hR : ∀ v < n, R v < n)
    (hinj : ∀ v < n, ∀ w < n, R v = R w → v = w) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.arrs "rnk" = arrOf n R ∧ (∃ g, σ.arrs dst = arrOf n g))
      (RamDriver.ordCom dst)
      (fun _ σ' => σ'.vars "n" = n ∧ σ'.arrs "rnk" = arrOf n R ∧
        ∃ (π : Equiv.Perm (Fin n)) (ordv : ℕ → ℕ),
          σ'.arrs dst = arrOf n ordv ∧ OrdersBy n π ordv)
      (12 * n + 6) := by
  -- the invariant: the positions below the counter have been inverted
  have hbody : Spec B
      (fun σ => (∃ g, σ.vars "n" = n ∧ σ.arrs "rnk" = arrOf n R ∧ σ.arrs dst = arrOf n g ∧
        σ.vars "z" ≤ n ∧ ∀ v < σ.vars "z", g (R v) = v) ∧ σ.vars "z" < n)
      (.seq (.store dst (.get "rnk" (.var "z")) (.var "z"))
        (.assign "z" (.add (.var "z") (.lit 1))))
      (fun σ σ' => (∃ g, σ'.vars "n" = n ∧ σ'.arrs "rnk" = arrOf n R ∧
        σ'.arrs dst = arrOf n g ∧ σ'.vars "z" ≤ n ∧ ∀ v < σ'.vars "z", g (R v) = v) ∧
        σ'.vars "z" = σ.vars "z" + 1) 8 := by
    refine Spec.of_exists fun σ hσ => ?_
    obtain ⟨⟨g, hn, hrnk, hordv, -, hinvv⟩, hz⟩ := hσ
    have hRz : R (σ.vars "z") < n := hR _ hz
    have h1 : Run B (.store dst (.get "rnk" (.var "z")) (.var "z")) σ
        (σ.setArr dst (R (σ.vars "z")) (σ.vars "z")) (1 + 2 + 1) := by
      have h := Run.store (B := B) (σ := σ) (a := dst) (i := .get "rnk" (.var "z"))
        (e := .var "z")
        (evalB_get (evalB_var (by omega)) (by rw [hrnk, getElem?_arrOf R hz]) (by omega))
        (evalB_var (by omega)) (by rw [hordv, length_arrOf]; exact hRz)
      simpa using h
    have h2 : Run B (.assign "z" (.add (.var "z") (.lit 1)))
        (σ.setArr dst (R (σ.vars "z")) (σ.vars "z"))
        ((σ.setArr dst (R (σ.vars "z")) (σ.vars "z")).setVar "z" (σ.vars "z" + 1)) (1 + 3) := by
      have h := Run.assign (B := B) (σ := σ.setArr dst (R (σ.vars "z")) (σ.vars "z"))
        (x := "z") (e := .add (.var "z") (.lit 1))
        (evalB_bin (evalB_var (by rw [vars_setArr]; omega)) (evalB_lit (by omega))
          (by simp only [Bop.apply_add, vars_setArr]; omega))
      rw [Bop.apply_add, vars_setArr] at h
      simpa using h
    refine ⟨_, _, h1.seq h2, by omega,
      ⟨upd g (R (σ.vars "z")) (σ.vars "z"), by simp [hn],
        by rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdr)]; exact hrnk, ?_, by simp; omega,
        ?_⟩, by simp⟩
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, hordv, set_arrOf_eq_upd]
    · intro v hv
      rw [vars_setVar, if_pos rfl] at hv
      rcases Nat.lt_or_ge v (σ.vars "z") with hlt | hge
      · rw [upd_of_ne _ (fun hc => absurd (hinj v (by omega) _ hz hc) (by omega))]
        exact hinvv v hlt
      · have : v = σ.vars "z" := by omega
        rw [this, upd_self]
  refine ((Spec.forRangeZero (B := B) "z" "n"
    (fun σ => ∃ g, σ.vars "n" = n ∧ σ.arrs "rnk" = arrOf n R ∧ σ.arrs dst = arrOf n g ∧
      σ.vars "z" ≤ n ∧ ∀ v < σ.vars "z", g (R v) = v) n 8 hnB
    (fun _ h => by obtain ⟨-, -, -, -, hzz, -⟩ := h; exact hzz)
    (fun _ h => by obtain ⟨-, hnn, -⟩ := h; exact hnn) hbody).pre ?_).post ?_
  · rintro σ ⟨hn, hrnk, ⟨g, hordv⟩⟩
    exact ⟨g, by simp [hn], by simp [hrnk], by simp [hordv], by simp,
      fun v hv => absurd hv (by simp)⟩
  · rintro σ σ' - ⟨⟨g, hn, hrnk, hordv, -, hinvv⟩, hzn⟩
    rw [hzn] at hinvv
    have hordlt : ∀ c < n, g c < n := by
      intro c hc
      obtain ⟨v, hv, rfl⟩ := exists_preimage_of_inj hR hinj hc
      rw [hinvv v hv]; exact hv
    have hRo : ∀ c < n, R (g c) = c := by
      intro c hc
      obtain ⟨v, hv, rfl⟩ := exists_preimage_of_inj hR hinj hc
      rw [hinvv v hv]
    exact ⟨hn, hrnk, RamCover.rankPerm n R g hR hordlt hRo hinvv, g, hordv,
      RamCover.ordersBy_rankPerm n R g hR hordlt hRo hinvv⟩

/-! ### The block structure, out of the way and back

`RamDriver.saveCsr` and `RamDriver.restoreCsr` are the same two copies
in the two directions, so one lemma serves both. The second copy's
bound is the *runtime* number `m + m`, which is why
`RamDriver.LevelPre` carries `σ.vars "m" + σ.vars "m" = ns` and why
`forRangeZero'` had to take its bound as an expression. -/

/-- **A block structure copied wholesale.** -/
theorem csrCopy_spec {B n ns : ℕ} {O T : ℕ → ℕ} (s₁ s₂ d₁ d₂ : String)
    (e₁ : s₁ ≠ d₁) (e₂ : s₂ ≠ d₁) (e₃ : s₂ ≠ d₂) (e₄ : s₁ ≠ d₂) (e₅ : d₁ ≠ d₂)
    (hnB : n + 1 < B) (hnsB : ns < B)
    (hOB : ∀ k < n + 1, O k < B) (hTB : ∀ k < ns, T k < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.vars "m" + σ.vars "m" = ns ∧
        σ.arrs s₁ = arrOf (n + 1) O ∧ σ.arrs s₂ = arrOf ns T ∧
        (∃ g, σ.arrs d₁ = arrOf (n + 1) g) ∧ (∃ g, σ.arrs d₂ = arrOf ns g))
      (.seq (RamDriver.copyUpto s₁ d₁ (.add (.var "n") (.lit 1)))
        (RamDriver.copyUpto s₂ d₂ (.add (.var "m") (.var "m"))))
      (fun σ σ' => σ'.vars "n" = n ∧ σ'.vars "m" = σ.vars "m" ∧
        σ'.arrs s₁ = arrOf (n + 1) O ∧ σ'.arrs s₂ = arrOf ns T ∧
        σ'.arrs d₁ = arrOf (n + 1) O ∧ σ'.arrs d₂ = arrOf ns T)
      (14 * (n + 1) + 14 * ns + 16) := by
  have hB : 0 < B := by omega
  -- the two contexts: what each copy reads and does not write
  have spec1 := copyUpto_spec (B := B) (n + 1) (n + 1) s₁ d₁ (.add (.var "n") (.lit 1)) O
    (fun σ => σ.vars "n" = n ∧ σ.vars "m" + σ.vars "m" = ns ∧
      σ.arrs s₁ = arrOf (n + 1) O ∧ σ.arrs s₂ = arrOf ns T ∧ (∃ g, σ.arrs d₂ = arrOf ns g))
    hB hnB le_rfl
    (fun σ σ' hQ hv ha => ⟨by rw [hv "n" (by decide)]; exact hQ.1,
      by rw [hv "m" (by decide)]; exact hQ.2.1, by rw [ha s₁ e₁]; exact hQ.2.2.1,
      by rw [ha s₂ e₂]; exact hQ.2.2.2.1, by rw [ha d₂ (Ne.symm e₅)]; exact hQ.2.2.2.2⟩)
    (fun σ hQ => by
      have h := evalB_bin (B := B) (σ := σ) (op := .add) (e := .var "n") (f := .lit 1)
        (evalB_var (show σ.vars "n" < B by rw [hQ.1]; omega))
        (evalB_lit (show 1 < B by omega))
        (show Bop.apply .add (σ.vars "n") 1 < B by simp only [Bop.apply_add, hQ.1]; omega)
      rw [Bop.apply_add, hQ.1] at h
      exact h)
    (fun σ hQ => hQ.2.2.1) hOB
  have spec2 := copyUpto_spec (B := B) ns ns s₂ d₂ (.add (.var "m") (.var "m")) T
    (fun σ => σ.vars "n" = n ∧ σ.vars "m" + σ.vars "m" = ns ∧
      σ.arrs s₁ = arrOf (n + 1) O ∧ σ.arrs s₂ = arrOf ns T ∧ σ.arrs d₁ = arrOf (n + 1) O)
    hB hnsB le_rfl
    (fun σ σ' hQ hv ha => ⟨by rw [hv "n" (by decide)]; exact hQ.1,
      by rw [hv "m" (by decide)]; exact hQ.2.1, by rw [ha s₁ e₄]; exact hQ.2.2.1,
      by rw [ha s₂ e₃]; exact hQ.2.2.2.1, by rw [ha d₁ e₅]; exact hQ.2.2.2.2⟩)
    (fun σ hQ => by
      have hm : σ.vars "m" < B := by have := hQ.2.1; omega
      have h := evalB_bin (B := B) (σ := σ) (op := .add) (e := .var "m") (f := .var "m")
        (evalB_var hm) (evalB_var hm)
        (show Bop.apply .add (σ.vars "m") (σ.vars "m") < B by
          simp only [Bop.apply_add]; have := hQ.2.1; omega)
      rw [Bop.apply_add, hQ.2.1] at h
      exact h)
    (fun σ hQ => hQ.2.2.2.1) hTB
  refine (Spec.seq (spec1.pre (fun σ hσ =>
      ⟨hσ.2.2.2.2.1, hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2.2⟩)) spec2
    ?hmid ?hpost).mono ?hcost
  case hmid =>
    rintro σ σ' - ⟨⟨h, hd₁, hagr⟩, -, hn', hm', hs₁', hs₂', hd₂'⟩
    exact ⟨hd₂', hn', hm', hs₁', hs₂', by rw [hd₁, arrOf_congr hagr]⟩
  case hpost =>
    rintro σ σ' σ'' ⟨-, hm, -, -, -, -⟩ - ⟨⟨h', hd₂, hagr'⟩, -, hn'', hm'', hs₁'', hs₂'', hd₁''⟩
    exact ⟨hn'', by omega, hs₁'', hs₂'', hd₁'', by rw [hd₂, arrOf_congr hagr']⟩
  case hcost =>
    simp only [size_add, size_var, size_lit]
    omega

/-- `RamDriver.saveCsr`, walked. -/
theorem saveCsr_spec {B n ns : ℕ} {O T : ℕ → ℕ} (hnB : n + 1 < B) (hnsB : ns < B)
    (hOB : ∀ k < n + 1, O k < B) (hTB : ∀ k < ns, T k < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.vars "m" + σ.vars "m" = ns ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
        (∃ g, σ.arrs "gof" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "gtg" = arrOf ns g))
      RamDriver.saveCsr
      (fun σ σ' => σ'.vars "n" = n ∧ σ'.vars "m" = σ.vars "m" ∧
        σ'.arrs "off" = arrOf (n + 1) O ∧ σ'.arrs "tgt" = arrOf ns T ∧
        σ'.arrs "gof" = arrOf (n + 1) O ∧ σ'.arrs "gtg" = arrOf ns T)
      (14 * (n + 1) + 14 * ns + 16) :=
  csrCopy_spec "off" "tgt" "gof" "gtg" (by decide) (by decide) (by decide) (by decide)
    (by decide) hnB hnsB hOB hTB

/-- `RamDriver.restoreCsr`, walked. -/
theorem restoreCsr_spec {B n ns : ℕ} {O T : ℕ → ℕ} (hnB : n + 1 < B) (hnsB : ns < B)
    (hOB : ∀ k < n + 1, O k < B) (hTB : ∀ k < ns, T k < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.vars "m" + σ.vars "m" = ns ∧
        σ.arrs "gof" = arrOf (n + 1) O ∧ σ.arrs "gtg" = arrOf ns T ∧
        (∃ g, σ.arrs "off" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "tgt" = arrOf ns g))
      RamDriver.restoreCsr
      (fun σ σ' => σ'.vars "n" = n ∧ σ'.vars "m" = σ.vars "m" ∧
        σ'.arrs "gof" = arrOf (n + 1) O ∧ σ'.arrs "gtg" = arrOf ns T ∧
        σ'.arrs "off" = arrOf (n + 1) O ∧ σ'.arrs "tgt" = arrOf ns T)
      (14 * (n + 1) + 14 * ns + 16) :=
  csrCopy_spec "gof" "gtg" "off" "tgt" (by decide) (by decide) (by decide) (by decide)
    (by decide) hnB hnsB hOB hTB

/-! ### What is left of the two large walks

The cover pass is complete: `coverTurnImplements` is
`RamCover.Implements` — with the word clauses of `CoverWords`, which
that obligation must gain before it is true at all — and
`coverPass_spec` is `RamCover.cover_spec`'s conclusion with no
hypothesis about the walk left in it.

`Lax3Proofs.RamAugment.Implements` and
`Lax3Proofs.RamDriver.OrderImplements` are the two that are not, and
this file's remaining contribution to them is the flat-pass kit above.
The frontier, pass by pass.

**The round** (`RamAugment.Implements`). Ten passes and one call, of
which the three counting sorts (`outPass`, the prefix sums of
`fratPass` and of `asmPass`) are `forRangeZero'` at a bound that is a
block offset rather than a length, and the four stamped enumerations
(`fratCount`, `fratFill`, `asmRow` twice) are two nested
`Csr.scan`s whose content is that a stamped walk emits each member of
its set exactly once. That last is the file's only genuinely new
mathematics, and `RamAugment.inN_augOr_eq` and
`RamAugment.card_inN_augOr` are what it has to land on; everything else
in `RamAugment` — the arc rule, the assembly identity, the degree
budget — is proved there already. `RamAugment.ElimAvail` closes the one
call outright, at `ns = fratSlots D`, since wave A2's width threading
made `RamElim.ElimPre`'s scratch width a caller's choice.

**The phase** (`RamDriver.OrderImplements`). Seven phases, of which
three are now walked here: `RamDriver.saveCsr` and
`RamDriver.restoreCsr` are `saveCsr_spec`/`restoreCsr_spec`, and the
rank inversion is `ordCom_spec` — which is the only part of the phase
carrying mathematics, and it is the whole of what the postcondition
asks for, since that postcondition names no ordering in particular.
What is left is bookkeeping of one shape: `RamDriver.augRelinkCom`'s
two copies and seven fills, `RamDriver.orderZeroCom`'s eight fills, and
the mask fill before the second elimination are all `fillUpto_spec` and
`copyUpto_spec` at the contexts `RamDriver.OrderMem` provides; the two
`RamElim.elimCom` calls are `RamDriver.ElimAvail`; and the `R` rounds
are `RamDriver.AugAvail` under `foldRange`, collected by
`RamAugment.isAugChain_succ`. The cost `K` is a parameter of the
obligation and is the wave that computes the cover's degree, not this
one.

**The cover phase** (`RamDriver.CoverImplements`). Its surface gap is
repaired — it now takes `RamBfs.CsrGraph G ns O T`, without which its
postcondition spoke about a graph the program had never been told about
and any `G` disagreeing with `O`/`T` refuted it — but the obligation is
no longer one application of `coverPass_spec`, because the phase is no
longer one call. `RamDriver.coverPhase` is the depth's ordering into
`ord`, the depth's mask into `alv`, the pass, and the four copies of
`RamDriver.coverSave` that make the answers the depth's own; the middle
one is `coverPass_spec` (`RamDriver.LevelPre` supplies the mask bound
and `RamDriver.LevelMem` the `dist` and `q` bounds), and the six around it are
`copyUpto_spec` and `copyCom_spec` at contexts `LevelMem` and
`RamDriver.DepthMem` provide. -/

end Lax3Proofs.RamDriverOrder
