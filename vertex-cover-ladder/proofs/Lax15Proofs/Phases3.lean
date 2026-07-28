import Lax15Proofs.Phases
import Lax15Proofs.Program3
import Lax15Proofs.Solver

/-!
The second rung's inner loops, run.

Two blocks of `Program3.lean` are new, and this file runs them both.

The **descend scan** is rung A's pass with the branching threshold
raised: instead of a first unmarked target and a flag on a second
different one, the per-owner registers hold the first *two* distinct
unmarked targets, `t1` and `t2`, and the flag goes up on a third. The
proof is `Phases.lean`'s `descendScan_run` line for line, with three
simplifications and one complication. Gone are `ro` and `cnted`: this
rung counts nothing, so the whole residual-owner half of rung A's
invariant disappears. What replaces it is `SeenInv`, which says that
the registers describe the block of the current owner exactly — every
unmarked target below the pointer is `t1` or `t2`, and each register
that is live is witnessed by a slot that named it. Three distinct
targets then follow from `SeenInv` together with the slot at hand, and
`three_le_resDeg_of_slots` turns them into the residual degree the
push spends budget on.

`SeenInv` is carried **only while the flag is down**. It cannot survive
the slot that raises the flag — that slot's target is by construction a
third value, outside `{t1, t2}` — and it is not wanted afterwards: once
the flag is up the scan's conclusion is the witness it already has, and
`recordFound` keeps the first one.

The verdict is the dichotomy of rung A at one threshold up: either the
flag is down and no unmarked block names three different unmarked
targets — `ThinBlocks3`, which `Solver.lean` turns into "every residual
degree is at most two", the solver's hypothesis — or the flag is up and
`v` names a vertex of residual degree at least three.
-/

namespace Lax15Proofs.VC3

open Lax13.Ram Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax11Proofs.CC
open Lax15Proofs.VC

variable {g : List ℕ} {n m B : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
  {M : Finset (Fin n)}

/-! ### Two combinators, run

`neTest` is the machine's disequality: two strict comparisons, so the
guarded command appears twice and a run of it has to pick the branch by
trichotomy. -/

/-- A disequality test that holds runs its command. -/
theorem neTest_ne {t : String} {c : Com} {ρ ρ' : Env} {K : ℕ} (hwB : ρ.vars "w" < B)
    (htB : ρ.vars t < B) (hne : ρ.vars "w" ≠ ρ.vars t) (h : Run B c ρ ρ' K) :
    Run B (neTest t c) ρ ρ' (K + 10) := by
  rcases Nat.lt_or_ge (ρ.vars "w") (ρ.vars t) with hlt | hge
  · exact (Run.ite_true ((evalB_condLt (evalB_var hwB) (evalB_var htB)).trans
      (by simp [hlt])) h).mono (by simp; omega)
  · have hlt : ρ.vars t < ρ.vars "w" := by omega
    exact (Run.ite_false ((evalB_condLt (evalB_var hwB) (evalB_var htB)).trans
        (by simp; omega))
      (Run.ite_true ((evalB_condLt (evalB_var htB) (evalB_var hwB)).trans
        (by simp [hlt])) h)).mono (by simp; omega)

/-- A disequality test that fails does nothing at all. -/
theorem neTest_eq {t : String} {c : Com} {ρ : Env} (hwB : ρ.vars "w" < B)
    (htB : ρ.vars t < B) (heq : ρ.vars "w" = ρ.vars t) : Run B (neTest t c) ρ ρ 10 :=
  (Run.ite_false ((evalB_condLt (evalB_var hwB) (evalB_var htB)).trans (by simp [heq]))
    (Run.ite_false ((evalB_condLt (evalB_var htB) (evalB_var hwB)).trans
      (by simp [heq])) Run.skip)).mono (by simp)

/-- **The dedup, with the descend scan's actions.** The first two
distinct unmarked targets of a block are recorded; a third raises the
flag, which keeps the witness it already has. Nothing but the five
registers moves. -/
theorem dedupFound_run {ρ : Env} (h1B : 1 < B) (h2B : 2 < B) (hsB : ρ.vars "seen" < B)
    (ht1B : ρ.vars "t1" < B) (ht2B : ρ.vars "t2" < B) (hwB : ρ.vars "w" < B)
    (hfB : ρ.vars "found" < B) (hf01 : ρ.vars "found" ≤ 1) (hs2 : ρ.vars "seen" ≤ 2)
    (huB : ρ.vars "u" < B) :
    ∃ ρ' K, Run B (dedupStep .skip .skip VC.recordFound) ρ ρ' K ∧ K ≤ 60 ∧
      ρ'.arrs = ρ.arrs ∧ ρ'.inp = ρ.inp ∧ ρ'.out = ρ.out ∧
      (∀ y, y ≠ "seen" → y ≠ "t1" → y ≠ "t2" → y ≠ "found" → y ≠ "v" →
        ρ'.vars y = ρ.vars y) ∧
      ((ρ.vars "seen" = 0 ∧ ρ'.vars "seen" = 1 ∧ ρ'.vars "t1" = ρ.vars "w" ∧
          ρ'.vars "t2" = ρ.vars "t2" ∧ ρ'.vars "found" = ρ.vars "found" ∧
          ρ'.vars "v" = ρ.vars "v") ∨
       (ρ.vars "seen" ≠ 0 ∧
          (ρ.vars "w" = ρ.vars "t1" ∨ (ρ.vars "seen" = 2 ∧ ρ.vars "w" = ρ.vars "t2")) ∧
          ρ'.vars "seen" = ρ.vars "seen" ∧ ρ'.vars "t1" = ρ.vars "t1" ∧
          ρ'.vars "t2" = ρ.vars "t2" ∧ ρ'.vars "found" = ρ.vars "found" ∧
          ρ'.vars "v" = ρ.vars "v") ∨
       (ρ.vars "seen" = 1 ∧ ρ.vars "w" ≠ ρ.vars "t1" ∧ ρ'.vars "seen" = 2 ∧
          ρ'.vars "t1" = ρ.vars "t1" ∧ ρ'.vars "t2" = ρ.vars "w" ∧
          ρ'.vars "found" = ρ.vars "found" ∧ ρ'.vars "v" = ρ.vars "v") ∨
       (ρ.vars "seen" ≠ 0 ∧ ρ.vars "seen" ≠ 1 ∧ ρ.vars "w" ≠ ρ.vars "t1" ∧
          ρ.vars "w" ≠ ρ.vars "t2" ∧ ρ'.vars "seen" = ρ.vars "seen" ∧
          ρ'.vars "t1" = ρ.vars "t1" ∧ ρ'.vars "t2" = ρ.vars "t2" ∧
          ρ'.vars "found" = 1 ∧
          ((ρ.vars "found" = 0 ∧ ρ'.vars "v" = ρ.vars "u") ∨
            (ρ.vars "found" = 1 ∧ ρ'.vars "v" = ρ.vars "v")))) := by
  by_cases hs0 : ρ.vars "seen" = 0
  · -- the block's first unmarked target
    refine ⟨(ρ.setVar "seen" 1).setVar "t1" (ρ.vars "w"), 60,
      (Run.ite_true ((evalB_condEq (evalB_var hsB) (evalB_lit (by omega))).trans
          (by simp [hs0]))
        (Run.seq (Run.assign (v := 1) (by simp; omega))
          (Run.seq (Run.assign (v := ρ.vars "w") (by simp; omega)) Run.skip))).mono
        (by simp),
      le_rfl, by simp, by simp, by simp, ?_,
      Or.inl ⟨hs0, by simp, by simp, by simp, by simp, by simp⟩⟩
    intro y h1 h2 _ _ _
    simp [h1, h2]
  · -- the block has a first target already
    by_cases hwt1 : ρ.vars "w" = ρ.vars "t1"
    · exact ⟨ρ, 60, (Run.ite_false ((evalB_condEq (evalB_var hsB)
          (evalB_lit (by omega))).trans (by simp [hs0]))
          (neTest_eq hwB ht1B hwt1)).mono (by simp), le_rfl, rfl, rfl, rfl,
        fun y _ _ _ _ _ => rfl,
        Or.inr (Or.inl ⟨hs0, Or.inl hwt1, rfl, rfl, rfl, rfl, rfl⟩)⟩
    · by_cases hs1 : ρ.vars "seen" = 1
      · -- the block's second distinct unmarked target
        refine ⟨(ρ.setVar "seen" 2).setVar "t2" (ρ.vars "w"), 60,
          (Run.ite_false ((evalB_condEq (evalB_var hsB) (evalB_lit (by omega))).trans
              (by simp [hs0]))
            (neTest_ne hwB ht1B hwt1
              (Run.ite_true ((evalB_condEq (evalB_var hsB) (evalB_lit (by omega))).trans
                  (by simp [hs1]))
                (Run.seq (Run.assign (v := 2) (by simp; omega))
                  (Run.seq (Run.assign (v := ρ.vars "w") (by simp; omega))
                    Run.skip))))).mono (by simp),
          le_rfl, by simp, by simp, by simp, ?_,
          Or.inr (Or.inr (Or.inl ⟨hs1, hwt1, by simp, by simp, by simp, by simp, by simp⟩))⟩
        intro y h1 _ h3 _ _
        simp [h1, h3]
      · by_cases hwt2 : ρ.vars "w" = ρ.vars "t2"
        · refine ⟨ρ, 60, (Run.ite_false ((evalB_condEq (evalB_var hsB)
              (evalB_lit (by omega))).trans (by simp [hs0]))
              (neTest_ne hwB ht1B hwt1
                (Run.ite_false ((evalB_condEq (evalB_var hsB)
                    (evalB_lit (by omega))).trans (by simp [hs1]))
                  (neTest_eq hwB ht2B hwt2)))).mono (by simp),
            le_rfl, rfl, rfl, rfl, fun y _ _ _ _ _ => rfl, Or.inr (Or.inl ?_)⟩
          exact ⟨hs0, Or.inr ⟨by omega, hwt2⟩, rfl, rfl, rfl, rfl, rfl⟩
        · -- a third distinct unmarked target: the flag goes up
          have hrec : ∃ σ' K, Run B VC.recordFound ρ σ' K ∧ K ≤ 15 ∧ σ'.arrs = ρ.arrs ∧
              σ'.inp = ρ.inp ∧ σ'.out = ρ.out ∧
              (∀ y, y ≠ "found" → y ≠ "v" → σ'.vars y = ρ.vars y) ∧
              σ'.vars "found" = 1 ∧
              ((ρ.vars "found" = 0 ∧ σ'.vars "v" = ρ.vars "u") ∨
                (ρ.vars "found" = 1 ∧ σ'.vars "v" = ρ.vars "v")) := by
            by_cases hf0 : ρ.vars "found" = 0
            · refine ⟨(ρ.setVar "found" 1).setVar "v" (ρ.vars "u"), 15,
                (Run.ite_true ((evalB_condEq (evalB_var hfB) (evalB_lit (by omega))).trans
                    (by simp [hf0]))
                  (Run.seq (Run.assign (v := 1) (by simp; omega))
                    (Run.assign (v := ρ.vars "u") (by simp; omega)))).mono (by simp),
                le_rfl, by simp, by simp, by simp, ?_, by simp, Or.inl ⟨hf0, by simp⟩⟩
              intro y h1 h2
              simp [h1, h2]
            · exact ⟨ρ, 15, (Run.ite_false ((evalB_condEq (evalB_var hfB)
                  (evalB_lit (by omega))).trans (by simp [hf0])) Run.skip).mono (by simp),
                le_rfl, rfl, rfl, rfl, fun y _ _ => rfl, by omega,
                Or.inr ⟨by omega, rfl⟩⟩
          obtain ⟨σ', K, hrun, hK, ha, hi, ho, hfr, hf1, hcase⟩ := hrec
          refine ⟨σ', 60, (Run.ite_false ((evalB_condEq (evalB_var hsB)
              (evalB_lit (by omega))).trans (by simp [hs0]))
              (neTest_ne hwB ht1B hwt1
                (Run.ite_false ((evalB_condEq (evalB_var hsB)
                    (evalB_lit (by omega))).trans (by simp [hs1]))
                  (neTest_ne hwB ht2B hwt2 hrun)))).mono (by simp; omega),
            le_rfl, ha, hi, ho, fun y h1 h2 h3 h4 h5 => hfr y h4 h5,
            Or.inr (Or.inr (Or.inr ⟨hs0, hs1, hwt1, hwt2,
              hfr "seen" (by decide) (by decide), hfr "t1" (by decide) (by decide),
              hfr "t2" (by decide) (by decide), hf1, hcase⟩))⟩

/-! ### What the scan knows about the current block -/

/-- The registers `seen`, `t1`, `t2` describe the block of `o` below the
slot `J` exactly: every unmarked target below `J` is one of the recorded
values, and each recorded value is witnessed by a slot that named it.
This is the whole of the threshold-three test — rung A's `ro`/`cnted`
bookkeeping has no counterpart here. -/
def SeenInv (g : List ℕ) {n : ℕ} (M : Finset (Fin n)) (o : Fin n) (J s t1 t2 : ℕ) : Prop :=
  (∀ p, offset g (o : ℕ) ≤ p → p < J → target g p ∉ markedVals M →
      (1 ≤ s ∧ target g p = t1) ∨ (s = 2 ∧ target g p = t2)) ∧
  (1 ≤ s → ∃ p, offset g (o : ℕ) ≤ p ∧ p < J ∧ target g p = t1 ∧ t1 ∉ markedVals M) ∧
  (s = 2 → t1 ≠ t2 ∧ ∃ p, offset g (o : ℕ) ≤ p ∧ p < J ∧ target g p = t2 ∧
    t2 ∉ markedVals M)

/-- Three values drawn from a pair collide. -/
theorem pigeon3 {a b x y z : ℕ} (hx : x = a ∨ x = b) (hy : y = a ∨ y = b)
    (hz : z = a ∨ z = b) : x = y ∨ x = z ∨ y = z := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    tauto

/-- **The block of the current owner is thin.** Every unmarked target it
has shown is `t1` or `t2`, so three of them collide: this is what makes
the flag's failure to go up a statement about the whole block. -/
theorem thin_of_seenInv {o : Fin n} {J s t1 t2 : ℕ} (h : SeenInv g M o J s t1 t2)
    {p₁ p₂ p₃ : ℕ} (ha₁ : offset g (o : ℕ) ≤ p₁) (hc₁ : p₁ < J)
    (ha₂ : offset g (o : ℕ) ≤ p₂) (hc₂ : p₂ < J)
    (ha₃ : offset g (o : ℕ) ≤ p₃) (hc₃ : p₃ < J)
    (hu₁ : target g p₁ ∉ markedVals M) (hu₂ : target g p₂ ∉ markedVals M)
    (hu₃ : target g p₃ ∉ markedVals M) :
    target g p₁ = target g p₂ ∨ target g p₁ = target g p₃ ∨ target g p₂ = target g p₃ :=
  pigeon3 (a := t1) (b := t2)
    ((h.1 p₁ ha₁ hc₁ hu₁).elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
    ((h.1 p₂ ha₂ hc₂ hu₂).elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
    ((h.1 p₃ ha₃ hc₃ hu₃).elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))

/-- Thin blocks, as far as the scan has looked: no unmarked block has
three differently-targeted unmarked slots below `J`. -/
def ThinBelow (g : List ℕ) {n : ℕ} (M : Finset (Fin n)) (J : ℕ) : Prop :=
  ∀ o : Fin n, o ∉ M → ∀ p₁ p₂ p₃, offset g (o : ℕ) ≤ p₁ → p₁ < offset g ((o : ℕ) + 1) →
    p₁ < J → offset g (o : ℕ) ≤ p₂ → p₂ < offset g ((o : ℕ) + 1) → p₂ < J →
    offset g (o : ℕ) ≤ p₃ → p₃ < offset g ((o : ℕ) + 1) → p₃ < J →
    target g p₁ ∉ markedVals M → target g p₂ ∉ markedVals M → target g p₃ ∉ markedVals M →
    target g p₁ = target g p₂ ∨ target g p₁ = target g p₃ ∨ target g p₂ = target g p₃

/-- Past the last slot, thin below is thin. -/
theorem thinBlocks3_of_thinBelow (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (h : ThinBelow g M (2 * m)) : ThinBlocks3 g M := by
  intro o ho p₁ p₂ p₃ a₁ b₁ a₂ b₂ a₃ b₃ u₁ u₂ u₃
  have hend : offset g ((o : ℕ) + 1) ≤ 2 * m := by
    have := offset_le hg (show (o : ℕ) + 1 ≤ n from o.2)
    omega
  exact h o ho p₁ p₂ p₃ a₁ b₁ (by omega) a₂ b₂ (by omega) a₃ b₃ (by omega) u₁ u₂ u₃

/-- **The slot that keeps the flag down.** If the registers still
describe the block of the current owner one slot further on, the whole
prefix of the target array is still thin: a triple of slots either lies
below the slot just passed, where the invariant already had it, or
belongs to the current owner, where the registers decide it. -/
theorem thinBelow_succ (hg : EncodesGraph g n G) {o : Fin n} {J s t1 t2 : ℕ}
    (hlo : offset g (o : ℕ) ≤ J) (hhi : J < offset g ((o : ℕ) + 1))
    (hthin : ThinBelow g M J) (hseen : o ∉ M → SeenInv g M o (J + 1) s t1 t2) :
    ThinBelow g M (J + 1) := by
  intro o' ho' p₁ p₂ p₃ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ d₁ d₂ d₃
  by_cases hbelow : p₁ < J ∧ p₂ < J ∧ p₃ < J
  · exact hthin o' ho' p₁ p₂ p₃ a₁ b₁ hbelow.1 a₂ b₂ hbelow.2.1 a₃ b₃ hbelow.2.2 d₁ d₂ d₃
  · have hoo : (o' : ℕ) = (o : ℕ) := by
      simp only [not_and_or, not_lt] at hbelow
      rcases hbelow with h | h | h
      · exact owner_unique hg (le_of_lt o'.2) (le_of_lt o.2) a₁ b₁
          (by rw [show p₁ = J by omega]; exact hlo) (by rw [show p₁ = J by omega]; exact hhi)
      · exact owner_unique hg (le_of_lt o'.2) (le_of_lt o.2) a₂ b₂
          (by rw [show p₂ = J by omega]; exact hlo) (by rw [show p₂ = J by omega]; exact hhi)
      · exact owner_unique hg (le_of_lt o'.2) (le_of_lt o.2) a₃ b₃
          (by rw [show p₃ = J by omega]; exact hlo) (by rw [show p₃ = J by omega]; exact hhi)
    have hoeq : o' = o := Fin.ext hoo
    subst hoeq
    exact thin_of_seenInv (hseen ho') a₁ c₁ a₂ c₂ a₃ c₃ d₁ d₂ d₃

/-! ### The descend scan -/

/-- As in rung A: a turn of the scan, and a turn of the owner advance
inside it, move only names the whole scan moves, so the invariant frames
against `descendScan3.wvars` and each turn discharges its frame
obligation through `Run.frame_var_sub`. -/
theorem wvars_slotStep3_sub : slotStep3.wvars ⊆ descendScan3.wvars := by decide

theorem wvars_ownerAdvance3_sub : ownerAdvance3.wvars ⊆ descendScan3.wvars := by decide

/-- The invariant of the descend scan. Beyond the frame conditions and
the position of the owner: while the flag is down the registers
describe the current block exactly (`SeenInv`), and the flag is the
dichotomy — nothing branchable below the pointer, or a named vertex of
residual degree at least three. -/
def ScanInv3 (g : List ℕ) {n : ℕ} (m : ℕ) (G : SimpleGraph (Fin n)) (M : Finset (Fin n))
    (σ τ : Env) : Prop :=
  (∀ y, y ∉ descendScan3.wvars → τ.vars y = σ.vars y) ∧ τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧
  τ.out = σ.out ∧ τ.vars "found" ≤ 1 ∧ τ.vars "seen" ≤ 2 ∧ τ.vars "t1" ≤ n ∧
  τ.vars "t2" ≤ n ∧ τ.vars "u" ≤ n ∧ offset g (τ.vars "u") ≤ τ.vars "j" ∧
  τ.vars "j" ≤ offset g (τ.vars "u" + 1) ∧ τ.vars "j" ≤ 2 * m ∧
  (τ.vars "found" = 0 → ∀ o : Fin n, (o : ℕ) = τ.vars "u" → o ∉ M →
    SeenInv g M o (τ.vars "j") (τ.vars "seen") (τ.vars "t1") (τ.vars "t2")) ∧
  ((τ.vars "found" = 0 ∧ ThinBelow g M (τ.vars "j")) ∨
   (τ.vars "found" = 1 ∧ ∃ v : Fin n, (v : ℕ) = τ.vars "v" ∧ v ∉ M ∧ 3 ≤ resDeg G M v))

/-- **The descend scan.** Started on a represented state, one pass over
the target array leaves the configuration represented and every array
untouched, having decided the branching test at threshold three: either
no unmarked block names three different unmarked vertices — the
solver's hypothesis — or `v` names a vertex of residual degree at least
three, which is what the deeper branch spends its budget on. No frame
condition is stated: the scalars the pass does not touch — `"n"` above
all, which the solver reads and `Rep` is silent about — are read off the
run by `Run.frame_var`. -/
theorem descendScan3_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ p < 2 * m, T p = target g p)
    (h1B : 1 < B) (hnB : n < B) (hmB : 2 * m < B)
    {C : Config n} {τ : Env} (hRep : Rep n m O T C τ) :
    ∃ (τ' : Env) (K : ℕ), Run B descendScan3 τ τ' K ∧ Rep n m O T C τ' ∧
      τ'.arrs = τ.arrs ∧ τ'.inp = τ.inp ∧ τ'.out = τ.out ∧
      ((τ'.vars "found" = 0 ∧ ThinBlocks3 g (marked C.frames)) ∨
        (τ'.vars "found" = 1 ∧ ∃ v : Fin n, (v : ℕ) = τ'.vars "v" ∧
          v ∉ marked C.frames ∧ 3 ≤ resDeg G (marked C.frames) v)) ∧
      K ≤ 800 * (n + 2 * m + 1) := by
  obtain ⟨MK, hmark, hMK⟩ := hRep.mark
  have hm2 := hRep.m2
  have hoff := hRep.off
  have htgt := hRep.tgt
  set M : Finset (Fin n) := marked C.frames with hMdef
  have hMKB : ∀ i, i < n → MK i < B := fun i hi => indicator_lt h1B hMK hi
  have hOB : ∀ i, i ≤ n → O i < B := by
    intro i hi
    have h1 := hO i hi
    have h2 := offset_le hg hi
    omega
  have hoffn : offset g n = 2 * m := by rw [hg.offset_last, hm]
  -- the owner is a vertex as long as the pointer is a slot
  have hult : ∀ ρ : Env, ρ.vars "u" ≤ n → offset g (ρ.vars "u") ≤ ρ.vars "j" →
      ρ.vars "j" < 2 * m → ρ.vars "u" < n := by
    intro ρ h1 h2 h3
    rcases Nat.lt_or_ge (ρ.vars "u") n with h | h
    · exact h
    · exfalso
      have hun : ρ.vars "u" = n := by omega
      rw [hun, hoffn] at h2
      omega
  -- the inner loop's condition, evaluated
  have hcondval : ∀ ρ : Env, ρ.arrs = τ.arrs → ρ.vars "u" < n → ρ.vars "j" < 2 * m →
      (Cond.lt (.get "off" (.add (.var "u") (.lit 1))) (.add (.var "j") (.lit 1))).evalB B ρ
        = some (decide (offset g (ρ.vars "u" + 1) < ρ.vars "j" + 1)) := by
    intro ρ harrs hu hj
    have hOu : O (ρ.vars "u" + 1) = offset g (ρ.vars "u" + 1) := hO _ (by omega)
    have := evalB_condLt (B := B) (σ := ρ)
      (e := .get "off" (.add (.var "u") (.lit 1))) (f := .add (.var "j") (.lit 1))
      (m := O (ρ.vars "u" + 1)) (n := ρ.vars "j" + 1)
      (evalB_get (k := ρ.vars "u" + 1)
        (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
        (by rw [harrs, hoff, getElem?_arrOf O (by omega)]) (hOB _ (by omega)))
      (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
    rwa [hOu] at this
  -- the owner advance
  have hadv : ∀ ρ : Env, ScanInv3 g m G M τ ρ → ρ.vars "j" < 2 * m →
      ∃ ρ' K, Run B ownerAdvance3 ρ ρ' K ∧ ScanInv3 g m G M τ ρ' ∧
        ρ'.vars "j" = ρ.vars "j" ∧ ρ'.vars "j" < offset g (ρ'.vars "u" + 1) ∧
        K + 200 * (n - ρ'.vars "u") ≤ 200 * (n - ρ.vars "u") + 10 := by
    intro ρ hI hj
    have hstep : ∀ ν : Env, (ScanInv3 g m G M τ ν ∧ ν.vars "j" = ρ.vars "j") →
        (Cond.lt (.get "off" (.add (.var "u") (.lit 1)))
          (.add (.var "j") (.lit 1))).evalB B ν = some true →
        ∃ ν' K, Run B (.seq (.assign "u" (.add (.var "u") (.lit 1)))
            (.seq (.assign "seen" (.lit 0))
              (.seq (.assign "t1" (.lit 0)) (.assign "t2" (.lit 0))))) ν ν' K ∧
          (ScanInv3 g m G M τ ν' ∧ ν'.vars "j" = ρ.vars "j") ∧
          1 + (Cond.lt (Expr.get "off" ((Expr.var "u").add (Expr.lit 1)))
              ((Expr.var "j").add (Expr.lit 1))).size + K + 200 * (n - ν'.vars "u") ≤
            200 * (n - ν.vars "u") := by
      rintro ν ⟨⟨hfr, harrs, hinp, hout, hf01, hs2, ht1n, ht2n, hun, hlo, hhi, hj2m,
        hseen, hdich⟩, hjν⟩ hcond
      have hjlt : ν.vars "j" < 2 * m := by omega
      have hu : ν.vars "u" < n := hult ν hun hlo hjlt
      rw [hcondval ν harrs hu hjlt] at hcond
      have hadvlt : offset g (ν.vars "u" + 1) ≤ ν.vars "j" := by
        have : decide (offset g (ν.vars "u" + 1) < ν.vars "j" + 1) = true := by
          simpa using hcond
        simp only [decide_eq_true_eq] at this
        omega
      have heq : offset g (ν.vars "u" + 1) = ν.vars "j" := by omega
      have hu1 : ν.vars "u" + 1 < n := by
        rcases Nat.lt_or_ge (ν.vars "u" + 1) n with h | h
        · exact h
        · exfalso
          have : ν.vars "u" + 1 = n := by omega
          rw [this, hoffn] at heq
          omega
      set ν' : Env := (((ν.setVar "u" (ν.vars "u" + 1)).setVar "seen" 0).setVar "t1"
        0).setVar "t2" 0 with hν'
      have hvu : ν'.vars "u" = ν.vars "u" + 1 := by simp [hν']
      have hvj : ν'.vars "j" = ν.vars "j" := by simp [hν']
      have rbody : Run B (.seq (.assign "u" (.add (.var "u") (.lit 1)))
          (.seq (.assign "seen" (.lit 0))
            (.seq (.assign "t1" (.lit 0)) (.assign "t2" (.lit 0))))) ν ν' 12 :=
        (Run.seq (Run.assign (v := ν.vars "u" + 1) (by simp; omega))
          (Run.seq (Run.assign (v := 0) (by simp; omega))
            (Run.seq (Run.assign (v := 0) (by simp; omega))
              (Run.assign (v := 0) (by simp; omega))))).mono (by simp)
      refine ⟨ν', 12, rbody, ⟨⟨?_, ?_,
        by simp [hν', hinp], by simp [hν', hout], by simp [hν']; omega,
        by simp [hν'], by simp [hν'], by simp [hν'],
        by omega, by rw [hvu, hvj, heq], ?_, by omega, ?_, ?_⟩, by rw [hvj, hjν]⟩, ?_⟩
      · intro y hy
        exact (rbody.frame_var_sub y wvars_ownerAdvance3_sub hy).trans (hfr y hy)
      · simp [hν', harrs]
      · rw [hvu, hvj, ← heq]
        exact offset_mono' hg (by omega) (by omega)
      · intro _ o ho _
        rw [hvu] at ho
        refine ⟨fun p hp1 hp2 _ => ?_, fun hs => absurd (show ν'.vars "seen" = 0 by
          simp [hν']) (by omega), fun hs => absurd (show ν'.vars "seen" = 0 by
          simp [hν']) (by omega)⟩
        exfalso
        rw [ho] at hp1
        rw [hvj] at hp2
        omega
      · rw [hvj, show ν'.vars "found" = ν.vars "found" by simp [hν'],
          show ν'.vars "v" = ν.vars "v" by simp [hν']]
        exact hdich
      · simp only [size_condLt, size_get, size_var, size_bin, size_lit, hvu]
        omega
    obtain ⟨ρ', K, hrun, ⟨hIρ', hjρ'⟩, hfalse, hpay⟩ :=
      Run.while_potential (B := B)
        (b := Cond.lt (.get "off" (.add (.var "u") (.lit 1))) (.add (.var "j") (.lit 1)))
        (c := .seq (.assign "u" (.add (.var "u") (.lit 1)))
          (.seq (.assign "seen" (.lit 0))
            (.seq (.assign "t1" (.lit 0)) (.assign "t2" (.lit 0)))))
        (fun ν => ScanInv3 g m G M τ ν ∧ ν.vars "j" = ρ.vars "j")
        (fun ν => 200 * (n - ν.vars "u"))
        (fun ν hν => by
          obtain ⟨⟨-, harrs, -, -, -, -, -, -, hun, hlo, -, -, -⟩, hjν⟩ := hν
          exact ⟨_, hcondval ν harrs (hult ν hun hlo (by omega)) (by omega)⟩)
        hstep ⟨hI, rfl⟩
    have hu' : ρ'.vars "u" < n :=
      hult ρ' hIρ'.2.2.2.2.2.2.2.2.1 hIρ'.2.2.2.2.2.2.2.2.2.1 (by omega)
    rw [hcondval ρ' hIρ'.2.1 hu' (by omega)] at hfalse
    refine ⟨ρ', K, hrun, hIρ', hjρ', ?_, ?_⟩
    · have : decide (offset g (ρ'.vars "u" + 1) < ρ'.vars "j" + 1) = false := by
        simpa using hfalse
      simp only [decide_eq_false_iff_not, not_lt] at this
      omega
    · simp only [size_condLt, size_get, size_var, size_bin, size_lit] at hpay
      omega
  -- one turn of the pass: the owner advance, then the slot
  have hstep : ∀ ρ, ScanInv3 g m G M τ ρ →
      (Cond.lt (.var "j") (.var "m2")).evalB B ρ = some true →
      ∃ ρ' K, Run B (.seq ownerAdvance3 slotStep3) ρ ρ' K ∧ ScanInv3 g m G M τ ρ' ∧
        1 + (Cond.lt (Expr.var "j") (Expr.var "m2")).size + K +
          (400 * (2 * m - ρ'.vars "j") + 200 * (n - ρ'.vars "u")) ≤
            400 * (2 * m - ρ.vars "j") + 200 * (n - ρ.vars "u") := by
    intro ρ hI hcond
    have hm2ρ : ρ.vars "m2" = 2 * m := by rw [hI.1 "m2" (by decide), hm2]
    have hjlt : ρ.vars "j" < 2 * m := by
      have := lt_of_condLt_true hcond
      omega
    obtain ⟨ρ₁, K₁, r₁, hI₁, hj₁, hblk, hpay₁⟩ := hadv ρ hI hjlt
    obtain ⟨hfr, harrs, hinp, hout, hf01, hs2, ht1n, ht2n, hun, hlo, hhi, hj2m,
      hseen, hdich⟩ := hI₁
    have hjρ₁ : ρ₁.vars "j" < 2 * m := by omega
    have hu : ρ₁.vars "u" < n := hult ρ₁ hun hlo hjρ₁
    have hmarkρ : ρ₁.arrs "mark" = arrOf n MK := by rw [harrs, hmark]
    have htgtρ : ρ₁.arrs "tgt" = arrOf (2 * m) T := by rw [harrs, htgt]
    have htj : T (ρ₁.vars "j") = target g (ρ₁.vars "j") := hT _ hjρ₁
    have htjn : target g (ρ₁.vars "j") < n := target_lt' hg hu hblk
    have hcondmark : ∀ (ν : Env) (x : String), ν.arrs "mark" = arrOf n MK →
        ν.vars x < n → (Cond.eq (.get "mark" (.var x)) (.lit 0)).evalB B ν
          = some (MK (ν.vars x) == 0) := by
      intro ν x hmν hx
      exact evalB_condEq (evalB_get (k := ν.vars x) (evalB_var (by omega))
        (by rw [hmν, getElem?_arrOf MK hx]) (hMKB _ hx)) (evalB_lit (by omega))
    -- a slot that is not residual moves nothing but the pointer
    have hskip : ∀ ρ' : Env, ρ'.arrs = ρ₁.arrs → ρ'.inp = ρ₁.inp → ρ'.out = ρ₁.out →
        (∀ y, y ≠ "j" → y ≠ "w" → ρ'.vars y = ρ₁.vars y) →
        ρ'.vars "j" = ρ₁.vars "j" + 1 →
        ((⟨ρ₁.vars "u", hu⟩ : Fin n) ∈ M ∨ target g (ρ₁.vars "j") ∈ markedVals M) →
        ScanInv3 g m G M τ ρ' := by
      intro ρ' ha hi ho hv hj hdead
      have hu' : ρ'.vars "u" = ρ₁.vars "u" := hv "u" (by decide) (by decide)
      have hdeadp : ∀ o : Fin n, (o : ℕ) = ρ₁.vars "u" → o ∉ M →
          target g (ρ₁.vars "j") ∈ markedVals M := by
        intro o ho hoM
        rcases hdead with h | h
        · exact absurd (show o ∈ M from (Fin.ext ho : o = ⟨ρ₁.vars "u", hu⟩) ▸ h) hoM
        · exact h
      refine ⟨fun y hy => ?_, by rw [ha, harrs], by rw [hi, hinp], by rw [ho, hout],
        by rw [hv "found" (by decide) (by decide)]; exact hf01,
        by rw [hv "seen" (by decide) (by decide)]; exact hs2,
        by rw [hv "t1" (by decide) (by decide)]; exact ht1n,
        by rw [hv "t2" (by decide) (by decide)]; exact ht2n,
        by rw [hu']; exact hun, by rw [hu', hj]; omega, by rw [hu', hj]; omega,
        by rw [hj]; omega, ?_, ?_⟩
      · rw [hv y (notMem_wvars_ne hy (by decide)) (notMem_wvars_ne hy (by decide))]
        exact hfr y hy
      · intro hf o ho hoM
        rw [hu'] at ho
        rw [hv "seen" (by decide) (by decide), hv "t1" (by decide) (by decide),
          hv "t2" (by decide) (by decide), hj]
        obtain ⟨hc1, hc2, hc3⟩ := hseen (by rwa [hv "found" (by decide) (by decide)] at hf)
          o ho hoM
        refine ⟨fun p hp1 hp2 hp3 => ?_, fun hs => ?_, fun hs => ?_⟩
        · rcases Nat.lt_or_ge p (ρ₁.vars "j") with hp | hp
          · exact hc1 p hp1 hp hp3
          · exact absurd (show target g p ∈ markedVals M by
              rw [show p = ρ₁.vars "j" by omega]; exact hdeadp o ho hoM) hp3
        · obtain ⟨p, hp1, hp2, hp3, hp4⟩ := hc2 hs
          exact ⟨p, hp1, by omega, hp3, hp4⟩
        · obtain ⟨hne, p, hp1, hp2, hp3, hp4⟩ := hc3 hs
          exact ⟨hne, p, hp1, by omega, hp3, hp4⟩
      · rw [hv "found" (by decide) (by decide), hv "v" (by decide) (by decide), hj]
        rcases hdich with ⟨hf, hall⟩ | ⟨hf, hv1⟩
        · refine Or.inl ⟨hf, ?_⟩
          intro o ho p₁ p₂ p₃ ha₁ hb₁ hc₁ ha₂ hb₂ hc₂ ha₃ hb₃ hc₃ hd₁ hd₂ hd₃
          have key : ∀ p, offset g (o : ℕ) ≤ p → p < offset g ((o : ℕ) + 1) →
              p < ρ₁.vars "j" + 1 → target g p ∉ markedVals M → p < ρ₁.vars "j" := by
            intro p hpa hpb hpc hpd
            rcases Nat.lt_or_ge p (ρ₁.vars "j") with h | h
            · exact h
            · exfalso
              have hpe : p = ρ₁.vars "j" := by omega
              subst hpe
              have hou : (o : ℕ) = ρ₁.vars "u" :=
                owner_unique hg (le_of_lt o.2) (le_of_lt hu) hpa hpb hlo hblk
              exact hpd (hdeadp o hou ho)
          exact hall o ho p₁ p₂ p₃ ha₁ hb₁ (key p₁ ha₁ hb₁ hc₁ hd₁) ha₂ hb₂
            (key p₂ ha₂ hb₂ hc₂ hd₂) ha₃ hb₃ (key p₃ ha₃ hb₃ hc₃ hd₃) hd₁ hd₂ hd₃
        · exact Or.inr ⟨hf, hv1⟩
    -- the three shapes a slot can have
    by_cases hMKu : MK (ρ₁.vars "u") = 0
    · have hUnot : (⟨ρ₁.vars "u", hu⟩ : Fin n) ∉ M := not_mem_of_indicator_eq hMK hu hMKu
      have hcu : (Cond.eq (.get "mark" (.var "u")) (.lit 0)).evalB B ρ₁ = some true := by
        rw [hcondmark ρ₁ "u" hmarkρ hu]
        simp [hMKu]
      have rw₁ : Run B (.assign "w" (.get "tgt" (.var "j"))) ρ₁
          (ρ₁.setVar "w" (target g (ρ₁.vars "j"))) 3 :=
        (Run.assign (v := target g (ρ₁.vars "j")) (evalB_get (k := ρ₁.vars "j")
          (evalB_var (by omega)) (by rw [htgtρ, getElem?_arrOf T hjρ₁, htj])
          (by omega))).mono (by simp)
      have hmarkρ₂ : (ρ₁.setVar "w" (target g (ρ₁.vars "j"))).arrs "mark" = arrOf n MK := by
        rw [arrs_setVar, hmarkρ]
      have hvw : (ρ₁.setVar "w" (target g (ρ₁.vars "j"))).vars "w" =
          target g (ρ₁.vars "j") := by simp
      by_cases hMKw : MK (target g (ρ₁.vars "j")) = 0
      · -- a residual slot: the dedup runs
        have htjnot : target g (ρ₁.vars "j") ∉ markedVals M :=
          (indicator_zero_iff hMK htjn).1 hMKw
        have hcw : (Cond.eq (.get "mark" (.var "w")) (.lit 0)).evalB B
            (ρ₁.setVar "w" (target g (ρ₁.vars "j"))) = some true := by
          rw [hcondmark _ "w" hmarkρ₂ (by rw [hvw]; exact htjn), hvw]
          simp [hMKw]
        set ρ₂ : Env := ρ₁.setVar "w" (target g (ρ₁.vars "j")) with hρ₂
        have h₂s : ρ₂.vars "seen" = ρ₁.vars "seen" := by simp [hρ₂]
        have h₂t1 : ρ₂.vars "t1" = ρ₁.vars "t1" := by simp [hρ₂]
        have h₂t2 : ρ₂.vars "t2" = ρ₁.vars "t2" := by simp [hρ₂]
        have h₂f : ρ₂.vars "found" = ρ₁.vars "found" := by simp [hρ₂]
        have h₂v : ρ₂.vars "v" = ρ₁.vars "v" := by simp [hρ₂]
        have h₂u : ρ₂.vars "u" = ρ₁.vars "u" := by simp [hρ₂]
        obtain ⟨ρ₄, K₄, r₄, hK₄, ha₄, hi₄, ho₄, hv₄, hcase₄⟩ :=
          dedupFound_run (B := B) (ρ := ρ₂) h1B (by omega) (by rw [h₂s]; omega)
            (by rw [h₂t1]; omega) (by rw [h₂t2]; omega) (by rw [hvw]; omega)
            (by rw [h₂f]; omega) (by rw [h₂f]; omega) (by rw [h₂s]; omega)
            (by rw [h₂u]; omega)
        have hj₄ : ρ₄.vars "j" = ρ₁.vars "j" := by
          rw [hv₄ "j" (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp [hρ₂]
        have hu₄ : ρ₄.vars "u" = ρ₁.vars "u" := by
          rw [hv₄ "u" (by decide) (by decide) (by decide) (by decide) (by decide), h₂u]
        have rslot : Run B slotStep3 ρ₁ (ρ₄.setVar "j" (ρ₁.vars "j" + 1)) 200 :=
          (Run.seq
            (Run.ite_true hcu (Run.seq rw₁ (Run.ite_true hcw r₄)))
            (Run.assign (v := ρ₁.vars "j" + 1) (by
              simp [hj₄]; omega))).mono (by simp; omega)
        refine ⟨ρ₄.setVar "j" (ρ₁.vars "j" + 1), K₁ + 200, Run.seq r₁ rslot, ?_, ?_⟩
        · -- the invariant, after a residual slot
          set ρ₅ : Env := ρ₄.setVar "j" (ρ₁.vars "j" + 1) with hρ₅
          have hfrall : ∀ y, y ≠ "j" → y ≠ "w" → y ≠ "seen" → y ≠ "t1" → y ≠ "t2" →
              y ≠ "found" → y ≠ "v" → ρ₅.vars y = ρ₁.vars y := by
            intro y h0 h1 h2 h3 h4 h5 h6
            rw [hρ₅, vars_setVar, if_neg h0, hv₄ y h2 h3 h4 h5 h6, hρ₂, vars_setVar,
              if_neg h1]
          have hu₅ : ρ₅.vars "u" = ρ₁.vars "u" :=
            hfrall "u" (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide)
          have hj₅ : ρ₅.vars "j" = ρ₁.vars "j" + 1 := by simp [hρ₅]
          have hs₅ : ρ₅.vars "seen" = ρ₄.vars "seen" := by simp [hρ₅]
          have ht1₅ : ρ₅.vars "t1" = ρ₄.vars "t1" := by simp [hρ₅]
          have ht2₅ : ρ₅.vars "t2" = ρ₄.vars "t2" := by simp [hρ₅]
          have hf₅ : ρ₅.vars "found" = ρ₄.vars "found" := by simp [hρ₅]
          have hv₅ : ρ₅.vars "v" = ρ₄.vars "v" := by simp [hρ₅]
          have hoU : ∀ o : Fin n, (o : ℕ) = ρ₁.vars "u" → o = ⟨ρ₁.vars "u", hu⟩ :=
            fun o ho => Fin.ext ho
          have harr₅ : ρ₅.arrs = τ.arrs := by
            rw [hρ₅, arrs_setVar, ha₄, hρ₂, arrs_setVar, harrs]
          -- the four shapes of the dedup, each with its registers and its verdict
          have hmain : (ρ₅.vars "found" ≤ 1 ∧ ρ₅.vars "seen" ≤ 2 ∧ ρ₅.vars "t1" ≤ n ∧
              ρ₅.vars "t2" ≤ n) ∧
              (ρ₅.vars "found" = 0 → ∀ o : Fin n, (o : ℕ) = ρ₅.vars "u" → o ∉ M →
                SeenInv g M o (ρ₅.vars "j") (ρ₅.vars "seen") (ρ₅.vars "t1")
                  (ρ₅.vars "t2")) ∧
              ((ρ₅.vars "found" = 0 ∧ ThinBelow g M (ρ₅.vars "j")) ∨
                (ρ₅.vars "found" = 1 ∧ ∃ v : Fin n, (v : ℕ) = ρ₅.vars "v" ∧ v ∉ M ∧
                  3 ≤ resDeg G M v)) := by
            have hcarry : ∀ (s' t1' t2' : ℕ),
                (ρ₅.vars "found" = 0 → ∀ o : Fin n, (o : ℕ) = ρ₁.vars "u" → o ∉ M →
                  SeenInv g M o (ρ₁.vars "j" + 1) s' t1' t2') →
                ρ₅.vars "seen" = s' → ρ₅.vars "t1" = t1' → ρ₅.vars "t2" = t2' →
                ρ₅.vars "found" = ρ₁.vars "found" →
                ρ₅.vars "v" = ρ₁.vars "v" → s' ≤ 2 → t1' ≤ n → t2' ≤ n →
                (ρ₅.vars "found" ≤ 1 ∧ ρ₅.vars "seen" ≤ 2 ∧ ρ₅.vars "t1" ≤ n ∧
                  ρ₅.vars "t2" ≤ n) ∧
                (ρ₅.vars "found" = 0 → ∀ o : Fin n, (o : ℕ) = ρ₅.vars "u" → o ∉ M →
                  SeenInv g M o (ρ₅.vars "j") (ρ₅.vars "seen") (ρ₅.vars "t1")
                    (ρ₅.vars "t2")) ∧
                ((ρ₅.vars "found" = 0 ∧ ThinBelow g M (ρ₅.vars "j")) ∨
                  (ρ₅.vars "found" = 1 ∧ ∃ v : Fin n, (v : ℕ) = ρ₅.vars "v" ∧ v ∉ M ∧
                    3 ≤ resDeg G M v)) := by
              intro s' t1' t2' hSeen' hs' ht1' ht2' hf' hv' hs2' ht1n' ht2n'
              refine ⟨⟨by rw [hf']; exact hf01, by rw [hs']; exact hs2',
                  by rw [ht1']; exact ht1n', by rw [ht2']; exact ht2n'⟩,
                by rw [hu₅, hj₅, hs', ht1', ht2']; exact hSeen', ?_⟩
              rcases hdich with ⟨hfz, hthin⟩ | ⟨hfz, hwit⟩
              · refine Or.inl ⟨by rw [hf', hfz], ?_⟩
                rw [hj₅]
                exact thinBelow_succ (o := ⟨ρ₁.vars "u", hu⟩) (s := s') (t1 := t1')
                  (t2 := t2') hg hlo hblk hthin
                  (fun hom => hSeen' (by rw [hf', hfz]) ⟨ρ₁.vars "u", hu⟩ rfl hom)
              · exact Or.inr ⟨by rw [hf', hfz], by rw [hv']; exact hwit⟩
            rcases hcase₄ with ⟨hs0, hs1', ht1', ht2', hf', hv'⟩ |
              ⟨hs0, hrep, hs1', ht1', ht2', hf', hv'⟩ |
              ⟨hs1, hne1, hs1', ht1', ht2', hf', hv'⟩ |
              ⟨hs0, hs1, hne1, hne2, hs1', ht1', ht2', hf', hvcase⟩
            · -- the block's first unmarked target
              refine hcarry 1 (target g (ρ₁.vars "j")) (ρ₁.vars "t2") ?_
                (by rw [hs₅, hs1']) (by rw [ht1₅, ht1', hvw]) (by rw [ht2₅, ht2', h₂t2])
                (by rw [hf₅, hf', h₂f]) (by rw [hv₅, hv', h₂v]) (by omega) (by omega)
                (by omega)
              intro hfz o ho hoM
              have hoeq := hoU o ho
              have hs0' : ρ₁.vars "seen" = 0 := by rw [← h₂s]; exact hs0
              have hlo' : offset g (o : ℕ) ≤ ρ₁.vars "j" := by rw [ho]; exact hlo
              refine ⟨fun p hp1 hp2 hp3 => ?_, fun _ => ⟨ρ₁.vars "j", hlo', by omega,
                rfl, htjnot⟩, fun hz => absurd hz (by omega)⟩
              rcases Nat.lt_or_ge p (ρ₁.vars "j") with hp | hp
              · exfalso
                have := (hseen (by rw [hf₅, hf', h₂f] at hfz; exact hfz) o ho hoM).1 p hp1
                  hp hp3
                rw [hs0'] at this
                rcases this with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
              · exact Or.inl ⟨le_rfl, by rw [show p = ρ₁.vars "j" by omega]⟩
            · -- a repeat of a recorded target
              refine hcarry (ρ₁.vars "seen") (ρ₁.vars "t1") (ρ₁.vars "t2") ?_
                (by rw [hs₅, hs1', h₂s]) (by rw [ht1₅, ht1', h₂t1])
                (by rw [ht2₅, ht2', h₂t2]) (by rw [hf₅, hf', h₂f]) (by rw [hv₅, hv', h₂v])
                (by omega) (by omega) (by omega)
              intro hfz o ho hoM
              have hfz' : ρ₁.vars "found" = 0 := by rw [hf₅, hf', h₂f] at hfz; exact hfz
              obtain ⟨hc1, hc2, hc3⟩ := hseen hfz' o ho hoM
              have hs0' : ρ₁.vars "seen" ≠ 0 := by rw [← h₂s]; exact hs0
              refine ⟨fun p hp1 hp2 hp3 => ?_, fun hs => ?_, fun hs => ?_⟩
              · rcases Nat.lt_or_ge p (ρ₁.vars "j") with hp | hp
                · exact hc1 p hp1 hp hp3
                · rw [show p = ρ₁.vars "j" by omega]
                  rcases hrep with h | ⟨h2, h⟩
                  · refine Or.inl ⟨by omega, ?_⟩
                    rw [← hvw, h, h₂t1]
                  · refine Or.inr ⟨by rw [← h₂s]; exact h2, ?_⟩
                    rw [← hvw, h, h₂t2]
              · obtain ⟨p, hp1, hp2, hp3, hp4⟩ := hc2 hs
                exact ⟨p, hp1, by omega, hp3, hp4⟩
              · obtain ⟨hne, p, hp1, hp2, hp3, hp4⟩ := hc3 hs
                exact ⟨hne, p, hp1, by omega, hp3, hp4⟩
            · -- the block's second distinct unmarked target
              have hs1'' : ρ₁.vars "seen" = 1 := by rw [← h₂s]; exact hs1
              refine hcarry 2 (ρ₁.vars "t1") (target g (ρ₁.vars "j")) ?_
                (by rw [hs₅, hs1']) (by rw [ht1₅, ht1', h₂t1]) (by rw [ht2₅, ht2', hvw])
                (by rw [hf₅, hf', h₂f]) (by rw [hv₅, hv', h₂v]) (by omega) (by omega)
                (by omega)
              intro hfz o ho hoM
              have hfz' : ρ₁.vars "found" = 0 := by rw [hf₅, hf', h₂f] at hfz; exact hfz
              obtain ⟨hc1, hc2, hc3⟩ := hseen hfz' o ho hoM
              have hlo' : offset g (o : ℕ) ≤ ρ₁.vars "j" := by rw [ho]; exact hlo
              have hnet : ρ₁.vars "t1" ≠ target g (ρ₁.vars "j") := by
                intro h
                exact hne1 (by rw [hvw, h₂t1, h])
              refine ⟨fun p hp1 hp2 hp3 => ?_, fun _ => ?_,
                fun _ => ⟨hnet, ρ₁.vars "j", hlo', by omega, rfl, htjnot⟩⟩
              · rcases Nat.lt_or_ge p (ρ₁.vars "j") with hp | hp
                · rcases hc1 p hp1 hp hp3 with ⟨-, h⟩ | ⟨h, -⟩
                  · exact Or.inl ⟨by omega, h⟩
                  · exact absurd h (by omega)
                · exact Or.inr ⟨rfl, by rw [show p = ρ₁.vars "j" by omega]⟩
              · obtain ⟨p, hp1, hp2, hp3, hp4⟩ := hc2 (by omega)
                exact ⟨p, hp1, by omega, hp3, hp4⟩
            · -- a third distinct unmarked target: the flag goes up
              have hs2' : ρ₁.vars "seen" = 2 := by
                rw [h₂s] at hs0 hs1
                omega
              have hfound : ρ₅.vars "found" = 1 := by rw [hf₅, hf']
              refine ⟨⟨by omega, by rw [hs₅, hs1', h₂s]; omega,
                by rw [ht1₅, ht1', h₂t1]; exact ht1n,
                by rw [ht2₅, ht2', h₂t2]; exact ht2n⟩,
                fun hz => absurd hz (by omega), Or.inr ⟨hfound, ?_⟩⟩
              rcases hvcase with ⟨hfz, hvv⟩ | ⟨hfz, hvv⟩
              · -- the first branching vertex the pass has seen
                have hfz' : ρ₁.vars "found" = 0 := by rw [← h₂f]; exact hfz
                obtain ⟨hc1, hc2, hc3⟩ := hseen hfz' ⟨ρ₁.vars "u", hu⟩ rfl hUnot
                obtain ⟨p₁, hp₁a, hp₁b, hp₁c, hp₁d⟩ := hc2 (by omega)
                obtain ⟨hnet, p₂, hp₂a, hp₂b, hp₂c, hp₂d⟩ := hc3 hs2'
                refine ⟨⟨ρ₁.vars "u", hu⟩, by rw [hv₅, hvv, h₂u], hUnot, ?_⟩
                refine three_le_resDeg_of_slots hg hp₁a
                  (show p₁ < offset g (ρ₁.vars "u" + 1) by omega) hp₂a
                  (show p₂ < offset g (ρ₁.vars "u" + 1) by omega) hlo
                  hblk (by rw [hp₁c]; exact hp₁d) (by rw [hp₂c]; exact hp₂d) htjnot ?_ ?_ ?_
                · rw [hp₁c, hp₂c]; exact hnet
                · rw [hp₁c]
                  intro h
                  exact hne1 (by rw [hvw, ← h, h₂t1])
                · rw [hp₂c]
                  intro h
                  exact hne2 (by rw [hvw, ← h, h₂t2])
              · -- the flag was already up, and keeps its witness
                have hfz' : ρ₁.vars "found" = 1 := by rw [← h₂f]; exact hfz
                rcases hdich with ⟨hfz'', -⟩ | ⟨-, v₀, hv0, hv1⟩
                · omega
                · exact ⟨v₀, by rw [hv₅, hvv, h₂v]; exact hv0, hv1⟩
          obtain ⟨⟨hb1, hb2, hb3, hb4⟩, hSeen₅, hdich₅⟩ := hmain
          exact ⟨fun y hy => (rslot.frame_var_sub y wvars_slotStep3_sub hy).trans (hfr y hy),
            harr₅, by rw [hρ₅, inp_setVar, hi₄, hρ₂, inp_setVar, hinp],
            by rw [hρ₅, out_setVar, ho₄, hρ₂, out_setVar, hout],
            hb1, hb2, hb3, hb4, by rw [hu₅]; exact hun, by rw [hu₅, hj₅]; omega,
            by rw [hu₅, hj₅]; omega, by rw [hj₅]; omega, hSeen₅, hdich₅⟩
        · -- the payment
          have hju : (ρ₄.setVar "j" (ρ₁.vars "j" + 1)).vars "u" = ρ₁.vars "u" := by
            rw [vars_setVar, if_neg (by decide), hu₄]
          have hjj : (ρ₄.setVar "j" (ρ₁.vars "j" + 1)).vars "j" = ρ₁.vars "j" + 1 := by
            simp
          simp only [size_condLt, size_var, hju, hjj]
          omega
      · -- the target is marked
        refine ⟨(ρ₁.setVar "w" (target g (ρ₁.vars "j"))).setVar "j" (ρ₁.vars "j" + 1),
          K₁ + 200, Run.seq r₁ ((Run.seq (Run.ite_true hcu (Run.seq rw₁
            (Run.ite_false (by
              rw [hcondmark _ "w" hmarkρ₂ (by rw [hvw]; exact htjn), hvw]
              simp [hMKw]) Run.skip)))
            (Run.assign (v := ρ₁.vars "j" + 1) (by simp; omega))).mono (by simp)), ?_, ?_⟩
        · refine hskip _ (by simp) (by simp) (by simp) (fun y h1 h2 => by simp [h1, h2])
            (by simp) (Or.inr ?_)
          by_contra hcon
          exact hMKw ((indicator_zero_iff hMK htjn).2 hcon)
        · have hjj : ((ρ₁.setVar "w" (target g (ρ₁.vars "j"))).setVar "j"
              (ρ₁.vars "j" + 1)).vars "j" = ρ₁.vars "j" + 1 := by simp
          have hju : ((ρ₁.setVar "w" (target g (ρ₁.vars "j"))).setVar "j"
              (ρ₁.vars "j" + 1)).vars "u" = ρ₁.vars "u" := by simp
          simp only [size_condLt, size_var, hjj, hju]
          omega
    · -- the owner is marked
      refine ⟨ρ₁.setVar "j" (ρ₁.vars "j" + 1), K₁ + 200,
        Run.seq r₁ ((Run.seq (Run.ite_false (by
            rw [hcondmark ρ₁ "u" hmarkρ hu]
            simp [hMKu]) Run.skip)
          (Run.assign (v := ρ₁.vars "j" + 1) (by simp; omega))).mono (by simp)), ?_, ?_⟩
      · exact hskip _ (by simp) (by simp) (by simp) (fun y h1 h2 => by simp [h1])
          (by simp) (Or.inl (mem_of_indicator_ne hMK hu hMKu))
      · have hjj : (ρ₁.setVar "j" (ρ₁.vars "j" + 1)).vars "j" = ρ₁.vars "j" + 1 := by simp
        have hju : (ρ₁.setVar "j" (ρ₁.vars "j" + 1)).vars "u" = ρ₁.vars "u" := by simp
        simp only [size_condLt, size_var, hjj, hju]
        omega
  -- the pass, from the initial state of its registers
  set σ₀ : Env := ((((((τ.setVar "j" 0).setVar "u" 0).setVar "found" 0).setVar "seen"
    0).setVar "t1" 0).setVar "t2" 0) with hσ₀
  have hI₀ : ScanInv3 g m G M τ σ₀ := by
    refine ⟨fun y hy => ?_, by simp [hσ₀], by simp [hσ₀], by simp [hσ₀], by simp [hσ₀],
      by simp [hσ₀], by simp [hσ₀], by simp [hσ₀], by simp [hσ₀], ?_, ?_, by simp [hσ₀],
      ?_, ?_⟩
    · have hne : ∀ z ∈ descendScan3.wvars, y ≠ z := fun _ hz => notMem_wvars_ne hy hz
      simp [hσ₀, hne "j" (by decide), hne "u" (by decide), hne "found" (by decide),
        hne "seen" (by decide), hne "t1" (by decide), hne "t2" (by decide)]
    · simp [hσ₀, hg.offset_zero]
    · simp [hσ₀]
    · intro _ o ho _
      exact ⟨fun p _ hp2 _ => absurd hp2 (by simp [hσ₀]),
        fun hs => absurd hs (by simp [hσ₀]), fun hs => absurd hs (by simp [hσ₀])⟩
    · refine Or.inl ⟨by simp [hσ₀], ?_⟩
      intro o _ p₁ p₂ p₃ _ _ hc₁
      exact absurd hc₁ (by simp [hσ₀])
  obtain ⟨τ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := Cond.lt (.var "j") (.var "m2"))
      (c := .seq ownerAdvance3 slotStep3) (ScanInv3 g m G M τ)
      (fun ν => 400 * (2 * m - ν.vars "j") + 200 * (n - ν.vars "u"))
      (fun ν hν => by
        have h1 : ν.vars "m2" = 2 * m := by rw [hν.1 "m2" (by decide), hm2]
        exact evalB_condLt_vars (by
          have := hν.2.2.2.2.2.2.2.2.2.2.2.1
          omega) (by omega))
      hstep hI₀
  obtain ⟨hfr', harrs', hinp', hout', hf01', hs2', ht1n', ht2n', hun', hlo', hhi',
    hj2m', hseen', hdich'⟩ := hI'
  have hm2' : τ'.vars "m2" = 2 * m := by rw [hfr' "m2" (by decide), hm2]
  have hjend : τ'.vars "j" = 2 * m := by
    have := le_of_condLt_false hfalse
    omega
  refine ⟨τ', 800 * (n + 2 * m + 1),
    ((Run.seq (Run.assign (v := 0) (by simp; omega))
      (Run.seq (Run.assign (v := 0) (by simp; omega))
        (Run.seq (Run.assign (v := 0) (by simp; omega))
          (Run.seq (Run.assign (v := 0) (by simp; omega))
            (Run.seq (Run.assign (v := 0) (by simp; omega))
              (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun))))))).mono ?_,
    ?_, harrs', hinp', hout', ?_, le_rfl⟩
  · simp only [hσ₀] at hpay
    simp only [size_condLt, size_var, size_lit] at hpay ⊢
    simp only [vars_setVar] at hpay
    omega
  · exact hRep.of_vars_eq harrs' (by rw [hfr' "m2" (by decide)])
      (by rw [hfr' "mode" (by decide)]) (by rw [hfr' "bud" (by decide)])
      (by rw [hfr' "ans" (by decide)]) (by rw [hfr' "top" (by decide)])
      (by rw [hfr' "tt" (by decide)])
  · rcases hdich' with ⟨hf, hthin⟩ | ⟨hf, hwit⟩
    · exact Or.inl ⟨hf, thinBlocks3_of_thinBelow hg hm (by rw [← hjend]; exact hthin)⟩
    · exact Or.inr ⟨hf, hwit⟩

/-! ### The solver's queue

The breadth-first sweep of the components driver, with the same
discipline: `vis` is set before the enqueue, so the queue holds each
visited vertex exactly once and is never reset between components. Here
the visited set is carried as a `Finset` rather than read off the array,
which makes the two facts the sweep needs — that the queue has room for
one more, and that a drained queue has expanded everything visited —
statements about cardinality. -/

/-- The queue holds exactly the visited vertices, once each, and `head`
is inside it. -/
structure Queue {n : ℕ} (V : Finset (Fin n)) (Q : ℕ → ℕ) (head tl : ℕ) : Prop where
  /-- The queue is as long as the visited set. -/
  card : tl = V.card
  /-- The expanded part is a prefix of the queue. -/
  hd : head ≤ tl
  /-- Everything on the queue is a visited vertex. -/
  mem : ∀ i < tl, ∃ v : Fin n, (v : ℕ) = Q i ∧ v ∈ V
  /-- Every visited vertex is on the queue. -/
  all : ∀ v ∈ V, ∃ i < tl, Q i = (v : ℕ)
  /-- Nothing is on the queue twice. -/
  inj : ∀ i < tl, ∀ j < tl, Q i = Q j → i = j

/-- The queue fits in the array. -/
theorem Queue.tl_le {V : Finset (Fin n)} {Q : ℕ → ℕ} {head tl : ℕ}
    (h : Queue V Q head tl) : tl ≤ n := by
  rw [h.card]
  simpa using Finset.card_le_univ V

/-- An unvisited vertex leaves room for one more. -/
theorem Queue.tl_lt {V : Finset (Fin n)} {Q : ℕ → ℕ} {head tl : ℕ} (h : Queue V Q head tl)
    {w : Fin n} (hw : w ∉ V) : tl < n := by
  rw [h.card]
  have : V ⊂ Finset.univ := ⟨Finset.subset_univ V, fun hsub => hw (hsub (Finset.mem_univ w))⟩
  simpa using Finset.card_lt_card this

/-- Enqueueing an unvisited vertex. -/
theorem Queue.push {V : Finset (Fin n)} {Q : ℕ → ℕ} {head tl : ℕ} (h : Queue V Q head tl)
    {w : Fin n} (hw : w ∉ V) :
    Queue (insert w V) (fun i => if i = tl then (w : ℕ) else Q i) head (tl + 1) where
  card := by rw [Finset.card_insert_of_notMem hw, h.card]
  hd := by have := h.hd; omega
  mem := by
    intro i hi
    by_cases hit : i = tl
    · exact ⟨w, by simp [hit], Finset.mem_insert_self _ _⟩
    · obtain ⟨v, hv1, hv2⟩ := h.mem i (by omega)
      exact ⟨v, by simp [hit, hv1], Finset.mem_insert_of_mem hv2⟩
  all := by
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact ⟨tl, by omega, by simp⟩
    · obtain ⟨i, hi, hQ⟩ := h.all v hv
      exact ⟨i, by omega, by simp [show i ≠ tl by omega, hQ]⟩
  inj := by
    intro i hi j hj hij
    by_cases hit : i = tl <;> by_cases hjt : j = tl
    · omega
    · exfalso
      obtain ⟨v, hv1, hv2⟩ := h.mem j (by omega)
      rw [if_pos hit, if_neg hjt] at hij
      have hwv : w = v := Fin.ext (by rw [hij, hv1])
      exact hw (by rw [hwv]; exact hv2)
    · exfalso
      obtain ⟨v, hv1, hv2⟩ := h.mem i (by omega)
      rw [if_neg hit, if_pos hjt] at hij
      have hwv : w = v := Fin.ext (by rw [← hij, hv1])
      exact hw (by rw [hwv]; exact hv2)
    · simp only [if_neg hit, if_neg hjt] at hij
      exact h.inj i (by omega) j (by omega) hij

/-- **The count and the push.** A distinct unmarked target of the
dequeued vertex `u` counts the edge `{u, w}` into the halving toggle if
`u` is its smaller endpoint, and visits and enqueues `w` if the search
has not reached it. The visited set afterwards is `insert w V`, whether
or not `w` was there already. -/
theorem countPush_run (h1B : 1 < B) (hnB : n < B) {ρ : Env} {V : Finset (Fin n)}
    {VIS Q : ℕ → ℕ} {u w : Fin n} {head tl : ℕ}
    (hvis : ρ.arrs "vis" = arrOf n VIS) (hVIS : Indicator V VIS)
    (hq : ρ.arrs "q" = arrOf n Q) (hQ : Queue V Q head tl)
    (hu : ρ.vars "u" = (u : ℕ)) (hw : ρ.vars "w" = (w : ℕ)) (htl : ρ.vars "tl" = tl)
    (hsB : ρ.vars "s" + 1 < B) (htog : ρ.vars "tog" ≤ 1) :
    ∃ (ρ' : Env) (VIS' Q' : ℕ → ℕ) (K : ℕ), Run B countPush ρ ρ' K ∧ K ≤ 60 ∧
      ρ'.inp = ρ.inp ∧ ρ'.out = ρ.out ∧
      (∀ a, a ≠ "vis" → a ≠ "q" → ρ'.arrs a = ρ.arrs a) ∧
      (∀ y, y ≠ "s" → y ≠ "tog" → y ≠ "tl" → ρ'.vars y = ρ.vars y) ∧
      ρ'.arrs "vis" = arrOf n VIS' ∧ Indicator (insert w V) VIS' ∧
      ρ'.arrs "q" = arrOf n Q' ∧ Queue (insert w V) Q' head (ρ'.vars "tl") ∧
      (∀ i < tl, Q' i = Q i) ∧ tl ≤ ρ'.vars "tl" ∧ ρ'.vars "tl" ≤ n ∧
      ((u < w ∧ ρ.vars "tog" = 0 ∧ ρ'.vars "s" = ρ.vars "s" + 1 ∧ ρ'.vars "tog" = 1) ∨
       (u < w ∧ ρ.vars "tog" = 1 ∧ ρ'.vars "s" = ρ.vars "s" ∧ ρ'.vars "tog" = 0) ∨
       (¬ ((u : ℕ) < (w : ℕ)) ∧ ρ'.vars "s" = ρ.vars "s" ∧
          ρ'.vars "tog" = ρ.vars "tog")) := by
  have hwn : (w : ℕ) < n := w.2
  have hun : (u : ℕ) < n := u.2
  -- the counting half
  have hcount : ∃ (ρ₁ : Env) (K : ℕ), Run B
      (.ite (.lt (.var "u") (.var "w"))
        (.ite (.eq (.var "tog") (.lit 0))
          (.seq (.assign "s" (.add (.var "s") (.lit 1))) (.assign "tog" (.lit 1)))
          (.assign "tog" (.lit 0)))
        .skip) ρ ρ₁ K ∧ K ≤ 20 ∧ ρ₁.arrs = ρ.arrs ∧ ρ₁.inp = ρ.inp ∧ ρ₁.out = ρ.out ∧
      (∀ y, y ≠ "s" → y ≠ "tog" → ρ₁.vars y = ρ.vars y) ∧
      (((u : ℕ) < (w : ℕ) ∧ ρ.vars "tog" = 0 ∧ ρ₁.vars "s" = ρ.vars "s" + 1 ∧
          ρ₁.vars "tog" = 1) ∨
       ((u : ℕ) < (w : ℕ) ∧ ρ.vars "tog" = 1 ∧ ρ₁.vars "s" = ρ.vars "s" ∧
          ρ₁.vars "tog" = 0) ∨
       (¬ ((u : ℕ) < (w : ℕ)) ∧ ρ₁.vars "s" = ρ.vars "s" ∧
          ρ₁.vars "tog" = ρ.vars "tog")) := by
    by_cases hlt : (u : ℕ) < (w : ℕ)
    · have hc : (Cond.lt (.var "u") (.var "w")).evalB B ρ = some true :=
        (evalB_condLt (evalB_var (by omega)) (evalB_var (by omega))).trans
          (by simp [hu, hw, hlt])
      by_cases ht0 : ρ.vars "tog" = 0
      · refine ⟨(ρ.setVar "s" (ρ.vars "s" + 1)).setVar "tog" 1, 20,
          (Run.ite_true hc (Run.ite_true ((evalB_condEq (evalB_var (by omega))
              (evalB_lit (by omega))).trans (by simp [ht0]))
            (Run.seq (Run.assign (v := ρ.vars "s" + 1) (by simp; omega))
              (Run.assign (v := 1) (by simp; omega))))).mono (by simp),
          le_rfl, by simp, by simp, by simp, ?_, Or.inl ⟨hlt, ht0, by simp, by simp⟩⟩
        intro y h1 h2
        simp [h1, h2]
      · refine ⟨ρ.setVar "tog" 0, 20,
          (Run.ite_true hc (Run.ite_false ((evalB_condEq (evalB_var (by omega))
              (evalB_lit (by omega))).trans (by simp [ht0]))
            (Run.assign (v := 0) (by simp; omega)))).mono (by simp),
          le_rfl, by simp, by simp, by simp, ?_,
          Or.inr (Or.inl ⟨hlt, by omega, by simp, by simp⟩)⟩
        intro y h1 h2
        simp [h2]
    · exact ⟨ρ, 20, (Run.ite_false ((evalB_condLt (evalB_var (by omega))
        (evalB_var (by omega))).trans (by simp [hu, hw, hlt])) Run.skip).mono (by simp),
        le_rfl, rfl, rfl, rfl, fun y _ _ => rfl, Or.inr (Or.inr ⟨hlt, rfl, rfl⟩)⟩
  obtain ⟨ρ₁, K₁, r₁, hK₁, ha₁, hi₁, ho₁, hfr₁, hcase₁⟩ := hcount
  have hvis₁ : ρ₁.arrs "vis" = arrOf n VIS := by rw [ha₁, hvis]
  have hq₁ : ρ₁.arrs "q" = arrOf n Q := by rw [ha₁, hq]
  have hw₁ : ρ₁.vars "w" = (w : ℕ) := by rw [hfr₁ "w" (by decide) (by decide), hw]
  have htl₁ : ρ₁.vars "tl" = tl := by rw [hfr₁ "tl" (by decide) (by decide), htl]
  have hVISB : VIS (w : ℕ) < B := indicator_lt h1B hVIS hwn
  have hcvis : (Cond.eq (.get "vis" (.var "w")) (.lit 0)).evalB B ρ₁
      = some (VIS (w : ℕ) == 0) := by
    have hev : (Expr.var "w").evalB B ρ₁ = some (w : ℕ) := by
      rw [← hw₁]; exact evalB_var (by omega)
    exact evalB_condEq (evalB_get (k := (w : ℕ)) hev
      (by rw [hvis₁, getElem?_arrOf VIS hwn]) hVISB) (evalB_lit (by omega))
  by_cases hvw : VIS (w : ℕ) = 0
  · -- an unvisited target: it is visited and enqueued
    have hwV : w ∉ V := not_mem_of_indicator_eq hVIS hwn hvw
    have htln : tl < n := hQ.tl_lt hwV
    set ρ₂ : Env := ((ρ₁.setArr "vis" (w : ℕ) 1).setArr "q" tl (w : ℕ)).setVar "tl" (tl + 1)
      with hρ₂
    have r₂ : Run B (.seq (.store "vis" (.var "w") (.lit 1))
        (.seq (.store "q" (.var "tl") (.var "w"))
          (.assign "tl" (.add (.var "tl") (.lit 1))))) ρ₁ ρ₂ 12 :=
      (Run.seq (Run.store (idx := (w : ℕ)) (v := 1) (by simp [hw₁]; omega)
          (by simp; omega) (by rw [hvis₁, length_arrOf]; exact hwn))
        (Run.seq (Run.store (idx := tl) (v := (w : ℕ)) (by simp [htl₁]; omega)
            (by simp [hw₁]; omega)
            (by rw [arrs_setArr, if_neg (by decide), hq₁, length_arrOf]; exact htln))
          (Run.assign (v := tl + 1) (by simp [htl₁]; omega)))).mono (by simp)
    refine ⟨ρ₂, fun x => if x = (w : ℕ) then 1 else VIS x,
      fun i => if i = tl then (w : ℕ) else Q i, K₁ + 40,
      (Run.seq r₁ (Run.ite_true (by simp [hcvis, hvw]) r₂)).mono (by simp),
      by omega, by simp [hρ₂, hi₁], by simp [hρ₂, ho₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by simp [hρ₂], by simp [hρ₂]; omega, ?_⟩
    · intro a h1 h2
      simp only [hρ₂, arrs_setVar, arrs_setArr, if_neg h1, if_neg h2]
      exact ha₁ ▸ rfl
    · intro y h1 h2 h3
      simp only [hρ₂, vars_setVar, vars_setArr, if_neg h3]
      exact hfr₁ y h1 h2
    · rw [hρ₂, arrs_setVar, arrs_setArr, if_neg (by decide), arrs_setArr, if_pos rfl,
        hvis₁, set_arrOf]
    · exact indicator_set_one hVIS hwn
    · rw [hρ₂, arrs_setVar, arrs_setArr, if_pos rfl, arrs_setArr, if_neg (by decide),
        hq₁, set_arrOf]
    · have : ρ₂.vars "tl" = tl + 1 := by simp [hρ₂]
      rw [this]
      exact hQ.push hwV
    · intro i hi
      simp [show i ≠ tl by omega]
    · rcases hcase₁ with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨h1, h2, by simp [hρ₂, h3], by simp [hρ₂, h4]⟩
      · exact Or.inr (Or.inl ⟨h1, h2, by simp [hρ₂, h3], by simp [hρ₂, h4]⟩)
      · exact Or.inr (Or.inr ⟨h1, by simp [hρ₂, h2], by simp [hρ₂, h3]⟩)
  · -- the target has been visited already
    have hwV : w ∈ V := mem_of_indicator_ne hVIS hwn hvw
    refine ⟨ρ₁, VIS, Q, K₁ + 40,
      (Run.seq r₁ (Run.ite_false (by simp [hcvis, hvw]) Run.skip)).mono (by simp),
      by omega, hi₁, ho₁, fun a _ _ => by rw [ha₁], fun y h1 h2 _ => hfr₁ y h1 h2,
      hvis₁, by rwa [Finset.insert_eq_self.2 hwV], hq₁, ?_, fun i _ => rfl,
      le_of_eq htl₁.symm, by rw [htl₁]; exact hQ.tl_le, ?_⟩
    · rw [htl₁, Finset.insert_eq_self.2 hwV]
      exact hQ
    · rcases hcase₁ with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-- **The dedup, with the solver's actions.** A first or second distinct
unmarked target is counted and enqueued; a repeat is ignored; a third
distinct one is *skipped* — the branch that `ThinBlocks3` makes
unreachable, and which the row scan refutes. -/
theorem dedupCount_run (h1B : 1 < B) (hnB : n < B) (h2B : 2 < B) {ρ : Env}
    {V : Finset (Fin n)} {VIS Q : ℕ → ℕ} {u w : Fin n} {head tl : ℕ}
    (hvis : ρ.arrs "vis" = arrOf n VIS) (hVIS : Indicator V VIS)
    (hq : ρ.arrs "q" = arrOf n Q) (hQ : Queue V Q head tl)
    (hu : ρ.vars "u" = (u : ℕ)) (hw : ρ.vars "w" = (w : ℕ)) (htl : ρ.vars "tl" = tl)
    (hsB : ρ.vars "s" + 1 < B) (htog : ρ.vars "tog" ≤ 1) (hs2 : ρ.vars "seen" ≤ 2)
    (ht1B : ρ.vars "t1" < B) (ht2B : ρ.vars "t2" < B) :
    ∃ (ρ' : Env) (VIS' Q' : ℕ → ℕ) (V' : Finset (Fin n)) (K : ℕ),
      Run B (dedupStep countPush countPush .skip) ρ ρ' K ∧ K ≤ 200 ∧
      ρ'.inp = ρ.inp ∧ ρ'.out = ρ.out ∧
      (∀ a, a ≠ "vis" → a ≠ "q" → ρ'.arrs a = ρ.arrs a) ∧
      (∀ y, y ≠ "s" → y ≠ "tog" → y ≠ "tl" → y ≠ "seen" → y ≠ "t1" → y ≠ "t2" →
        ρ'.vars y = ρ.vars y) ∧
      ρ'.arrs "vis" = arrOf n VIS' ∧ Indicator V' VIS' ∧
      ρ'.arrs "q" = arrOf n Q' ∧ Queue V' Q' head (ρ'.vars "tl") ∧
      (∀ i < tl, Q' i = Q i) ∧ tl ≤ ρ'.vars "tl" ∧ ρ'.vars "tl" ≤ n ∧
      ρ'.vars "tog" ≤ 1 ∧ ρ'.vars "seen" ≤ 2 ∧
      ((V' = insert w V ∧
        ((ρ.vars "seen" = 0 ∧ ρ'.vars "seen" = 1 ∧ ρ'.vars "t1" = (w : ℕ) ∧
            ρ'.vars "t2" = ρ.vars "t2") ∨
         (ρ.vars "seen" = 1 ∧ (w : ℕ) ≠ ρ.vars "t1" ∧ ρ'.vars "seen" = 2 ∧
            ρ'.vars "t1" = ρ.vars "t1" ∧ ρ'.vars "t2" = (w : ℕ))) ∧
        (((u : ℕ) < (w : ℕ) ∧ ρ.vars "tog" = 0 ∧ ρ'.vars "s" = ρ.vars "s" + 1 ∧
            ρ'.vars "tog" = 1) ∨
         ((u : ℕ) < (w : ℕ) ∧ ρ.vars "tog" = 1 ∧ ρ'.vars "s" = ρ.vars "s" ∧
            ρ'.vars "tog" = 0) ∨
         (¬ ((u : ℕ) < (w : ℕ)) ∧ ρ'.vars "s" = ρ.vars "s" ∧
            ρ'.vars "tog" = ρ.vars "tog"))) ∨
       (ρ' = ρ ∧ V' = V ∧ ρ.vars "seen" ≠ 0 ∧
        ((w : ℕ) = ρ.vars "t1" ∨ (ρ.vars "seen" = 2 ∧ (w : ℕ) = ρ.vars "t2") ∨
         (ρ.vars "seen" = 2 ∧ (w : ℕ) ≠ ρ.vars "t1" ∧ (w : ℕ) ≠ ρ.vars "t2")))) := by
  have hwn : (w : ℕ) < n := w.2
  have hsB' : ρ.vars "seen" < B := by omega
  have hwB : ρ.vars "w" < B := by rw [hw]; omega
  -- the two branches that record a new target both end in `countPush`
  have hnew : ∀ (ρa : Env), ρa.arrs = ρ.arrs → ρa.inp = ρ.inp → ρa.out = ρ.out →
      (∀ y, y ≠ "seen" → y ≠ "t1" → y ≠ "t2" → ρa.vars y = ρ.vars y) →
      ∃ (ρ' : Env) (VIS' Q' : ℕ → ℕ) (K : ℕ), Run B countPush ρa ρ' K ∧ K ≤ 60 ∧
        ρ'.inp = ρ.inp ∧ ρ'.out = ρ.out ∧
        (∀ a, a ≠ "vis" → a ≠ "q" → ρ'.arrs a = ρ.arrs a) ∧
        (∀ y, y ≠ "s" → y ≠ "tog" → y ≠ "tl" → ρ'.vars y = ρa.vars y) ∧
        ρ'.arrs "vis" = arrOf n VIS' ∧ Indicator (insert w V) VIS' ∧
        ρ'.arrs "q" = arrOf n Q' ∧ Queue (insert w V) Q' head (ρ'.vars "tl") ∧
        (∀ i < tl, Q' i = Q i) ∧ tl ≤ ρ'.vars "tl" ∧ ρ'.vars "tl" ≤ n ∧
        (((u : ℕ) < (w : ℕ) ∧ ρ.vars "tog" = 0 ∧ ρ'.vars "s" = ρ.vars "s" + 1 ∧
            ρ'.vars "tog" = 1) ∨
         ((u : ℕ) < (w : ℕ) ∧ ρ.vars "tog" = 1 ∧ ρ'.vars "s" = ρ.vars "s" ∧
            ρ'.vars "tog" = 0) ∨
         (¬ ((u : ℕ) < (w : ℕ)) ∧ ρ'.vars "s" = ρ.vars "s" ∧
            ρ'.vars "tog" = ρ.vars "tog")) := by
    intro ρa ha hi ho hfr
    obtain ⟨ρ', VIS', Q', K, hrun, hK, hi', ho', ha', hfr', hv1, hv2, hv3, hv4, hv5,
      hv6, hv7, hcase⟩ :=
      countPush_run (B := B) (V := V) (VIS := VIS) (Q := Q) (u := u) (w := w)
        (head := head) (tl := tl) h1B hnB (by rw [ha, hvis]) hVIS (by rw [ha, hq]) hQ
        (by rw [hfr "u" (by decide) (by decide) (by decide), hu])
        (by rw [hfr "w" (by decide) (by decide) (by decide), hw])
        (by rw [hfr "tl" (by decide) (by decide) (by decide), htl])
        (by rw [hfr "s" (by decide) (by decide) (by decide)]; omega)
        (by rw [hfr "tog" (by decide) (by decide) (by decide)]; omega)
    have hsa : ρa.vars "s" = ρ.vars "s" := hfr "s" (by decide) (by decide) (by decide)
    have hta : ρa.vars "tog" = ρ.vars "tog" :=
      hfr "tog" (by decide) (by decide) (by decide)
    refine ⟨ρ', VIS', Q', K, hrun, hK, by rw [hi', hi], by rw [ho', ho], ?_, hfr',
      hv1, hv2, hv3, hv4, hv5, hv6, hv7, ?_⟩
    · intro a h1 h2
      rw [ha' a h1 h2, ha]
    · rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨h1, by omega, by omega, h4⟩
      · exact Or.inr (Or.inl ⟨h1, by omega, by omega, h4⟩)
      · exact Or.inr (Or.inr ⟨h1, by omega, by omega⟩)
  by_cases hs0 : ρ.vars "seen" = 0
  · -- the block's first unmarked target: counted and enqueued
    set ρa : Env := (ρ.setVar "seen" 1).setVar "t1" (ρ.vars "w") with hρa
    obtain ⟨ρ', VIS', Q', K, hrun, hK, hi', ho', ha', hfr', hv1, hv2, hv3, hv4, hv5,
      hv6, hv7, hcase⟩ :=
      hnew ρa (by simp [hρa]) (by simp [hρa]) (by simp [hρa])
        (fun y h1 h2 _ => by simp [hρa, h1, h2])
    refine ⟨ρ', VIS', Q', insert w V, K + 60,
      (Run.ite_true ((evalB_condEq (evalB_var hsB') (evalB_lit (by omega))).trans
          (by simp [hs0]))
        (Run.seq (Run.assign (v := 1) (by simp; omega))
          (Run.seq (Run.assign (v := ρ.vars "w") (by simp; omega)) hrun))).mono
        (by simp; omega),
      by omega, hi', ho', ha', ?_, hv1, hv2, hv3, hv4, hv5, hv6, hv7, ?_, ?_,
      Or.inl ⟨rfl, Or.inl ⟨hs0, ?_, ?_, ?_⟩, hcase⟩⟩
    · intro y h1 h2 h3 h4 h5 h6
      rw [hfr' y h1 h2 h3]
      simp [hρa, h4, h5]
    · rcases hcase with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩
      · omega
      · omega
      · omega
    · rw [hfr' "seen" (by decide) (by decide) (by decide)]
      simp [hρa]
    · rw [hfr' "seen" (by decide) (by decide) (by decide)]
      simp [hρa]
    · rw [hfr' "t1" (by decide) (by decide) (by decide)]
      simp [hρa, hw]
    · rw [hfr' "t2" (by decide) (by decide) (by decide)]
      simp [hρa]
  · by_cases hwt1 : ρ.vars "w" = ρ.vars "t1"
    · -- a repeat of the first target
      exact ⟨ρ, VIS, Q, V, 200, (Run.ite_false ((evalB_condEq (evalB_var hsB')
          (evalB_lit (by omega))).trans (by simp [hs0]))
          (neTest_eq hwB ht1B hwt1)).mono (by simp), le_rfl, rfl, rfl,
        fun a _ _ => rfl, fun y _ _ _ _ _ _ => rfl, hvis, hVIS, hq, by rw [htl]; exact hQ,
        fun i _ => rfl, by rw [htl], by rw [htl]; exact hQ.tl_le, htog, hs2,
        Or.inr ⟨rfl, rfl, hs0, Or.inl (by rw [← hw, hwt1])⟩⟩
    · by_cases hs1 : ρ.vars "seen" = 1
      · -- the block's second distinct unmarked target
        set ρa : Env := (ρ.setVar "seen" 2).setVar "t2" (ρ.vars "w") with hρa
        obtain ⟨ρ', VIS', Q', K, hrun, hK, hi', ho', ha', hfr', hv1, hv2, hv3, hv4, hv5,
          hv6, hv7, hcase⟩ :=
          hnew ρa (by simp [hρa]) (by simp [hρa]) (by simp [hρa])
            (fun y h1 _ h3 => by simp [hρa, h1, h3])
        refine ⟨ρ', VIS', Q', insert w V, K + 100,
          (Run.ite_false ((evalB_condEq (evalB_var hsB') (evalB_lit (by omega))).trans
              (by simp [hs0]))
            (neTest_ne hwB ht1B hwt1
              (Run.ite_true ((evalB_condEq (evalB_var hsB') (evalB_lit (by omega))).trans
                  (by simp [hs1]))
                (Run.seq (Run.assign (v := 2) (by simp; omega))
                  (Run.seq (Run.assign (v := ρ.vars "w") (by simp; omega))
                    hrun))))).mono (by simp; omega),
          by omega, hi', ho', ha', ?_, hv1, hv2, hv3, hv4, hv5, hv6, hv7, ?_, ?_,
          Or.inl ⟨rfl, Or.inr ⟨hs1, by rw [← hw]; exact hwt1, ?_, ?_, ?_⟩, hcase⟩⟩
        · intro y h1 h2 h3 h4 h5 h6
          rw [hfr' y h1 h2 h3]
          simp [hρa, h4, h6]
        · rcases hcase with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩
          · omega
          · omega
          · omega
        · rw [hfr' "seen" (by decide) (by decide) (by decide)]
          simp [hρa]
        · rw [hfr' "seen" (by decide) (by decide) (by decide)]
          simp [hρa]
        · rw [hfr' "t1" (by decide) (by decide) (by decide)]
          simp [hρa]
        · rw [hfr' "t2" (by decide) (by decide) (by decide)]
          simp [hρa, hw]
      · -- a repeat of the second target, or a third distinct one: nothing happens
        have hs2' : ρ.vars "seen" = 2 := by omega
        by_cases hwt2 : ρ.vars "w" = ρ.vars "t2"
        · exact ⟨ρ, VIS, Q, V, 200, (Run.ite_false ((evalB_condEq (evalB_var hsB')
              (evalB_lit (by omega))).trans (by simp [hs0]))
              (neTest_ne hwB ht1B hwt1
                (Run.ite_false ((evalB_condEq (evalB_var hsB')
                    (evalB_lit (by omega))).trans (by simp [hs1]))
                  (neTest_eq hwB ht2B hwt2)))).mono (by simp), le_rfl, rfl, rfl,
            fun a _ _ => rfl, fun y _ _ _ _ _ _ => rfl, hvis, hVIS, hq,
            by rw [htl]; exact hQ, fun i _ => rfl, by rw [htl],
            by rw [htl]; exact hQ.tl_le, htog, hs2,
            Or.inr ⟨rfl, rfl, hs0, Or.inr (Or.inl ⟨hs2', by rw [← hw, hwt2]⟩)⟩⟩
        · exact ⟨ρ, VIS, Q, V, 200, (Run.ite_false ((evalB_condEq (evalB_var hsB')
              (evalB_lit (by omega))).trans (by simp [hs0]))
              (neTest_ne hwB ht1B hwt1
                (Run.ite_false ((evalB_condEq (evalB_var hsB')
                    (evalB_lit (by omega))).trans (by simp [hs1]))
                  (neTest_ne hwB ht2B hwt2 Run.skip)))).mono (by simp), le_rfl, rfl, rfl,
            fun a _ _ => rfl, fun y _ _ _ _ _ _ => rfl, hvis, hVIS, hq,
            by rw [htl]; exact hQ, fun i _ => rfl, by rw [htl],
            by rw [htl]; exact hQ.tl_le, htog, hs2,
            Or.inr ⟨rfl, rfl, hs0, Or.inr (Or.inr ⟨hs2', by rw [← hw]; exact hwt1,
              by rw [← hw]; exact hwt2⟩)⟩⟩

/-! ### The solver's row scan

One dequeued vertex, its whole block. `resTgts` is the set of residual
targets the block has shown below the pointer — what the visited set
grows by, and what the toggle halves the upward edges of. The dedup's
registers are tied to it by cardinality, which is how the scan knows a
target is new. Three distinct targets cannot occur: `resTgts` would be
a third residual neighbour of `u`, which `ThinBlocks3` has excluded.
That is where the solver's hypothesis is spent, and the only place. -/

/-- The residual targets of the block of `o` named below the slot `J`. -/
def resTgts (g : List ℕ) {n : ℕ} (M : Finset (Fin n)) (o : Fin n) (J : ℕ) :
    Finset (Fin n) :=
  Finset.univ.filter fun x => x ∉ M ∧ ∃ p ∈ Finset.range J, offset g (o : ℕ) ≤ p ∧
    target g p = (x : ℕ)

theorem mem_resTgts {o : Fin n} {J : ℕ} {x : Fin n} :
    x ∈ resTgts g M o J ↔ x ∉ M ∧ ∃ p, offset g (o : ℕ) ≤ p ∧ p < J ∧
      target g p = (x : ℕ) := by
  simp only [resTgts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨h1, p, hp, h2, h3⟩
    exact ⟨h1, p, h2, hp, h3⟩
  · rintro ⟨h1, p, h2, hp, h3⟩
    exact ⟨h1, p, hp, h2, h3⟩

@[simp] theorem resTgts_start {o : Fin n} : resTgts g M o (offset g (o : ℕ)) = ∅ := by
  ext x
  simp only [mem_resTgts, Finset.notMem_empty, iff_false, not_and]
  rintro - ⟨p, h1, h2, -⟩
  omega

/-- A slot whose target is marked contributes nothing. -/
theorem resTgts_succ_of_marked {o : Fin n} {J : ℕ} (h : target g J ∈ markedVals M) :
    resTgts g M o (J + 1) = resTgts g M o J := by
  ext x
  simp only [mem_resTgts]
  constructor
  · rintro ⟨h1, p, h2, h3, h4⟩
    refine ⟨h1, p, h2, ?_, h4⟩
    rcases Nat.lt_or_ge p J with hp | hp
    · exact hp
    · exact absurd (show (x : ℕ) ∈ markedVals M by rw [← h4, show p = J by omega]; exact h)
        (fun hx => h1 ((mem_markedVals_iff x.2).1 hx))
  · rintro ⟨h1, p, h2, h3, h4⟩
    exact ⟨h1, p, h2, by omega, h4⟩

/-- A slot whose target is unmarked adds it. -/
theorem resTgts_succ_of_unmarked {o : Fin n} {J : ℕ} (hlo : offset g (o : ℕ) ≤ J)
    (htn : target g J < n) (h : target g J ∉ markedVals M) :
    resTgts g M o (J + 1) = insert (⟨target g J, htn⟩ : Fin n) (resTgts g M o J) := by
  ext x
  simp only [mem_resTgts, Finset.mem_insert]
  constructor
  · rintro ⟨h1, p, h2, h3, h4⟩
    rcases Nat.lt_or_ge p J with hp | hp
    · exact Or.inr ⟨h1, p, h2, hp, h4⟩
    · exact Or.inl (Fin.ext (by rw [← h4, show p = J by omega]))
  · rintro (rfl | ⟨h1, p, h2, h3, h4⟩)
    · exact ⟨fun hx => h ((mem_markedVals_iff htn).2 hx), J, hlo, by omega, rfl⟩
    · exact ⟨h1, p, h2, by omega, h4⟩

/-- Past the last slot of the block, the residual targets are the
residual neighbourhood. -/
theorem resTgts_end (hg : EncodesGraph g n G) {o : Fin n} :
    resTgts g M o (offset g ((o : ℕ) + 1)) = ResNbhd G M o := by
  ext x
  rw [mem_resTgts]
  constructor
  · rintro ⟨hx, p, hp1, hp2, hp3⟩
    obtain ⟨y, hy1, hy2⟩ := exists_mem_resNbhd_of_slot (M := M) hg hp1 hp2
      (fun hm => hx ((mem_markedVals_iff x.2).1 (hp3 ▸ hm)))
    rwa [show x = y from Fin.ext (by rw [hy1, hp3])]
  · intro hx
    obtain ⟨p, h1, h2, h3, h4⟩ := exists_slot_of_mem_resNbhd hg hx
    exact ⟨(mem_resNbhd.1 hx).2, p, h1, h2, h3⟩

/-- The invariant of the row scan. -/
def RowInv3 (g : List ℕ) {n : ℕ} (M V : Finset (Fin n)) (u : Fin n) (Q : ℕ → ℕ)
    (head tl s0 tog0 : ℕ) (σ ν : Env) : Prop :=
  (∀ y, y ≠ "s" → y ≠ "tog" → y ≠ "tl" → y ≠ "seen" → y ≠ "t1" → y ≠ "t2" →
      y ≠ "j" → y ≠ "w" → ν.vars y = σ.vars y) ∧
  (∀ a, a ≠ "vis" → a ≠ "q" → ν.arrs a = σ.arrs a) ∧ ν.inp = σ.inp ∧ ν.out = σ.out ∧
  offset g (u : ℕ) ≤ ν.vars "j" ∧ ν.vars "j" ≤ offset g ((u : ℕ) + 1) ∧
  ν.vars "seen" ≤ 2 ∧ ν.vars "t1" ≤ n ∧ ν.vars "t2" ≤ n ∧ ν.vars "tog" ≤ 1 ∧
  ν.vars "s" ≤ s0 + 1 ∧
  (resTgts g M u (ν.vars "j")).card = ν.vars "seen" ∧
  (1 ≤ ν.vars "seen" → ∃ x ∈ resTgts g M u (ν.vars "j"), (x : ℕ) = ν.vars "t1") ∧
  (ν.vars "seen" = 2 → (∃ x ∈ resTgts g M u (ν.vars "j"), (x : ℕ) = ν.vars "t2") ∧
    ν.vars "t1" ≠ ν.vars "t2") ∧
  ν.vars "s" = s0 + (((resTgts g M u (ν.vars "j")).filter
      (fun x : Fin n => (u : ℕ) < (x : ℕ))).card + 1 - tog0) / 2 ∧
  ν.vars "tog" = (((resTgts g M u (ν.vars "j")).filter
      (fun x : Fin n => (u : ℕ) < (x : ℕ))).card + tog0) % 2 ∧
  ∃ VIS' Q' : ℕ → ℕ, ν.arrs "vis" = arrOf n VIS' ∧
    Indicator (V ∪ resTgts g M u (ν.vars "j")) VIS' ∧
    ν.arrs "q" = arrOf n Q' ∧ Queue (V ∪ resTgts g M u (ν.vars "j")) Q' head
      (ν.vars "tl") ∧ (∀ i < tl, Q' i = Q i) ∧ tl ≤ ν.vars "tl" ∧ ν.vars "tl" ≤ n

theorem resTgts_mono {o : Fin n} {J J' : ℕ} (h : J ≤ J') :
    resTgts g M o J ⊆ resTgts g M o J' := by
  intro x hx
  obtain ⟨h1, p, h2, h3, h4⟩ := mem_resTgts.1 hx
  exact mem_resTgts.2 ⟨h1, p, h2, by omega, h4⟩

/-! #### The row scan itself

One dequeued vertex, its whole block. The conclusion hands the drain the
visited set and the queue grown by `ResNbhd G M u`, and the toggle in
closed form: with `c` the residual neighbours of `u` above `u` — the
edges of `u` counted at their smaller endpoint — the cost `s` rises by
`(c + 1 - tog) / 2` and the toggle becomes `(c + tog) % 2`. That is
`⌈e/2⌉` accumulated one edge at a time.

Three facts carry the step: `dedupCount_run` for the slot,
`resTgts_succ_of_unmarked` / `resTgts_succ_of_marked` for the set of
recorded targets, and — for the branch where the dedup reports a *third*
distinct target — `resTgts_mono` together with `resTgts_end`, which put
three residual targets inside `ResNbhd G M u` and so contradict the
standing `resDeg ≤ 2`. The cost is stated per block, which is what lets
the drain amortize it: each vertex is expanded at most once, so the
blocks summed over a drain are at most `2m`. -/

/-- A one-element finset is the singleton of any of its members. -/
theorem eq_singleton_of_card_one {s : Finset (Fin n)} {a : Fin n} (hcard : s.card = 1)
    (ha : a ∈ s) : s = {a} :=
  (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.2 ha)
    (by simp [hcard])).symm

/-- A two-element finset is the pair of any two distinct members. -/
theorem eq_pair_of_card_two {s : Finset (Fin n)} {a b : Fin n} (hcard : s.card = 2)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : s = {a, b} :=
  (Finset.eq_of_subset_of_card_le
    (Finset.insert_subset_iff.2 ⟨ha, Finset.singleton_subset_iff.2 hb⟩)
    (by rw [hcard, Finset.card_pair hab])).symm

/-- **The solver's row scan.** From the start of the block of a dequeued
vertex `u` of residual degree at most two, with the per-row registers
reset, the loop visits and enqueues every residual neighbour of `u` and
counts the edges of `u` that point upward into the halving toggle. -/
theorem rowScan3_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hT : ∀ p < 2 * m, T p = target g p)
    (h1B : 1 < B) (h2B : 2 < B) (hnB : n < B) (hmB : 2 * m < B)
    {V : Finset (Fin n)} {u : Fin n} {MK VIS Q : ℕ → ℕ} {head tl : ℕ} {σ : Env}
    (hdeg : resDeg G M u ≤ 2)
    (hmark : σ.arrs "mark" = arrOf n MK) (hMK : Indicator M MK)
    (htgt : σ.arrs "tgt" = arrOf (2 * m) T)
    (hvis : σ.arrs "vis" = arrOf n VIS) (hVIS : Indicator V VIS)
    (hq : σ.arrs "q" = arrOf n Q) (hQ : Queue V Q head tl) (htl : σ.vars "tl" = tl)
    (hu : σ.vars "u" = (u : ℕ)) (hj : σ.vars "j" = offset g (u : ℕ))
    (hjend : σ.vars "jend" = offset g ((u : ℕ) + 1))
    (hseen : σ.vars "seen" = 0) (ht1 : σ.vars "t1" = 0) (ht2 : σ.vars "t2" = 0)
    (htog : σ.vars "tog" ≤ 1) (hsB : σ.vars "s" + 2 < B) :
    ∃ (τ' : Env) (VIS' Q' : ℕ → ℕ) (K : ℕ),
      Run B (.while (.lt (.var "j") (.var "jend")) solveSlot) σ τ' K ∧
      τ'.inp = σ.inp ∧ τ'.out = σ.out ∧
      (∀ a, a ≠ "vis" → a ≠ "q" → τ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "s" → y ≠ "tog" → y ≠ "tl" → y ≠ "seen" → y ≠ "t1" → y ≠ "t2" →
        y ≠ "j" → y ≠ "w" → τ'.vars y = σ.vars y) ∧
      τ'.arrs "vis" = arrOf n VIS' ∧ Indicator (V ∪ ResNbhd G M u) VIS' ∧
      τ'.arrs "q" = arrOf n Q' ∧ Queue (V ∪ ResNbhd G M u) Q' head (τ'.vars "tl") ∧
      (∀ i < tl, Q' i = Q i) ∧ tl ≤ τ'.vars "tl" ∧ τ'.vars "tl" ≤ n ∧
      τ'.vars "s" = σ.vars "s" +
        (((ResNbhd G M u).filter (fun x : Fin n => (u : ℕ) < (x : ℕ))).card + 1 -
          σ.vars "tog") / 2 ∧
      τ'.vars "tog" =
        (((ResNbhd G M u).filter (fun x : Fin n => (u : ℕ) < (x : ℕ))).card +
          σ.vars "tog") % 2 ∧
      K ≤ 300 * (offset g ((u : ℕ) + 1) - offset g (u : ℕ)) + 10 := by
  classical
  have hend : offset g ((u : ℕ) + 1) ≤ 2 * m := by
    have := offset_le hg (show (u : ℕ) + 1 ≤ n from u.2)
    omega
  have hstart : offset g (u : ℕ) ≤ offset g ((u : ℕ) + 1) := offset_mono' hg (by omega) u.2
  have hMKB : ∀ i, i < n → MK i < B := fun i hi => indicator_lt h1B hMK hi
  -- the recorded targets never outgrow the residual neighbourhood
  have hsubN : ∀ J, J ≤ offset g ((u : ℕ) + 1) → resTgts g M u J ⊆ ResNbhd G M u := by
    intro J hJ
    rw [← resTgts_end (G := G) (M := M) (o := u) hg]
    exact resTgts_mono hJ
  have hstep : ∀ ρ, RowInv3 g M V u Q head tl (σ.vars "s") (σ.vars "tog") σ ρ →
      (Cond.lt (Expr.var "j") (Expr.var "jend")).evalB B ρ = some true →
      ∃ ρ' K, Run B solveSlot ρ ρ' K ∧
        RowInv3 g M V u Q head tl (σ.vars "s") (σ.vars "tog") σ ρ' ∧
        1 + (Cond.lt (Expr.var "j") (Expr.var "jend")).size + K +
            300 * (offset g ((u : ℕ) + 1) - ρ'.vars "j") ≤
          300 * (offset g ((u : ℕ) + 1) - ρ.vars "j") := by
    rintro ρ ⟨hfr, harr, hinp, hout, hlo, hhi, hseen2, ht1n, ht2n, htog1, hsle,
      hcardρ, hst1, hst2, hsρ, htgρ, VISρ, Qρ, hvisρ, hVISρ, hqρ, hQρ, hQpre,
      htlge, htln⟩ hcond
    have hjendρ : ρ.vars "jend" = offset g ((u : ℕ) + 1) := by
      rw [hfr "jend" (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), hjend]
    have hjlt : ρ.vars "j" < offset g ((u : ℕ) + 1) := by
      have := lt_of_condLt_true hcond
      omega
    have hj2m : ρ.vars "j" < 2 * m := by omega
    have huρ : ρ.vars "u" = (u : ℕ) := by
      rw [hfr "u" (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), hu]
    have htgtρ : ρ.arrs "tgt" = arrOf (2 * m) T := by
      rw [harr "tgt" (by decide) (by decide), htgt]
    have hmarkρ : ρ.arrs "mark" = arrOf n MK := by
      rw [harr "mark" (by decide) (by decide), hmark]
    have hwn : target g (ρ.vars "j") < n := target_lt' hg u.2 hjlt
    obtain ⟨w, hwval⟩ : ∃ w : Fin n, (w : ℕ) = target g (ρ.vars "j") := ⟨⟨_, hwn⟩, rfl⟩
    have hwlt : (w : ℕ) < n := w.2
    have hTj : T (ρ.vars "j") = (w : ℕ) := by rw [hwval]; exact hT _ hj2m
    have hw₁ : (ρ.setVar "w" (w : ℕ)).vars "w" = (w : ℕ) := by simp
    have r₁ : Run B (.assign "w" (.get "tgt" (.var "j"))) ρ (ρ.setVar "w" (w : ℕ)) 3 :=
      (Run.assign (v := (w : ℕ)) (evalB_get (k := ρ.vars "j") (evalB_var (by omega))
        (by rw [htgtρ, getElem?_arrOf T hj2m, hTj]) (by omega))).mono (by simp)
    have hcm : (Cond.eq (.get "mark" (.var "w")) (.lit 0)).evalB B (ρ.setVar "w" (w : ℕ))
        = some (MK (w : ℕ) == 0) := by
      have hev : (Expr.var "w").evalB B (ρ.setVar "w" (w : ℕ)) = some (w : ℕ) := by
        have := evalB_var (B := B) (x := "w") (σ := ρ.setVar "w" (w : ℕ))
          (by rw [hw₁]; omega)
        rwa [hw₁] at this
      exact evalB_condEq (evalB_get (k := (w : ℕ)) hev
        (by rw [arrs_setVar, hmarkρ, getElem?_arrOf MK hwlt]) (hMKB _ hwlt))
        (evalB_lit (by omega))
    by_cases hMKw : MK (w : ℕ) = 0
    · -- **an unmarked target**: the dedup decides what the slot does
      have hwM : w ∉ M := not_mem_of_indicator_eq hMK hwlt hMKw
      have hwmv : target g (ρ.vars "j") ∉ markedVals M := by
        rw [← hwval]; simpa using hwM
      have hres : resTgts g M u (ρ.vars "j" + 1)
          = insert w (resTgts g M u (ρ.vars "j")) := by
        rw [resTgts_succ_of_unmarked (o := u) hlo hwn hwmv]
        congr 1
        exact Fin.ext hwval.symm
      obtain ⟨ρ₂, VIS₂, Q₂, V₂, K₂, r₂, hK₂, hinp₂, hout₂, harr₂, hfr₂, hvis₂, hVIS₂,
          hq₂, hQ₂, hQpre₂, htlge₂, htln₂, htog₂, hseen₂, hcase₂⟩ :=
        dedupCount_run (B := B) (n := n) (V := V ∪ resTgts g M u (ρ.vars "j"))
          (VIS := VISρ) (Q := Qρ) (u := u) (w := w) (head := head) (tl := ρ.vars "tl")
          h1B hnB h2B (by simpa using hvisρ) hVISρ (by simpa using hqρ) hQρ
          (by simpa using huρ) hw₁ (by simp) (by simp; omega) (by simpa using htog1)
          (by simpa using hseen2) (by simp; omega) (by simp; omega)
      have e_seen : (ρ.setVar "w" (w : ℕ)).vars "seen" = ρ.vars "seen" := by simp
      have e_t1 : (ρ.setVar "w" (w : ℕ)).vars "t1" = ρ.vars "t1" := by simp
      have e_t2 : (ρ.setVar "w" (w : ℕ)).vars "t2" = ρ.vars "t2" := by simp
      have e_s : (ρ.setVar "w" (w : ℕ)).vars "s" = ρ.vars "s" := by simp
      have e_tog : (ρ.setVar "w" (w : ℕ)).vars "tog" = ρ.vars "tog" := by simp
      rw [e_seen, e_t1, e_t2, e_s, e_tog] at hcase₂
      have hj₂ : ρ₂.vars "j" = ρ.vars "j" := by
        rw [hfr₂ "j" (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
        simp
      have hjnew : (ρ₂.setVar "j" (ρ.vars "j" + 1)).vars "j" = ρ.vars "j" + 1 := by simp
      have r₃ : Run B (.assign "j" (.add (.var "j") (.lit 1))) ρ₂
          (ρ₂.setVar "j" (ρ.vars "j" + 1)) 4 :=
        (Run.assign (v := ρ.vars "j" + 1) (by simp [hj₂]; omega)).mono (by simp)
      have hrun : Run B solveSlot ρ (ρ₂.setVar "j" (ρ.vars "j" + 1)) 250 :=
        (Run.seq r₁ (Run.seq (Run.ite_true (by rw [hcm]; simp [hMKw]) r₂) r₃)).mono
          (by simp; omega)
      -- the frame conditions, which do not depend on which branch the dedup took
      have hfrρ' : ∀ y, y ≠ "s" → y ≠ "tog" → y ≠ "tl" → y ≠ "seen" → y ≠ "t1" →
          y ≠ "t2" → y ≠ "j" → y ≠ "w" →
          (ρ₂.setVar "j" (ρ.vars "j" + 1)).vars y = σ.vars y := by
        intro y h1 h2 h3 h4 h5 h6 h7 h8
        rw [vars_setVar, if_neg h7, hfr₂ y h1 h2 h3 h4 h5 h6, vars_setVar, if_neg h8]
        exact hfr y h1 h2 h3 h4 h5 h6 h7 h8
      have harrρ' : ∀ a, a ≠ "vis" → a ≠ "q" →
          (ρ₂.setVar "j" (ρ.vars "j" + 1)).arrs a = σ.arrs a := by
        intro a h1 h2
        rw [arrs_setVar, harr₂ a h1 h2, arrs_setVar]
        exact harr a h1 h2
      have hinpρ' : (ρ₂.setVar "j" (ρ.vars "j" + 1)).inp = σ.inp := by
        rw [inp_setVar, hinp₂, inp_setVar]; exact hinp
      have houtρ' : (ρ₂.setVar "j" (ρ.vars "j" + 1)).out = σ.out := by
        rw [out_setVar, hout₂, out_setVar]; exact hout
      have hQpreρ' : ∀ i < tl, Q₂ i = Q i := by
        intro i hi
        rw [hQpre₂ i (by omega), hQpre i hi]
      rcases hcase₂ with ⟨hV₂, hreg, hcnt⟩ | ⟨hρeq, hV₂, hsne, hrep⟩
      · -- a target the block has not shown before
        have hwnot : w ∉ resTgts g M u (ρ.vars "j") := by
          rcases hreg with ⟨hs0, -, -, -⟩ | ⟨hs1, hne, -, -, -⟩
          · have hemp : resTgts g M u (ρ.vars "j") = ∅ :=
              Finset.card_eq_zero.1 (by omega)
            simp [hemp]
          · obtain ⟨x, hx, hxv⟩ := hst1 (by omega)
            rw [eq_singleton_of_card_one (by omega) hx]
            simp only [Finset.mem_singleton]
            rintro rfl
            exact hne hxv
        have hseennew : ρ₂.vars "seen" = ρ.vars "seen" + 1 := by
          rcases hreg with ⟨hs0, hs1, -, -⟩ | ⟨hs1, -, hs2, -, -⟩ <;> omega
        have hcardnew : (resTgts g M u (ρ.vars "j" + 1)).card = ρ₂.vars "seen" := by
          rw [hres, Finset.card_insert_of_notMem hwnot]
          omega
        have hVeq : V ∪ resTgts g M u (ρ.vars "j" + 1) = V₂ := by
          rw [hV₂, hres, Finset.union_insert]
        have hfilt : ((resTgts g M u (ρ.vars "j" + 1)).filter
            (fun x : Fin n => (u : ℕ) < (x : ℕ))).card ≤ 2 := by
          have := Finset.card_filter_le (resTgts g M u (ρ.vars "j" + 1))
            (fun x : Fin n => (u : ℕ) < (x : ℕ))
          omega
        have hcnt' : ((resTgts g M u (ρ.vars "j" + 1)).filter
              (fun x : Fin n => (u : ℕ) < (x : ℕ))).card
            = ((resTgts g M u (ρ.vars "j")).filter
              (fun x : Fin n => (u : ℕ) < (x : ℕ))).card +
                (if (u : ℕ) < (w : ℕ) then 1 else 0) := by
          rw [hres]
          simp only [Finset.filter_insert]
          by_cases hlt : (u : ℕ) < (w : ℕ)
          · rw [if_pos hlt, if_pos hlt, Finset.card_insert_of_notMem
              (fun hmem => hwnot (Finset.mem_of_mem_filter _ hmem))]
          · rw [if_neg hlt, if_neg hlt]
            omega
        have hsnew : ρ₂.vars "s" = σ.vars "s" +
              (((resTgts g M u (ρ.vars "j" + 1)).filter
                (fun x : Fin n => (u : ℕ) < (x : ℕ))).card + 1 - σ.vars "tog") / 2 ∧
            ρ₂.vars "tog" = (((resTgts g M u (ρ.vars "j" + 1)).filter
                (fun x : Fin n => (u : ℕ) < (x : ℕ))).card + σ.vars "tog") % 2 := by
          rw [hcnt']
          rcases hcnt with ⟨hlt, hz, ha, hb⟩ | ⟨hlt, hz, ha, hb⟩ | ⟨hnlt, ha, hb⟩
          · rw [if_pos hlt]; omega
          · rw [if_pos hlt]; omega
          · rw [if_neg hnlt]; omega
        refine ⟨ρ₂.setVar "j" (ρ.vars "j" + 1), 250, hrun,
          ⟨hfrρ', harrρ', hinpρ', houtρ', by rw [hjnew]; omega, by rw [hjnew]; omega,
            by simpa using hseen₂, ?_, ?_, by simpa using htog₂, ?_,
            by rw [hjnew]; simpa using hcardnew, ?_, ?_, ?_, ?_,
            VIS₂, Q₂, by simpa using hvis₂, by rw [hjnew, hVeq]; exact hVIS₂,
            by simpa using hq₂, by rw [hjnew, hVeq]; simpa using hQ₂,
            hQpreρ', by simp; omega, by simpa using htln₂⟩, by simp; omega⟩
        · -- `t1` is a vertex
          rcases hreg with ⟨-, -, ht1', -⟩ | ⟨-, -, -, ht1', -⟩
          · rw [vars_setVar, if_neg (by decide), ht1']; omega
          · rw [vars_setVar, if_neg (by decide), ht1']; omega
        · -- `t2` is a vertex
          rcases hreg with ⟨-, -, -, ht2'⟩ | ⟨-, -, -, -, ht2'⟩
          · rw [vars_setVar, if_neg (by decide), ht2']; omega
          · rw [vars_setVar, if_neg (by decide), ht2']; omega
        · -- `s` has not run away
          rw [vars_setVar, if_neg (show ¬ ("s" = "j") by decide)]
          omega
        · -- the first recorded target is still witnessed
          intro _
          rcases hreg with ⟨-, -, ht1', -⟩ | ⟨hs1, -, -, ht1', -⟩
          · exact ⟨w, by rw [hjnew, hres]; exact Finset.mem_insert_self _ _,
              by rw [vars_setVar, if_neg (by decide), ht1']⟩
          · obtain ⟨x, hx, hxv⟩ := hst1 (by omega)
            exact ⟨x, by rw [hjnew]; exact resTgts_mono (by omega) hx,
              by rw [vars_setVar, if_neg (by decide), ht1', hxv]⟩
        · -- and so is the second, when there is one
          intro h2
          rcases hreg with ⟨-, hs1, -, -⟩ | ⟨hs1, hne, -, ht1', ht2'⟩
          · rw [vars_setVar, if_neg (by decide)] at h2; omega
          · refine ⟨⟨w, by rw [hjnew, hres]; exact Finset.mem_insert_self _ _,
              by rw [vars_setVar, if_neg (by decide), ht2']⟩, ?_⟩
            rw [vars_setVar, if_neg (by decide), vars_setVar, if_neg (by decide),
              ht1', ht2']
            exact fun h => hne h.symm
        · -- the accumulated cost, in closed form
          rw [hjnew, vars_setVar, if_neg (show ¬ ("s" = "j") by decide)]
          exact hsnew.1
        · -- and the toggle
          rw [hjnew, vars_setVar, if_neg (show ¬ ("tog" = "j") by decide)]
          exact hsnew.2
      · -- a repeat: the set of recorded targets does not move
        have hres' : resTgts g M u (ρ.vars "j" + 1) = resTgts g M u (ρ.vars "j") := by
          have hwin : w ∈ resTgts g M u (ρ.vars "j") := by
            rcases hrep with hw1 | ⟨hs2, hw2⟩ | ⟨hs2, hne1, hne2⟩
            · obtain ⟨x, hx, hxv⟩ := hst1 (by omega)
              have : x = w := Fin.ext (by rw [hxv, ← hw1])
              rwa [this] at hx
            · obtain ⟨⟨x, hx, hxv⟩, -⟩ := hst2 hs2
              have : x = w := Fin.ext (by rw [hxv, ← hw2])
              rwa [this] at hx
            · exfalso
              obtain ⟨x1, hx1, hx1v⟩ := hst1 (by omega)
              obtain ⟨⟨x2, hx2, hx2v⟩, hne12⟩ := hst2 hs2
              have hx12 : x1 ≠ x2 := fun h => hne12 (by rw [← hx1v, ← hx2v, h])
              have hpair : resTgts g M u (ρ.vars "j") = {x1, x2} :=
                eq_pair_of_card_two (by omega) hx1 hx2 hx12
              have hwnot : w ∉ resTgts g M u (ρ.vars "j") := by
                rw [hpair]
                simp only [Finset.mem_insert, Finset.mem_singleton]
                rintro (rfl | rfl)
                · exact hne1 hx1v
                · exact hne2 hx2v
              have h3 : (resTgts g M u (ρ.vars "j" + 1)).card = 3 := by
                rw [hres, Finset.card_insert_of_notMem hwnot, hpair,
                  Finset.card_pair hx12]
              have hle := Finset.card_le_card (hsubN (ρ.vars "j" + 1) (by omega))
              rw [h3, ← resDeg_eq_card] at hle
              omega
          rw [hres, Finset.insert_eq_self.2 hwin]
        subst hρeq
        have hVeq : V ∪ resTgts g M u (ρ.vars "j" + 1)
            = V ∪ resTgts g M u (ρ.vars "j") := by rw [hres']
        refine ⟨(ρ.setVar "w" (w : ℕ)).setVar "j" (ρ.vars "j" + 1), 250, hrun,
          ⟨hfrρ', harrρ', hinpρ', houtρ', by rw [hjnew]; omega, by rw [hjnew]; omega,
            by simp; omega, by simp; omega, by simp; omega, by simp; omega,
            by simp; omega, by rw [hjnew, hres']; simp; omega, ?_, ?_, ?_, ?_,
            VIS₂, Q₂, by simpa using hvis₂,
            by rw [hjnew, hres']; rw [hV₂] at hVIS₂; exact hVIS₂,
            by simpa using hq₂,
            by rw [hjnew, hres']; rw [hV₂] at hQ₂; simpa using hQ₂,
            hQpreρ', by simp; omega, by simpa using htln₂⟩, by simp; omega⟩
        · intro h1
          rw [hjnew, hres']
          simp only [vars_setVar, if_neg (show ¬ ("t1" = "j") by decide),
            if_neg (show ¬ ("t1" = "w") by decide)]
          refine hst1 ?_
          simpa using h1
        · intro h2
          rw [hjnew, hres']
          simp only [vars_setVar, if_neg (show ¬ ("t1" = "j") by decide),
            if_neg (show ¬ ("t1" = "w") by decide),
            if_neg (show ¬ ("t2" = "j") by decide),
            if_neg (show ¬ ("t2" = "w") by decide)]
          refine hst2 ?_
          simpa using h2
        · rw [hjnew, hres']
          simpa using hsρ
        · rw [hjnew, hres']
          simpa using htgρ
    · -- **a marked target**: the slot contributes nothing
      have hwM : w ∈ M := mem_of_indicator_ne hMK hwlt hMKw
      have hwmv : target g (ρ.vars "j") ∈ markedVals M := by
        rw [← hwval]; simpa using hwM
      have hres : resTgts g M u (ρ.vars "j" + 1) = resTgts g M u (ρ.vars "j") :=
        resTgts_succ_of_marked (o := u) hwmv
      have hjnew : ((ρ.setVar "w" (w : ℕ)).setVar "j" (ρ.vars "j" + 1)).vars "j"
          = ρ.vars "j" + 1 := by simp
      have r₃ : Run B (.assign "j" (.add (.var "j") (.lit 1))) (ρ.setVar "w" (w : ℕ))
          ((ρ.setVar "w" (w : ℕ)).setVar "j" (ρ.vars "j" + 1)) 4 :=
        (Run.assign (v := ρ.vars "j" + 1)
          (evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega))
            (by simp; omega))).mono (by simp)
      have hrun : Run B solveSlot ρ ((ρ.setVar "w" (w : ℕ)).setVar "j"
          (ρ.vars "j" + 1)) 250 :=
        (Run.seq r₁ (Run.seq (Run.ite_false (by rw [hcm]; simp [hMKw]) Run.skip)
          r₃)).mono (by simp)
      refine ⟨(ρ.setVar "w" (w : ℕ)).setVar "j" (ρ.vars "j" + 1), 250, hrun,
        ⟨?_, ?_, by simp [hinp], by simp [hout], by rw [hjnew]; omega,
          by rw [hjnew]; omega, by simp; omega, by simp; omega, by simp; omega,
          by simp; omega, by simp; omega, by rw [hjnew, hres]; simp; omega, ?_, ?_,
          ?_, ?_, VISρ, Qρ, by simpa using hvisρ, by rw [hjnew, hres]; exact hVISρ,
          by simpa using hqρ, by rw [hjnew, hres]; simpa using hQρ, hQpre,
          by simp; omega, by simpa using htln⟩, by simp; omega⟩
      · intro y h1 h2 h3 h4 h5 h6 h7 h8
        rw [vars_setVar, if_neg h7, vars_setVar, if_neg h8]
        exact hfr y h1 h2 h3 h4 h5 h6 h7 h8
      · intro a h1 h2
        rw [arrs_setVar, arrs_setVar]
        exact harr a h1 h2
      · intro h1
        rw [hjnew, hres]
        simp only [vars_setVar, if_neg (show ¬ ("t1" = "j") by decide),
          if_neg (show ¬ ("t1" = "w") by decide)]
        refine hst1 ?_
        simpa using h1
      · intro h2
        rw [hjnew, hres]
        simp only [vars_setVar, if_neg (show ¬ ("t1" = "j") by decide),
          if_neg (show ¬ ("t1" = "w") by decide),
          if_neg (show ¬ ("t2" = "j") by decide),
          if_neg (show ¬ ("t2" = "w") by decide)]
        refine hst2 ?_
        simpa using h2
      · rw [hjnew, hres]
        simpa using hsρ
      · rw [hjnew, hres]
        simpa using htgρ
  obtain ⟨τ', K, hrun, ⟨hfr', harr', hinp', hout', hlo', hhi', hseen2', ht1n', ht2n',
      htog1', hsle', hcard', hst1', hst2', hs', htg', VIS', Q', hvis', hVIS', hq',
      hQ', hQpre', htlge', htln'⟩, hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := Cond.lt (.var "j") (.var "jend")) (c := solveSlot)
      (RowInv3 g M V u Q head tl (σ.vars "s") (σ.vars "tog") σ)
      (fun ρ => 300 * (offset g ((u : ℕ) + 1) - ρ.vars "j"))
      (fun ρ hρ => by
        obtain ⟨hfr, -, -, -, -, hhi, -⟩ := hρ
        refine evalB_condLt_vars (by omega) ?_
        rw [hfr "jend" (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), hjend]
        omega)
      hstep
      ⟨fun y _ _ _ _ _ _ _ _ => rfl, fun a _ _ => rfl, rfl, rfl, by omega,
        by rw [hj]; exact hstart, by omega, by omega, by omega, htog, by omega,
        by rw [hj, resTgts_start]; simp [hseen],
        by omega, by omega,
        by rw [hj, resTgts_start]; simp only [Finset.filter_empty,
          Finset.card_empty]; omega,
        by rw [hj, resTgts_start]; simp only [Finset.filter_empty,
          Finset.card_empty]; omega,
        VIS, Q, hvis, by rw [hj, resTgts_start]; simpa using hVIS,
        hq, by rw [hj, resTgts_start, htl]; simpa using hQ,
        fun i _ => rfl, by omega, by rw [htl]; exact hQ.tl_le⟩
  have hjend' : τ'.vars "jend" = offset g ((u : ℕ) + 1) := by
    rw [hfr' "jend" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hjend]
  have hjeq : τ'.vars "j" = offset g ((u : ℕ) + 1) := by
    have := le_of_condLt_false hfalse
    omega
  rw [hjeq, resTgts_end (G := G) (M := M) (o := u) hg] at hVIS' hQ' hs' htg'
  refine ⟨τ', VIS', Q', K, hrun, hinp', hout', harr', hfr', hvis', hVIS', hq', hQ',
    hQpre', htlge', htln', hs', htg', ?_⟩
  have hΦ : 300 * (offset g ((u : ℕ) + 1) - σ.vars "j")
      = 300 * (offset g ((u : ℕ) + 1) - offset g (u : ℕ)) := by rw [hj]
  simp only [size_condLt, size_var] at hpay
  omega

/-! ### Clearing the visited array

Every solver call starts by zeroing `vis`; only the first could skip it,
since fresh arrays are zeroed. -/

/-- **The clearing pass.** One walk over `vis` writes `0` everywhere,
leaving the visited set empty and nothing but the counter moved. -/
theorem clearVis_run (h1B : 1 < B) (hnB : n < B) {VIS : ℕ → ℕ} {σ : Env}
    (hvis : σ.arrs "vis" = arrOf n VIS) (hn : σ.vars "n" = n) :
    ∃ (τ' : Env) (VIS' : ℕ → ℕ) (K : ℕ), Run B clearVis σ τ' K ∧
      τ'.inp = σ.inp ∧ τ'.out = σ.out ∧
      (∀ a, a ≠ "vis" → τ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "i" → τ'.vars y = σ.vars y) ∧
      τ'.arrs "vis" = arrOf n VIS' ∧ Indicator (∅ : Finset (Fin n)) VIS' ∧
      K ≤ 20 * n + 10 := by
  have r₀ : Run B (.assign "i" (.lit 0)) σ (σ.setVar "i" 0) 2 :=
    (Run.assign (v := 0) (evalB_lit (by omega))).mono (by simp)
  obtain ⟨τ', K, hrun, ⟨hfr, harr, hinp, hout, hile, VIS', hvis', hzero⟩,
      hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := Cond.lt (.var "i") (.var "n"))
      (σ := σ.setVar "i" 0)
      (c := .seq (.store "vis" (.var "i") (.lit 0))
        (.assign "i" (.add (.var "i") (.lit 1))))
      (fun ν => (∀ y, y ≠ "i" → ν.vars y = σ.vars y) ∧
        (∀ a, a ≠ "vis" → ν.arrs a = σ.arrs a) ∧ ν.inp = σ.inp ∧ ν.out = σ.out ∧
        ν.vars "i" ≤ n ∧ ∃ VIS', ν.arrs "vis" = arrOf n VIS' ∧
          ∀ x < ν.vars "i", VIS' x = 0)
      (fun ν => 20 * (n - ν.vars "i"))
      (fun ν hν => by
        obtain ⟨hfr, -, -, -, hile, -⟩ := hν
        refine evalB_condLt_vars (by omega) ?_
        rw [hfr "n" (by decide), hn]
        omega)
      (by
        rintro ν ⟨hfr, harr, hinp, hout, hile, VISν, hvisν, hzero⟩ hcond
        have hnν : ν.vars "n" = n := by rw [hfr "n" (by decide), hn]
        have hilt : ν.vars "i" < n := by
          have := lt_of_condLt_true hcond
          omega
        refine ⟨(ν.setArr "vis" (ν.vars "i") 0).setVar "i" (ν.vars "i" + 1), 7,
          (Run.seq (Run.store (idx := ν.vars "i") (v := 0) (evalB_var (by omega))
              (evalB_lit (by omega)) (by rw [hvisν, length_arrOf]; exact hilt))
            (Run.assign (v := ν.vars "i" + 1) (by simp; omega))).mono (by simp),
          ⟨?_, ?_, by simp [hinp], by simp [hout], by simp; omega,
            fun x => if x = ν.vars "i" then 0 else VISν x, ?_, ?_⟩, by simp; omega⟩
        · intro y hy
          rw [vars_setVar, if_neg hy, vars_setArr]
          exact hfr y hy
        · intro a ha
          rw [arrs_setVar, arrs_setArr, if_neg ha]
          exact harr a ha
        · rw [arrs_setVar, arrs_setArr, if_pos rfl, hvisν, set_arrOf]
        · intro x hx
          rw [vars_setVar, if_pos rfl] at hx
          by_cases hxi : x = ν.vars "i"
          · simp [hxi]
          · simp only [if_neg hxi]
            exact hzero x (by omega))
      ⟨fun y hy => by simp [hy], fun a _ => by simp, by simp, by simp, by simp,
        VIS, by simpa using hvis, by simp⟩
  have hin : τ'.vars "i" = n := by
    have h1 : τ'.vars "n" = n := by rw [hfr "n" (by decide), hn]
    have := le_of_condLt_false hfalse
    omega
  refine ⟨τ', VIS', 20 * n + 10, (Run.seq r₀ hrun).mono ?_, hinp, hout, harr, hfr,
    hvis', ?_, le_rfl⟩
  · simp only [size_condLt, size_var] at hpay
    omega
  · intro x hx
    rw [if_neg (Finset.notMem_empty _)]
    exact hzero x (by omega)

/-! ### One dequeued vertex

`expandBody3_run` is `rowScan3_run` with the block set up: the queue
gives the vertex, the offset array gives the two ends of its block, and
the per-row registers are reset. -/

/-- Moving the head past a vertex that is on the queue. -/
theorem Queue.advance {V : Finset (Fin n)} {Q : ℕ → ℕ} {head tl : ℕ}
    (h : Queue V Q head tl) (hh : head + 1 ≤ tl) : Queue V Q (head + 1) tl :=
  ⟨h.card, hh, h.mem, h.all, h.inj⟩

/-- **One turn of the drain.** The vertex at the head of the queue is
dequeued and its whole block scanned: the visited set and the queue grow
by its residual neighbourhood and the toggle counts its upward edges. -/
theorem expandBody3_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ p < 2 * m, T p = target g p)
    (h1B : 1 < B) (h2B : 2 < B) (hnB : n + 1 < B) (hmB : 2 * m < B)
    {V : Finset (Fin n)} {MK VIS Q : ℕ → ℕ} {head tl : ℕ} {σ : Env}
    (hthin : ∀ v : Fin n, v ∉ M → resDeg G M v ≤ 2) (hVM : ∀ v ∈ V, v ∉ M)
    (hoff : σ.arrs "off" = arrOf (n + 1) O)
    (hmark : σ.arrs "mark" = arrOf n MK) (hMK : Indicator M MK)
    (htgt : σ.arrs "tgt" = arrOf (2 * m) T)
    (hvis : σ.arrs "vis" = arrOf n VIS) (hVIS : Indicator V VIS)
    (hq : σ.arrs "q" = arrOf n Q) (hQ : Queue V Q head tl)
    (hhead : σ.vars "head" = head) (htl : σ.vars "tl" = tl) (hlt : head < tl)
    (htog : σ.vars "tog" ≤ 1) (hsB : σ.vars "s" + 2 < B) :
    ∃ (τ' : Env) (VIS' Q' : ℕ → ℕ) (u : Fin n) (K : ℕ),
      Run B expandBody3 σ τ' K ∧ (u : ℕ) = Q head ∧ u ∈ V ∧
      τ'.inp = σ.inp ∧ τ'.out = σ.out ∧
      (∀ a, a ≠ "vis" → a ≠ "q" → τ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "s" → y ≠ "tog" → y ≠ "tl" → y ≠ "seen" → y ≠ "t1" → y ≠ "t2" →
        y ≠ "j" → y ≠ "w" → y ≠ "u" → y ≠ "jend" → y ≠ "head" →
        τ'.vars y = σ.vars y) ∧
      τ'.vars "head" = head + 1 ∧
      τ'.arrs "vis" = arrOf n VIS' ∧ Indicator (V ∪ ResNbhd G M u) VIS' ∧
      τ'.arrs "q" = arrOf n Q' ∧
      Queue (V ∪ ResNbhd G M u) Q' (head + 1) (τ'.vars "tl") ∧
      (∀ i < tl, Q' i = Q i) ∧ tl ≤ τ'.vars "tl" ∧ τ'.vars "tl" ≤ n ∧
      τ'.vars "s" = σ.vars "s" +
        (((ResNbhd G M u).filter (fun x : Fin n => (u : ℕ) < (x : ℕ))).card + 1 -
          σ.vars "tog") / 2 ∧
      τ'.vars "tog" =
        (((ResNbhd G M u).filter (fun x : Fin n => (u : ℕ) < (x : ℕ))).card +
          σ.vars "tog") % 2 ∧
      τ'.vars "tog" ≤ 1 ∧
      K ≤ 300 * (offset g ((u : ℕ) + 1) - offset g (u : ℕ)) + 60 := by
  classical
  obtain ⟨u, huval, huV⟩ := hQ.mem head (by omega)
  have huM : u ∉ M := hVM u huV
  have hun : (u : ℕ) < n := u.2
  have htln : tl ≤ n := hQ.tl_le
  have hOu : O (u : ℕ) = offset g (u : ℕ) := hO _ (by omega)
  have hOu1 : O ((u : ℕ) + 1) = offset g ((u : ℕ) + 1) := hO _ (by omega)
  have hoffu : offset g (u : ℕ) ≤ 2 * m := by
    have := offset_le hg (show (u : ℕ) ≤ n by omega); omega
  have hoffu1 : offset g ((u : ℕ) + 1) ≤ 2 * m := by
    have := offset_le hg (show (u : ℕ) + 1 ≤ n by omega); omega
  -- the six assignments that set the block up
  have hsetup : ∃ ρ : Env, ρ.arrs = σ.arrs ∧ ρ.inp = σ.inp ∧ ρ.out = σ.out ∧
      (∀ y, y ≠ "u" → y ≠ "j" → y ≠ "jend" → y ≠ "seen" → y ≠ "t1" → y ≠ "t2" →
        ρ.vars y = σ.vars y) ∧
      ρ.vars "u" = (u : ℕ) ∧ ρ.vars "j" = offset g (u : ℕ) ∧
      ρ.vars "jend" = offset g ((u : ℕ) + 1) ∧ ρ.vars "seen" = 0 ∧
      ρ.vars "t1" = 0 ∧ ρ.vars "t2" = 0 ∧
      ∀ (c : Com) (ρ'' : Env) (Kc : ℕ), Run B c ρ ρ'' Kc →
        Run B (.seq (.assign "u" (.get "q" (.var "head")))
          (.seq (.assign "j" (.get "off" (.var "u")))
            (.seq (.assign "jend" (.get "off" (.add (.var "u") (.lit 1))))
              (.seq (.assign "seen" (.lit 0))
                (.seq (.assign "t1" (.lit 0)) (.seq (.assign "t2" (.lit 0)) c))))))
          σ ρ'' (25 + Kc) := by
    refine ⟨(((((σ.setVar "u" (u : ℕ)).setVar "j" (offset g (u : ℕ))).setVar "jend"
        (offset g ((u : ℕ) + 1))).setVar "seen" 0).setVar "t1" 0).setVar "t2" 0,
      by simp, by simp, by simp, ?_, by simp, by simp, by simp,
      by simp, by simp, by simp, ?_⟩
    · intro y h1 h2 h3 h4 h5 h6
      simp [h1, h2, h3, h4, h5, h6]
    · intro c ρ'' Kc hc
      refine (Run.seq (Run.assign (v := (u : ℕ)) (evalB_get (k := head)
          (by rw [← hhead]; exact evalB_var (by omega))
          (by rw [hq, getElem?_arrOf Q (show head < n by omega), huval]) (by omega)))
        (Run.seq (Run.assign (v := offset g (u : ℕ)) (evalB_get (k := (u : ℕ))
            (evalB_var (by simp; omega))
            (by simp only [arrs_setVar]; rw [hoff, getElem?_arrOf O (by omega), hOu])
            (by omega)))
          (Run.seq (Run.assign (v := offset g ((u : ℕ) + 1))
              (evalB_get (k := (u : ℕ) + 1)
              (evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega))
                (by simp; omega))
              (by simp only [arrs_setVar]; rw [hoff, getElem?_arrOf O (by omega), hOu1])
              (by omega)))
            (Run.seq (Run.assign (v := 0) (evalB_lit (by omega)))
              (Run.seq (Run.assign (v := 0) (evalB_lit (by omega)))
                (Run.seq (Run.assign (v := 0) (evalB_lit (by omega))) hc)))))).mono ?_
      simp
      omega
  obtain ⟨σ₆, harr₆, hinp₆, hout₆, hfr₆, hu₆, hj₆, hjend₆, hseen₆, ht1₆, ht2₆,
    hcont⟩ := hsetup
  obtain ⟨τ₀, VIS', Q', K₀, hrun₀, hinp₀, hout₀, harr₀, hfr₀, hvis₀, hVIS₀, hq₀,
      hQ₀, hQpre₀, htlge₀, htln₀, hs₀, htg₀, hK₀⟩ :=
    rowScan3_run (B := B) (V := V) (u := u) (MK := MK) (VIS := VIS) (Q := Q)
      (head := head) (tl := tl) (σ := σ₆) hg hm hT h1B h2B (by omega) hmB
      (hthin u huM) (by rw [harr₆]; exact hmark) hMK (by rw [harr₆]; exact htgt)
      (by rw [harr₆]; exact hvis) hVIS (by rw [harr₆]; exact hq) hQ
      (by rw [hfr₆ "tl" (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact htl)
      hu₆ hj₆ hjend₆ hseen₆ ht1₆ ht2₆
      (by rw [hfr₆ "tog" (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact htog)
      (by rw [hfr₆ "s" (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hsB)
  have hhead₀ : τ₀.vars "head" = head := by
    rw [hfr₀ "head" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      hfr₆ "head" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hhead
  have r₇ : Run B (.assign "head" (.add (.var "head") (.lit 1))) τ₀
      (τ₀.setVar "head" (head + 1)) 4 :=
    (Run.assign (v := head + 1) (by simp [hhead₀]; omega)).mono (by simp)
  refine ⟨τ₀.setVar "head" (head + 1), VIS', Q', u,
    300 * (offset g ((u : ℕ) + 1) - offset g (u : ℕ)) + 60,
    (hcont _ _ _ (Run.seq hrun₀ r₇)).mono (by omega),
    huval, huV, ?_, ?_, ?_, ?_, by simp,
    by simpa using hvis₀, hVIS₀, by simpa using hq₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    le_rfl⟩
  · rw [inp_setVar, hinp₀, hinp₆]
  · rw [out_setVar, hout₀, hout₆]
  · intro a h1 h2
    rw [arrs_setVar, harr₀ a h1 h2, harr₆]
  · intro y h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    rw [vars_setVar, if_neg h11, hfr₀ y h1 h2 h3 h4 h5 h6 h7 h8,
      hfr₆ y h9 h7 h10 h4 h5 h6]
  · rw [show (τ₀.setVar "head" (head + 1)).vars "tl" = τ₀.vars "tl" by simp]
    exact hQ₀.advance (by omega)
  · exact hQpre₀
  · rw [show (τ₀.setVar "head" (head + 1)).vars "tl" = τ₀.vars "tl" by simp]
    exact htlge₀
  · rw [show (τ₀.setVar "head" (head + 1)).vars "tl" = τ₀.vars "tl" by simp]
    exact htln₀
  · rw [vars_setVar, if_neg (show ¬ ("s" = "head") by decide), hs₀,
      hfr₆ "s" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hfr₆ "tog" (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]
  · rw [vars_setVar, if_neg (show ¬ ("tog" = "head") by decide), htg₀,
      hfr₆ "tog" (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]
  · rw [vars_setVar, if_neg (show ¬ ("tog" = "head") by decide), htg₀]
    omega

/-! ### What becomes of these lemmas

The two loops around `expandBody3` and the block that holds them are in
`Sweep3.lean`: `drain3_run` (the queue-reading potential and the pure
identity `∑_{v ∈ C} upDeg v = (compEdges C).card`), `rootSweep_run`, and
`solve_run`, which runs the whole of `solveBlock`, final `ite`
included, so that the outer body consumes it with a single `Run.seq`. -/

end Lax15Proofs.VC3