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

/-- The eight scalars the descend scan moves. -/
def Scanned3 (y : String) : Prop :=
  y = "j" ∨ y = "u" ∨ y = "w" ∨ y = "found" ∨ y = "v" ∨ y = "seen" ∨ y = "t1" ∨ y = "t2"

instance : DecidablePred Scanned3 := fun y => by unfold Scanned3; infer_instance

/-- What a frame condition against `Scanned3` gives, one name at a
time. -/
theorem not_scanned3_ne {y : String} (h : ¬ Scanned3 y) :
    y ≠ "j" ∧ y ≠ "u" ∧ y ≠ "w" ∧ y ≠ "found" ∧ y ≠ "v" ∧ y ≠ "seen" ∧ y ≠ "t1" ∧
      y ≠ "t2" := by
  simp only [Scanned3, not_or] at h
  exact h

/-- The invariant of the descend scan. Beyond the frame conditions and
the position of the owner: while the flag is down the registers
describe the current block exactly (`SeenInv`), and the flag is the
dichotomy — nothing branchable below the pointer, or a named vertex of
residual degree at least three. -/
def ScanInv3 (g : List ℕ) {n : ℕ} (m : ℕ) (G : SimpleGraph (Fin n)) (M : Finset (Fin n))
    (σ τ : Env) : Prop :=
  (∀ y, ¬ Scanned3 y → τ.vars y = σ.vars y) ∧ τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧
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
three, which is what the deeper branch spends its budget on. -/
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
      refine ⟨ν', 12, (Run.seq (Run.assign (v := ν.vars "u" + 1) (by simp; omega))
          (Run.seq (Run.assign (v := 0) (by simp; omega))
            (Run.seq (Run.assign (v := 0) (by simp; omega))
              (Run.assign (v := 0) (by simp; omega))))).mono (by simp), ⟨⟨?_, ?_,
        by simp [hν', hinp], by simp [hν', hout], by simp [hν']; omega,
        by simp [hν'], by simp [hν'], by simp [hν'],
        by omega, by rw [hvu, hvj, heq], ?_, by omega, ?_, ?_⟩, by rw [hvj, hjν]⟩, ?_⟩
      · intro y hy
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := not_scanned3_ne hy
        simp only [hν', vars_setVar, if_neg h8, if_neg h7, if_neg h6, if_neg h2]
        exact hfr y hy
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
      Run.while_pot (B := B)
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
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := not_scanned3_ne hy
        rw [hv y h1 h3]
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
        refine ⟨ρ₄.setVar "j" (ρ₁.vars "j" + 1), K₁ + 200, Run.seq r₁ ((Run.seq
          (Run.ite_true hcu (Run.seq rw₁ (Run.ite_true hcw r₄)))
          (Run.assign (v := ρ₁.vars "j" + 1) (by
            simp [hj₄]; omega))).mono (by simp; omega)), ?_, ?_⟩
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
          exact ⟨fun y hy => by
              obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := not_scanned3_ne hy
              rw [hfrall y h1 h3 h6 h7 h8 h4 h5]
              exact hfr y hy,
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
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := not_scanned3_ne hy
      simp [hσ₀, h1, h2, h4, h6, h7, h8]
    · simp [hσ₀, hg.offset_zero]
    · simp [hσ₀]
    · intro _ o ho _
      exact ⟨fun p _ hp2 _ => absurd hp2 (by simp [hσ₀]),
        fun hs => absurd hs (by simp [hσ₀]), fun hs => absurd hs (by simp [hσ₀])⟩
    · refine Or.inl ⟨by simp [hσ₀], ?_⟩
      intro o _ p₁ p₂ p₃ _ _ hc₁
      exact absurd hc₁ (by simp [hσ₀])
  obtain ⟨τ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_pot (B := B) (b := Cond.lt (.var "j") (.var "m2"))
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

end Lax15Proofs.VC3
