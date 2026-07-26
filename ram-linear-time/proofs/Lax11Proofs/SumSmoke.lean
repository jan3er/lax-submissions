import Lax11.RamComputes
import Lax11Proofs.Simulation

/-!
The P1 chain, end to end, on one algorithm: an IMP+ program that reads
a length-prefixed word and writes its sum runs on the machine within a
linear time bound.

This is a test of the tower, not of the algorithm. It is written at the
level P1 offers — a big-step derivation built by hand, with the loop
done by induction on the remaining input — precisely to record what
that costs before P2 and P3 exist to make it pleasant. Everything about
the constants is deliberately crude: 21 units of IMP+ cost per input
number, times the layout's 22 machine steps per unit, gives 462, and
nothing is tight anywhere.
-/

namespace Lax11Proofs.SumSmoke

open Lax11.Ram Lax11.RamComputes Lax11Proofs.Imp Lax11Proofs.Compile
open Lax11Proofs.Simulation

/-- `i < n`, the loop condition. -/
def loopCond : Cond := .lt (.var "i") (.var "n")

/-- Read the next number, add it to the running sum, count it. -/
def body : Com :=
  .seq (.read "v")
    (.seq (.assign "s" (.add (.var "s") (.var "v")))
      (.assign "i" (.add (.var "i") (.lit 1))))

/-- The loop. -/
def loop : Com := .while loopCond body

/-- Read the count, then that many numbers, then write their sum. -/
def sumCom : Com :=
  .seq (.read "n")
    (.seq (.assign "i" (.lit 0))
      (.seq (.assign "s" (.lit 0))
        (.seq loop (.write (.var "s")))))

/-- Four scalars, no arrays, two temporaries. -/
def layout : Layout := ⟨["n", "i", "s", "v"], [], 2⟩

/-- The machine program. -/
def sumProgram : Program := compileProgram layout sumCom

theorem sumCom_ok : Com.Ok layout sumCom := by
  simp only [sumCom, loop, body, loopCond, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]
  refine ⟨by simp, ⟨by simp, by simp⟩, ⟨by simp, by simp⟩,
    ⟨⟨⟨by simp, by simp, by simp⟩, trivial, by simp⟩, by simp,
      ⟨by simp, by simp, by simp⟩, by simp, by simp⟩, by simp, by simp⟩

theorem const_eq : layout.const = 22 := by
  simp [Layout.const, Layout.idxLen, layout]

/-- The loop: whatever the input still holds, it is read, counted and
summed, at a cost of at most 14 per number. Induction on the input that
is left, which is the loop's variant. -/
theorem loop_bigStep : ∀ (rest : List ℕ) (σ : Env), σ.inp = rest →
    σ.vars "n" = σ.vars "i" + rest.length →
    ∃ (σ' : Env) (k : ℕ), BigStep loop σ σ' k ∧ k ≤ 14 * (rest.length + 1) ∧
      σ'.vars "s" = σ.vars "s" + rest.sum ∧ σ'.out = σ.out := by
  intro rest
  induction rest with
  | nil =>
      intro σ _ hn
      refine ⟨σ, 4, BigStep.while_false ?_, by omega, by simp, rfl⟩
      simp [loopCond, Cond.eval, Expr.eval, hn]
  | cons v rest ih =>
      intro σ hinp hn
      have hlt : loopCond.eval σ = some true := by
        simp [loopCond, Cond.eval, Expr.eval, hn]
      have hb₁ : BigStep (.read "v") σ { σ.setVar "v" v with inp := rest } 1 :=
        BigStep.read (by rw [hinp])
      set σ₁ : Env := { σ.setVar "v" v with inp := rest } with hσ₁
      have hb₂ : BigStep (.assign "s" (.add (.var "s") (.var "v"))) σ₁
          (σ₁.setVar "s" (σ.vars "s" + v)) 4 := by
        refine BigStep.assign ?_
        simp [Expr.eval, hσ₁, Env.setVar]
      set σ₂ : Env := σ₁.setVar "s" (σ.vars "s" + v) with hσ₂
      have hb₃ : BigStep (.assign "i" (.add (.var "i") (.lit 1))) σ₂
          (σ₂.setVar "i" (σ.vars "i" + 1)) 4 := by
        refine BigStep.assign ?_
        simp [Expr.eval, hσ₂, hσ₁, Env.setVar]
      set σ₃ : Env := σ₂.setVar "i" (σ.vars "i" + 1) with hσ₃
      obtain ⟨σ', k, hk, hkle, hs, hout⟩ := ih σ₃ (by simp [hσ₃, hσ₂, hσ₁, Env.setVar])
        (by simp [hσ₃, hσ₂, hσ₁, Env.setVar] at hn ⊢; omega)
      refine ⟨σ', 13 + k, BigStep.while_true hlt (BigStep.seq hb₁ (BigStep.seq hb₂ hb₃)) hk,
        by simp; omega, ?_, ?_⟩
      · rw [hs]
        simp [hσ₃, hσ₂, hσ₁, Env.setVar]
        omega
      · rw [hout]
        simp [hσ₃, hσ₂, hσ₁, Env.setVar]

/-- The whole program: on a length-prefixed word, the derivation
exists, it costs at most `21 * (|x| + 1)`, and it writes the sum. -/
theorem sumCom_bigStep (xs : List ℕ) :
    ∃ (σ' : Env) (k : ℕ),
      BigStep sumCom (initEnv (fun _ => 0) (xs.length :: xs)) σ' k ∧
      k ≤ 21 * ((xs.length :: xs).length + 1) ∧ σ'.out = [xs.sum] := by
  set σ₀ : Env := initEnv (fun _ => 0) (xs.length :: xs) with hσ₀
  have hb₁ : BigStep (.read "n") σ₀ { σ₀.setVar "n" xs.length with inp := xs } 1 :=
    BigStep.read rfl
  set σ₁ : Env := { σ₀.setVar "n" xs.length with inp := xs } with hσ₁
  have hb₂ : BigStep (.assign "i" (.lit 0)) σ₁ (σ₁.setVar "i" 0) 2 := BigStep.assign rfl
  set σ₂ : Env := σ₁.setVar "i" 0 with hσ₂
  have hb₃ : BigStep (.assign "s" (.lit 0)) σ₂ (σ₂.setVar "s" 0) 2 := BigStep.assign rfl
  set σ₃ : Env := σ₂.setVar "s" 0 with hσ₃
  obtain ⟨σ', k, hk, hkle, hs, hout⟩ := loop_bigStep xs σ₃ (by simp [hσ₃, hσ₂, hσ₁, Env.setVar])
    (by simp [hσ₃, hσ₂, hσ₁, hσ₀, initEnv, Env.setVar])
  have hb₅ : BigStep (.write (.var "s")) σ' { σ' with out := σ'.out ++ [σ'.vars "s"] } 2 :=
    BigStep.write rfl
  refine ⟨{ σ' with out := σ'.out ++ [σ'.vars "s"] }, _,
    BigStep.seq hb₁ (BigStep.seq hb₂ (BigStep.seq hb₃ (BigStep.seq hk hb₅))), ?_, ?_⟩
  · simp only [List.length_cons]; omega
  · show σ'.out ++ [σ'.vars "s"] = _
    rw [hout, hs]
    simp [hσ₃, hσ₂, hσ₁, hσ₀, initEnv, Env.setVar]

/-- **The chain, end to end.** The compiled machine program computes
the sum of a length-prefixed word within `462 * (|x| + 1)` steps. The
constant comes from `21` units of IMP+ cost per input number and the
layout's `22` machine steps per unit; the time is the machine's own
step count. -/
theorem sumProgram_computesInTime :
    ComputesInTime sumProgram {x : List ℕ | ∃ xs, x = xs.length :: xs}
      (fun x => [x.tail.sum]) (fun x => 462 * (x.length + 1)) := by
  rintro x ⟨xs, rfl⟩
  obtain ⟨σ', k, hbs, hk, hout⟩ := sumCom_bigStep xs
  obtain ⟨t, ht, hrun⟩ := compileProgram_runsTo sumCom_ok hbs
  refine ⟨t, ?_, ?_⟩
  · rw [const_eq] at ht
    calc t ≤ 22 * k := ht
      _ ≤ 22 * (21 * ((xs.length :: xs).length + 1)) := Nat.mul_le_mul_left _ hk
      _ = 462 * ((xs.length :: xs).length + 1) := by ring
  · simpa [hout] using hrun

end Lax11Proofs.SumSmoke
