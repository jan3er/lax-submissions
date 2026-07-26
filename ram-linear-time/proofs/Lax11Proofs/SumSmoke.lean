import Lax11Proofs.Reasoning

/-!
The chain, end to end, on one algorithm: an IMP+ program that reads a
length-prefixed word and writes its sum runs on the machine within a
linear time bound.

This is a test of the tower, not of the algorithm, and it is the
measurement that decides whether the reasoning kit was worth building.
The same three theorems were first proved directly against the big-step
semantics (git history, rev 5 of the plan): a derivation built by hand
for every command, the loop by induction on the remaining input, every
intermediate environment named, and the cost of every construct matched
on the nose and repaired afterwards by `omega`. That came to 59 lines
of tactic script, and the constant came out at `462 * (|x| + 1)`.

Here it is 34, and what is left is the algorithm rather than the
semantics: the invariant, the argument that the loop exits with the
input consumed, and the arithmetic of the bound. The loop is one
application of `Run.while_count`; the straight-line code is four rule
applications with the environments inferred; the constant — now
`286 * (|x| + 1)`, smaller because slack is taken once instead of at
every construct — falls out of `computesInTime_of_run`.
-/

namespace Lax11Proofs.SumSmoke

open Lax11.Ram Lax11.RamComputes Lax11Proofs.Imp Lax11Proofs.Compile
open Lax11Proofs.Reasoning

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

/-- The loop invariant, relative to the environment `σ₀` in which the
loop is entered: the counter has the input still to be read left to go,
the sum of what was read is already in `s`, and nothing was written. -/
def Inv (σ₀ τ : Env) : Prop :=
  τ.vars "n" = τ.vars "i" + τ.inp.length ∧
  τ.vars "s" + τ.inp.sum = σ₀.vars "s" + σ₀.inp.sum ∧
  τ.out = σ₀.out

/-- The loop: whatever the input still holds is read, counted and
summed, at a cost of at most 13 per number. The variant is the input
that is left; one application of the counted while rule. -/
theorem loop_run (σ₀ : Env) (hn : σ₀.vars "n" = σ₀.vars "i" + σ₀.inp.length) :
    ∃ σ', Run loop σ₀ σ' (13 * σ₀.inp.length + 4) ∧
      σ'.vars "s" = σ₀.vars "s" + σ₀.inp.sum ∧ σ'.out = σ₀.out := by
  have hstep : ∀ τ : Env, Inv σ₀ τ → loopCond.eval τ = some true →
      ∃ τ', Run body τ τ' 9 ∧ Inv σ₀ τ' ∧ τ'.inp.length < τ.inp.length := by
    rintro τ ⟨hn', hs', hout'⟩ hcond
    have hlt : τ.vars "i" < τ.vars "n" := by
      simpa [loopCond] using hcond
    obtain ⟨v, rest, hinp⟩ : ∃ v rest, τ.inp = v :: rest := by
      rcases h : τ.inp with _ | ⟨v, rest⟩
      · rw [h] at hn'; simp at hn'; omega
      · exact ⟨v, rest, rfl⟩
    refine ⟨_, (Run.seq (Run.read hinp)
        (Run.seq (Run.assign (v := τ.vars "s" + v) (by simp))
          (Run.assign (v := τ.vars "i" + 1) (by simp)))).mono
        (by simp), ⟨?_, ?_, ?_⟩, ?_⟩
    · simp [hinp] at hn' ⊢; omega
    · simp [hinp] at hs' ⊢; omega
    · simpa using hout'
    · simp [hinp]
  obtain ⟨σ', hrun, ⟨hn'', hs'', hout''⟩, hfalse⟩ :=
    Run.while_count (b := loopCond) (c := body) (Inv σ₀) (fun τ => τ.inp.length) 9
      (fun τ _ => ⟨_, rfl⟩) hstep ⟨hn, rfl, rfl⟩
  have hexit : ¬ σ'.vars "i" < σ'.vars "n" := by
    simpa [loopCond] using hfalse
  have hnil : σ'.inp = [] := by
    rcases h : σ'.inp with _ | ⟨v, rest⟩
    · rfl
    · rw [h] at hn''; simp at hn''; omega
  refine ⟨σ', hrun.mono (by simp [loopCond]), ?_, hout''⟩
  rw [hnil] at hs''; simpa using hs''

/-- **The chain, end to end.** The compiled machine program computes
the sum of a length-prefixed word within `286 * (|x| + 1)` steps, in
the machine's own step count. Three lines of arithmetic: the IMP+ cost
of the run is `13 * |xs| + 11`, the layout costs `22` machine steps per
unit of it, and `22 * (13 * |xs| + 11) ≤ 286 * (|xs| + 2)`. -/
theorem sumProgram_computesInTime :
    ComputesInTime sumProgram {x : List ℕ | ∃ xs, x = xs.length :: xs}
      (fun x => [x.tail.sum]) (fun x => 286 * (x.length + 1)) := by
  refine computesInTime_of_run sumCom_ok ?_
  rintro x ⟨xs, rfl⟩
  set σ₀ : Env := initEnv (fun _ => 0) (xs.length :: xs) with hσ₀
  obtain ⟨σ', hloop, hs, hout⟩ :=
    loop_run (({ σ₀.setVar "n" xs.length with inp := xs }.setVar "i" 0).setVar "s" 0)
      (by simp [hσ₀, initEnv])
  refine ⟨fun _ => 0, _, _, Run.seq (Run.read rfl)
    (Run.seq (Run.assign (v := 0) rfl)
      (Run.seq (Run.assign (v := 0) rfl)
        (Run.seq hloop (Run.write (v := σ'.vars "s") rfl)))), ?_, ?_⟩
  · show σ'.out ++ [σ'.vars "s"] = _
    rw [hout, hs]; simp [hσ₀, initEnv]
  · rw [const_eq]; simp [hσ₀, initEnv]; omega

end Lax11Proofs.SumSmoke
