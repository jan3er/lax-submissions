import Lax13Proofs.Refine.NREST.Pw

/-!
The executable gate for the NREST layer.

Campaign rule D4 of `plans/word-ram/refinement-tower/design.md`: every
layer gets executable instances and property checks *the day it lands*,
and the repo's standing practice is to try to refute an obligation
before proving it. This file is that gate for `Basic.lean` and
`Pw.lean`: the monad laws and `bindT_mono` are run, at a finite carrier,
against sampled data.

## Why there are executable twins

`sSup` on `NRest` is a classical `if` on set membership, so `bindT` is
`noncomputable`, and mathlib's `CompleteLattice ℕ∞` is `noncomputable`
too, which makes `⊤`, `⊥` and `⊔` on `NRest _ ℕ∞` non-executable even
though their *definitions* are plain matches. `#guard` and `#test`
compile the term they check, so neither can be pointed at `bindT`
directly.

The route taken is the one the campaign brief sanctions: a small
executable model of each operation at the carrier
`NRest (Fin 3) ℕ∞` — `returnE`, `specE`, `consumeBE`, `joinE`, `bindE` —
each with a *proved* agreement theorem tying it to the real operation.
The checks below therefore test the real statements: `bindE_eq` and
friends are theorems, so a counterexample to a law stated with `bindE`
is a counterexample to the law itself.

Nothing here is used by any other module; it is a gate, not a library.
-/

namespace Lax13Proofs.Refine

open Plausible

namespace Sanity

/-- The sanity carrier: three results, costs in `ℕ∞` (the source's
`enat`). Small enough to enumerate, big enough that associativity has
something to say. -/
abbrev SRest := NRest (Fin 3) ℕ∞

/-! ### Decidability at the sanity carrier -/

/-- Equality is decidable: result maps out of `Fin 3` into
`WithBot ℕ∞ = Option (Option ℕ)` are finite data. -/
instance instDecidableEqSRest : DecidableEq SRest := fun m n =>
  match m, n with
  | .fail, .fail => isTrue rfl
  | .fail, .rest _ => isFalse (by simp)
  | .rest _, .fail => isFalse (by simp)
  | .rest X, .rest Y => decidable_of_iff (X = Y) (by simp)

/-- And so is the order, by the three clauses of `less_eq_nrest`. -/
instance instDecidableLESRest : DecidableLE SRest := fun m n =>
  match m, n with
  | _, .fail => isTrue (NRest.le_fail _)
  | .fail, .rest _ => isFalse (by simp)
  | .rest X, .rest Y => decidable_of_iff (∀ i, X i ≤ Y i) (by simp [Pi.le_def])

/-! ### Executable twins, and their agreement with the real operations -/

/-- `⨆` over `Fin 3`, unfolded — the shape `bindE` computes in. -/
theorem iSup_fin3 {A : Type} [CompleteLattice A] (g : Fin 3 → A) :
    (⨆ i, g i) = g 0 ⊔ g 1 ⊔ g 2 := by
  refine le_antisymm (iSup_le fun i => ?_)
    (sup_le (sup_le (le_iSup g 0) (le_iSup g 1)) (le_iSup g 2))
  fin_cases i
  · exact le_sup_of_le_left le_sup_left
  · exact le_sup_of_le_left le_sup_right
  · exact le_sup_right

/-- Executable `⊔`, decided by the (computable) order. -/
def joinE (m n : SRest) : SRest :=
  match m, n with
  | .fail, _ => .fail
  | _, .fail => .fail
  | .rest a, .rest b => .rest (fun i => if a i ≤ b i then b i else a i)

@[simp] theorem joinE_fail_left (n : SRest) : joinE .fail n = .fail := rfl

@[simp] theorem joinE_fail_right (a : Fin 3 → WithBot ℕ∞) :
    joinE (.rest a) .fail = .fail := rfl

@[simp] theorem joinE_rest (a b : Fin 3 → WithBot ℕ∞) :
    joinE (.rest a) (.rest b) = .rest (fun i => if a i ≤ b i then b i else a i) := rfl

theorem joinE_eq (m n : SRest) : joinE m n = m ⊔ n := by
  cases m with
  | fail => simp
  | rest a =>
    cases n with
    | fail => simp
    | rest b =>
      rw [joinE_rest, NRest.sup_eq_join, NRest.join_rest, NRest.rest_inj_iff]
      funext i
      rw [Pi.sup_apply]
      split
      · exact (sup_eq_right.mpr ‹_›).symm
      · exact (sup_eq_left.mpr (le_of_not_ge ‹_›)).symm

/-- Executable `returnT`. -/
def returnE (x : Fin 3) : SRest := .rest (fun v => if v = x then (0 : WithBot ℕ∞) else ⊥)

theorem returnE_eq (x : Fin 3) : returnE x = NRest.returnT x := by
  rw [returnE, NRest.returnT, NRest.rest_inj_iff]
  funext v
  rw [NRest.single_eq_ite]

/-- Executable `spec`, over a `Bool`-valued predicate. -/
def specE (P : Fin 3 → Bool) (t : Fin 3 → ℕ∞) : SRest :=
  .rest (fun v => if P v then ((t v : ℕ∞) : WithBot ℕ∞) else ⊥)

theorem specE_eq (P : Fin 3 → Bool) (t : Fin 3 → ℕ∞) :
    specE P t = NRest.spec (fun v => P v = true) t := by
  rw [specE, NRest.spec, NRest.rest_inj_iff]
  funext v
  by_cases h : P v = true <;> simp [h]

/-- Executable `consumeB`. -/
def consumeBE (m : SRest) (u : WithBot ℕ∞) : SRest :=
  u.recBotCoe (.rest (fun _ => ⊥)) (fun t => NRest.consume m t)

@[simp] theorem consumeBE_bot (m : SRest) : consumeBE m ⊥ = .rest (fun _ => ⊥) := rfl

@[simp] theorem consumeBE_coe (m : SRest) (t : ℕ∞) :
    consumeBE m (t : WithBot ℕ∞) = NRest.consume m t := rfl

theorem consumeBE_eq (m : SRest) (u : WithBot ℕ∞) : consumeBE m u = NRest.consumeB m u := by
  rcases withBot_eq_bot_or_coe u with rfl | ⟨t, rfl⟩
  · rw [consumeBE_bot, NRest.consumeB_bot, NRest.bot_eq_rest_bot, NRest.rest_inj_iff]
    rfl
  · rw [consumeBE_coe, NRest.consumeB_coe]

/-- Executable `bindT`: the supremum of `bindT_rest_eq_iSup`, unfolded
over the three results. -/
def bindE (m : SRest) (f : Fin 3 → SRest) : SRest :=
  match m with
  | .fail => .fail
  | .rest X =>
    joinE (joinE (consumeBE (f 0) (X 0)) (consumeBE (f 1) (X 1))) (consumeBE (f 2) (X 2))

@[simp] theorem bindE_fail (f : Fin 3 → SRest) : bindE .fail f = .fail := rfl

@[simp] theorem bindE_rest (X : Fin 3 → WithBot ℕ∞) (f : Fin 3 → SRest) :
    bindE (.rest X) f =
      joinE (joinE (consumeBE (f 0) (X 0)) (consumeBE (f 1) (X 1)))
        (consumeBE (f 2) (X 2)) := rfl

/-- **The bridge.** Everything checked below is checked about `bindT`. -/
theorem bindE_eq (m : SRest) (f : Fin 3 → SRest) : bindE m f = NRest.bindT m f := by
  cases m with
  | fail => rfl
  | rest X =>
    rw [NRest.bindT_rest_eq_iSup, iSup_fin3, bindE_rest, joinE_eq, joinE_eq,
      consumeBE_eq, consumeBE_eq, consumeBE_eq]

/-! ### Spot checks

Concrete computations, kernel-checked at elaboration time. -/

/-- A sample result map: result `0` at cost `1`, result `1` unreachable,
result `2` at cost `5`. -/
def sampleX : Fin 3 → WithBot ℕ∞ := ![((1 : ℕ∞) : WithBot ℕ∞), ⊥, ((5 : ℕ∞) : WithBot ℕ∞)]

/-- A sample continuation. -/
def sampleF : Fin 3 → SRest := ![returnE 2, .fail, .rest ![⊥, ((2 : ℕ∞) : WithBot ℕ∞), ⊥]]

-- `consume` adds on the left, and `⊥` stays `⊥`.
#guard NRest.consume ((NRest.rest sampleX : SRest)) 2
  = .rest ![((3 : ℕ∞) : WithBot ℕ∞), ⊥, ((7 : ℕ∞) : WithBot ℕ∞)]

#guard NRest.consume ((NRest.rest sampleX : SRest)) 0 = .rest sampleX

-- left identity, at three sample continuations
#guard bindE (returnE 0) sampleF = sampleF 0
#guard bindE (returnE 1) sampleF = sampleF 1
#guard bindE (returnE 2) sampleF = sampleF 2

-- right identity
#guard bindE ((NRest.rest sampleX : SRest)) returnE = (NRest.rest sampleX : SRest)
#guard bindE (NRest.fail : SRest) returnE = (NRest.fail : SRest)

-- one result of `sampleF` fails, and the bound computation can reach it,
-- so the bind fails
#guard bindE (.rest ![⊥, ((1 : ℕ∞) : WithBot ℕ∞), ⊥]) sampleF = (NRest.fail : SRest)

-- and if it cannot reach it, the bind is a `rest`
#guard bindE (.rest ![((1 : ℕ∞) : WithBot ℕ∞), ⊥, ⊥]) sampleF
  = .rest ![⊥, ⊥, ((1 : ℕ∞) : WithBot ℕ∞)]

-- `spec` against `returnT`: `returnT x` is below any `spec` admitting
-- `x`, and not below one that does not
#guard returnE 1 ≤ specE (fun _ => true) (fun _ => 0)
#guard ¬ (returnE 1 ≤ specE (fun v => v = 0) (fun _ => 0))
#guard returnE 1 ≤ specE (fun v => v = 1) (fun _ => 7)

-- associativity, on samples
#guard bindE (bindE ((NRest.rest sampleX : SRest)) sampleF) sampleF
  = bindE ((NRest.rest sampleX : SRest)) (fun x => bindE (sampleF x) sampleF)

/-! ### Property checks

Plausible over sampled result maps. The proxy is
`Option (List (ℕ × ℕ))`: `none` gives `fail`, and a list of
`(result, cost)` pairs is written into an all-`⊥` map, so both
`fail` and arbitrary partial maps are sampled. -/

/-- The index `n mod 3`. -/
def mk3 (n : ℕ) : Fin 3 := ⟨n % 3, by omega⟩

/-- Build a result map from a list of `(result, cost)` pairs. -/
def mapOfPairs : List (ℕ × ℕ) → (Fin 3 → WithBot ℕ∞)
  | [] => fun _ => ⊥
  | (a, c) :: l => Function.update (mapOfPairs l) (mk3 a) (((c : ℕ) : ℕ∞) : WithBot ℕ∞)

@[simp] theorem mapOfPairs_nil : mapOfPairs [] = fun _ => ⊥ := rfl

@[simp] theorem mapOfPairs_cons (a c : ℕ) (l : List (ℕ × ℕ)) :
    mapOfPairs ((a, c) :: l) =
      Function.update (mapOfPairs l) (mk3 a) (((c : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl

/-- The sampling proxy for `SRest`. -/
def ofProxy : Option (List (ℕ × ℕ)) → SRest
  | none => .fail
  | some l => .rest (mapOfPairs l)

@[simp] theorem ofProxy_none : ofProxy none = (NRest.fail : SRest) := rfl

@[simp] theorem ofProxy_some (l : List (ℕ × ℕ)) : ofProxy (some l) = .rest (mapOfPairs l) := rfl

/-- Sampling: `none` gives `fail`, a list of `(result, cost)` pairs is
written into an all-`⊥` map. -/
instance instSampleableExtSRest : SampleableExt SRest where
  proxy := Option (List (ℕ × ℕ))
  sample := inferInstance
  interp := ofProxy

-- Left identity: `bindT (returnT x) f = f x`.
#test ∀ (n : ℕ) (f₀ f₁ f₂ : SRest),
  bindE (returnE (mk3 n)) ![f₀, f₁, f₂] = ![f₀, f₁, f₂] (mk3 n)

-- Right identity: `bindT M returnT = M`.
#test ∀ M : SRest, bindE M returnE = M

-- Associativity: `bindT (bindT M f) g = bindT M (fun x => bindT (f x) g)`.
#test ∀ (M f₀ f₁ f₂ g₀ g₁ g₂ : SRest),
  bindE (bindE M ![f₀, f₁, f₂]) ![g₀, g₁, g₂]
    = bindE M (fun x => bindE (![f₀, f₁, f₂] x) ![g₀, g₁, g₂])

-- `bindT_mono`, guarded form.
#test ∀ (M M' f₀ f₁ f₂ g₀ g₁ g₂ : SRest),
  M ≤ M' → f₀ ≤ g₀ → f₁ ≤ g₁ → f₂ ≤ g₂ →
    bindE M ![f₀, f₁, f₂] ≤ bindE M' ![g₀, g₁, g₂]

-- `bindT_mono`, in the hypothesis-free form its premises are always
-- satisfiable in: joining can only increase a bind.
#test ∀ (M M' f₀ f₁ f₂ g₀ g₁ g₂ : SRest),
  bindE M ![f₀, f₁, f₂]
    ≤ bindE (joinE M M') (fun x => joinE (![f₀, f₁, f₂] x) (![g₀, g₁, g₂] x))

-- `consume` is monotone in both arguments.
#test ∀ (M M' : SRest) (s t : ℕ),
  M ≤ M' → s ≤ t → NRest.consume M (s : ℕ∞) ≤ NRest.consume M' (t : ℕ∞)

end Sanity

end Lax13Proofs.Refine
