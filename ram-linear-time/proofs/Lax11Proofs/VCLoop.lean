import Lax11Proofs.VCScan

/-!
The outer loop: one transition lemma for the body, then the loop rule.

`Rep` says what the arrays and scalars hold when the pure configuration
is `C`: the stack arrays list the frames bottom-up — entry `i` is frame
`i` counted from the bottom, which is `C.frames.reverse[i]`, since the
pure stack keeps its top at the head — and the mark array is the
indicator of the marked set. The invariant handed to the loop rule is
"some configuration is represented, and it satisfies `Inv`".

The loop potential must be a total function of the environment, so it
cannot read the pure configuration; `phasesOf` reads the phase list
back off the stack array — garbage off the invariant is fine, since
only invariant states are ever compared — and `potN` mirrors `pot` on
it. On represented states the two agree, which is the one lemma that
crosses between the numeric and the pure potential.

Each body case builds its `Run` by hand, hands the new configuration to
the matching preservation lemma of `VCSpec`, and pays the loop rule out
of the matching drop lemma. The descend cases contain the scan; their
cost is `≤ 100m + 50n + 100`, which is why the loop potential carries
the factor `100m + 50n + 104`.
-/

namespace Lax11Proofs.VC

open Lax11.Ram Lax11.GraphEncoding
open Lax11Proofs.Imp Lax11Proofs.Compile Lax11Proofs.Reasoning Lax11Proofs.CC

variable {g : List ℕ} {n m k : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}

/-! ### Representation -/

/-- The arrays and scalars represent the configuration `C`: the CSR
arrays hold the encoding, the mode, budget, answer and stack pointer
are the configuration's, the mark array is the indicator of the marked
set, and the stack arrays list the frames bottom-up. -/
def Rep (n m k : ℕ) (O T : ℕ → ℕ) (C : Config n) (τ : Env) : Prop :=
  τ.vars "m2" = 2 * m ∧
  τ.arrs "off" = arrOf (n + 1) O ∧ τ.arrs "tgt" = arrOf (2 * m) T ∧
  τ.vars "mode" = C.mode ∧ τ.vars "bud" = C.bud ∧ τ.vars "ans" = C.ans ∧
  τ.vars "top" = C.frames.length ∧
  (∃ MK, τ.arrs "mark" = arrOf n MK ∧
    ∀ w (hw : w < n), MK w = if (⟨w, hw⟩ : Fin n) ∈ marked C.frames then 1 else 0) ∧
  (∃ SU SV SP, τ.arrs "stkU" = arrOf k SU ∧ τ.arrs "stkV" = arrOf k SV ∧
    τ.arrs "stkP" = arrOf k SP ∧
    ∀ i (hi : i < C.frames.length),
      SU i = ((C.frames.reverse[i]'(by simpa using hi)).u : ℕ) ∧
      SV i = ((C.frames.reverse[i]'(by simpa using hi)).v : ℕ) ∧
      SP i = if (C.frames.reverse[i]'(by simpa using hi)).ph then 1 else 0)

/-- Reading the top frame out of the bottom-up array order. -/
theorem reverse_getElem_top (f : Frame n) (fs : List (Frame n)) :
    (f :: fs).reverse[fs.length]'(by simp) = f := by
  simp

/-- Reading a lower frame past a push, in the bottom-up order. -/
theorem reverse_getElem_lt (f : Frame n) {fs : List (Frame n)} {i : ℕ}
    (hi : i < fs.length) :
    (f :: fs).reverse[i]'(by simp; omega) = fs.reverse[i]'(by simpa using hi) := by
  simp only [List.reverse_cons]
  rw [List.getElem_append_left (by simpa using hi)]

/-- An indicator that is not `0` witnesses membership. -/
theorem mem_of_indicator_ne {MK : ℕ → ℕ} {fs : List (Frame n)}
    (hMK : ∀ w (hw : w < n), MK w = if (⟨w, hw⟩ : Fin n) ∈ marked fs then 1 else 0)
    {w : ℕ} (hw : w < n) (h : MK w ≠ 0) : (⟨w, hw⟩ : Fin n) ∈ marked fs := by
  by_contra hmem
  rw [hMK w hw, if_neg hmem] at h
  exact h rfl

/-- An indicator that is `0` witnesses non-membership. -/
theorem not_mem_of_indicator_eq {MK : ℕ → ℕ} {fs : List (Frame n)}
    (hMK : ∀ w (hw : w < n), MK w = if (⟨w, hw⟩ : Fin n) ∈ marked fs then 1 else 0)
    {w : ℕ} (hw : w < n) (h : MK w = 0) : (⟨w, hw⟩ : Fin n) ∉ marked fs := by
  intro hmem
  rw [hMK w hw, if_pos hmem] at h
  exact absurd h one_ne_zero

/-! ### The numeric potential -/

/-- The stack potential read off the phase list alone. -/
def stackPotB : List Bool → ℕ → ℕ
  | [], _ => 0
  | ph :: phs, b => (if ph then 1 else fPot b + 2) + stackPotB phs (b + 1)

theorem stackPot_eq_stackPotB (fs : List (Frame n)) (b : ℕ) :
    stackPot fs b = stackPotB (fs.map Frame.ph) b := by
  induction fs generalizing b with
  | nil => rfl
  | cons f fs ih => simp [stackPot, stackPotB, ih]

/-- The potential as a function of what the environment holds: mode,
budget, and the phase list. -/
def potN (mode bud : ℕ) (phs : List Bool) : ℕ :=
  (if mode = 0 then fPot bud else 0) + stackPotB phs bud + (if mode = 2 then 0 else 1)

theorem pot_eq_potN (C : Config n) :
    pot C = potN C.mode C.bud (C.frames.map Frame.ph) := by
  simp [pot, potN, stackPot_eq_stackPotB]

/-- The phase list, read back off the stack array top-first. Total on
every environment; meaningful on represented ones. -/
def phasesOf (τ : Env) : List Bool :=
  (List.range (τ.vars "top")).map
    (fun i => (τ.arrs "stkP").getD (τ.vars "top" - 1 - i) 0 == 1)

/-- On a represented state the numeric phase list is the pure one. -/
theorem phasesOf_eq {C : Config n} {τ : Env} (hRep : Rep n m k O T C τ)
    (hlen : C.frames.length ≤ k) :
    phasesOf τ = C.frames.map Frame.ph := by
  obtain ⟨-, -, -, -, -, -, htop, -, SU, SV, SP, -, -, hstkP, hstk⟩ := hRep
  refine List.ext_getElem (by simp [phasesOf, htop]) fun i h₁ h₂ => ?_
  simp only [phasesOf, List.getElem_map, List.getElem_range, List.length_map,
    List.length_range] at h₁ h₂ ⊢
  rw [htop] at h₁ ⊢
  have hik : C.frames.length - 1 - i < k := by omega
  have hil : C.frames.length - 1 - i < C.frames.length := by omega
  rw [hstkP, getD_arrOf SP hik, (hstk _ hil).2.2]
  have hrev : (C.frames.reverse[C.frames.length - 1 - i]'(by simpa using hil)) =
      C.frames[i]'h₂ := by
    rw [List.getElem_reverse]
    congr 1
    omega
  rw [hrev]
  cases hph : (C.frames[i]'h₂).ph <;> simp

/-- On a represented state the numeric potential is the pure one. -/
theorem potN_eq {C : Config n} {τ : Env} (hRep : Rep n m k O T C τ)
    (hlen : C.frames.length ≤ k) :
    potN (τ.vars "mode") (τ.vars "bud") (phasesOf τ) = pot C := by
  rw [hRep.2.2.2.1, hRep.2.2.2.2.1, phasesOf_eq hRep hlen, ← pot_eq_potN]

end Lax11Proofs.VC
