import Lax3.DistFO
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The arithmetic of the horizon functions `rhoMinus`, `rhoPlus` of
`Lax3.DistFO`: the source's defining inequalities (eq. 1 of
arXiv:2606.23180), the exact identity ρ⁺(k,q) = 9^k · ρ⁻(k,q) that the
concrete pair satisfies, monotonicity in each argument and along the
antidiagonal (the direction quantifier steps move in), and the derived
chain ρ⁻(k+1,q) ≤ ρ⁺(k+1,q) ≤ ρ⁻(k,q+1). Everything the locality-engine
proofs use about the two functions is here; no proof elsewhere unfolds
the `9 ^ _` normal forms.
-/

namespace Lax3Proofs.Horizon

open Lax3.DistFO

/-- Horizon values are positive. -/
theorem one_le_rhoMinus (k q : ℕ) : 1 ≤ rhoMinus k q :=
  Nat.one_le_pow _ _ (by norm_num)

/-- Horizon values are positive. -/
theorem one_le_rhoPlus (k q : ℕ) : 1 ≤ rhoPlus k q :=
  Nat.one_le_pow _ _ (by norm_num)

/-- The concrete pair satisfies the second condition of the source's
eq. (1) with equality: ρ⁺(k,q) = 9^k · ρ⁻(k,q). -/
theorem rhoPlus_eq (k q : ℕ) : rhoPlus k q = 9 ^ k * rhoMinus k q := by
  rw [rhoPlus, rhoMinus, ← pow_add]
  congr 1
  ring

/-- The second condition of the source's eq. (1):
ρ⁺(k,q) ≥ 9^k · ρ⁻(k,q). -/
theorem nine_pow_mul_rhoMinus_le_rhoPlus (k q : ℕ) :
    9 ^ k * rhoMinus k q ≤ rhoPlus k q :=
  (rhoPlus_eq k q).ge

/-- Powers of nine: a sum of two is dominated by any strictly higher
power. The one shape of arithmetic the eq.-(1) inequality needs. -/
theorem nine_pow_add_nine_pow_le {a b e : ℕ} (ha : a + 1 ≤ e) (hb : b + 1 ≤ e) :
    9 ^ a + 9 ^ b ≤ 9 ^ e := by
  have key : ∀ {c d : ℕ}, c ≤ d → d + 1 ≤ e → 9 ^ c + 9 ^ d ≤ 9 ^ e := by
    intro c d hcd hde
    calc 9 ^ c + 9 ^ d ≤ 9 ^ d + 9 ^ d :=
          Nat.add_le_add_right (Nat.pow_le_pow_right (by norm_num) hcd) _
      _ ≤ 9 * 9 ^ d := by omega
      _ = 9 ^ (d + 1) := (pow_succ 9 d).symm ▸ (mul_comm _ _)
      _ ≤ 9 ^ e := Nat.pow_le_pow_right (by norm_num) hde
  rcases le_total a b with h | h
  · exact key h hb
  · rw [Nat.add_comm]
    exact key h ha

/-- The first condition of the source's eq. (1):
ρ⁻(k,q) ≥ ρ⁺(k+1,q−1) + ρ⁻(k+1,q−1), stated at `q + 1` so no
subtraction appears. -/
theorem rhoPlus_add_rhoMinus_le (k q : ℕ) :
    rhoPlus (k + 1) q + rhoMinus (k + 1) q ≤ rhoMinus k (q + 1) := by
  rw [rhoPlus, rhoMinus, rhoMinus]
  exact nine_pow_add_nine_pow_le (by nlinarith) (by nlinarith)

/-- ρ⁻ is monotone in both arguments. -/
theorem rhoMinus_mono {k k' q q' : ℕ} (hk : k ≤ k') (hq : q ≤ q') :
    rhoMinus k q ≤ rhoMinus k' q' :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul (by omega) hq)

/-- ρ⁺ is monotone in both arguments. -/
theorem rhoPlus_mono {k k' q q' : ℕ} (hk : k ≤ k') (hq : q ≤ q') :
    rhoPlus k q ≤ rhoPlus k' q' :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul (by omega) (by omega))

/-- ρ⁻ grows along the antidiagonal: trading a free variable for a
quantifier never shrinks the horizon. -/
theorem rhoMinus_succ_left_le (k q : ℕ) : rhoMinus (k + 1) q ≤ rhoMinus k (q + 1) :=
  Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- ρ⁺ grows along the antidiagonal. -/
theorem rhoPlus_succ_left_le (k q : ℕ) : rhoPlus (k + 1) q ≤ rhoPlus k (q + 1) :=
  Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- ρ⁻ is below ρ⁺ at every rank. -/
theorem rhoMinus_le_rhoPlus (k q : ℕ) : rhoMinus k q ≤ rhoPlus k q :=
  Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- The derived chain: one rank level in, ρ⁺ is still below ρ⁻ one
level out. -/
theorem rhoPlus_le_rhoMinus (k q : ℕ) : rhoPlus (k + 1) q ≤ rhoMinus k (q + 1) :=
  le_trans (Nat.le_add_right _ _) (rhoPlus_add_rhoMinus_le k q)

/-- The strict form of the chain, which the source states as
ρ⁺(k+1,q−1) < ρ⁻(k,q). -/
theorem rhoPlus_lt_rhoMinus (k q : ℕ) : rhoPlus (k + 1) q < rhoMinus k (q + 1) :=
  lt_of_lt_of_le
    (Nat.lt_add_of_pos_right (one_le_rhoMinus (k + 1) q))
    (rhoPlus_add_rhoMinus_le k q)

end Lax3Proofs.Horizon
