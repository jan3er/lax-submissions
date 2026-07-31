import Lax3Proofs.RamDriverRoot
import Lax3Proofs.TgtCoupling

/-!
**Wave B7's gate: two compiled findings that block the C0 discharge.**

C0 (`Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking`)
hands the program a word `x` with `Lax11.GraphEncoding.EncodesGraph x n G`
*alone* and asks for cost `c · (|x| + 1) ^ (1 + ε)` at every `ε > 0`.
The brief's assembly route is `RamDriverRoot.driverRoot_decides_sentence`
(30 slots, all producered) → `Spec` → `ComputesInTime`. Both findings are
compiled against those slots verbatim, in the house style of
`Refine.CostShapeProbe` (the frozen interface's floor) and
`TgtWidenProbe` (the fold gates): the refutation is checked before any
assembly is attempted, and it is the record.

**Finding 1 — `EncodesGraph` does not produce `CsrSimple` (slot #6).**
The encoding *deliberately* permits a block to name a neighbour twice
(`Lax11.GraphEncoding`'s notes say so in words), and the root theorem's
`hcsr : RamElim.CsrSimple G ns O T` — wave D4's "data of the word" —
forbids exactly that: the two eliminations of the ordering phase read a
degree off a row, so a duplicate slot inflates a degree and the greedy
minimality the cover-degree chain stands on is about the wrong number.
`dupWord` below is a genuine `EncodesGraph` word for `K₂` whose first
row lists vertex `1` twice; `encodesGraph_not_csrSimple` is the
headline. Consequence: `CsrSimple` cannot be *assumed* at the C0
boundary, where the input predicate is `EncodesGraph` alone — the
driver needs a dedup guard between the decode and the first level
(`driverRoot = decodeCom ; driverAt 0 ; sentenceCom`, so the splice
point exists and `driver_correct`'s decode slot is already a
hypothesis), or an equivalent repair. Options are itemized in the wave
report and the plan ledger.

**Finding 2 — the landed cost interface has an `Ω(n·W)` floor, and
`W ≥ chainWidth ≥ n² + 1` at the `R = R*` the mass bound needs.**
`level_interface_floor` is proved from three hypotheses of
`driverRoot_decides_sentence` *verbatim* — `hKs` (#20), `hKo` (#22),
`hKl` (#27) — for every instantiation of every free parameter: any
level budget `Kl` those side conditions admit at `ℓ ≥ 2` pays
`n · (60·W + 1600·n) ≤ Kl 0 n`. The mechanism is the plan's own R1.6
touched-only debt surfacing at the composition: `hKo` charges the
ordering phase at *carrier* width (`orderPhaseCost n ns W =
1600·n + 1350·ns + 60·W + 650`) at **every** arena, including the empty
one, and `hKl`'s turn sum runs up to `m = n` turns each of which pays a
nested level (`turnCost` carries `Kin` additively). So even at
`W = ns` the interface floor is `1600·n²` — over C0's bound for every
`ε < 1` on sparse class members — and on the C0 cost path the width is
not `ns`: the mass bound needs `R = R* > 0` (`integration-design.md`
§2.3, compiled there), `orderImplementsR`'s `hWc` pins
`chainWidth n d D₁ R ≤ W`, and `chainWidth` carries an `n · n` term for
the level's own graph, so the floor is `60·n³`
(`level_interface_floor_cubic`). No parameter split can land that under
`c · (|x| + 1) ^ (1 + ε)`: on a sparse member `|x| ≤ 3·n + 3`, and the
`#guard` at the bottom checks `60·n³ > c · (3·n + 4)²` — the `ε = 1`
budget at a generous constant — at one large instance; `c` is chosen
before `n`, so the quantifier order does the rest.

The floor is not only in the hypothesis shapes: the *program* pays it
too — `orderCom R W j` opens with `saveCsr`, which copies `.lit W`
cells at every level entry (rebase F-c-4), and a level can be entered
`n` times per depth. That half is a paper argument, exactly as the F1
program floor was (`integration-design.md` §2.2); this file compiles
the interface shadow, which is what the assembly would have had to
consume.

Repairs (owner decisions; itemized in the wave report): block-driven
nested order/cover/base phases (R1.6/R1.8, the plan's own deferred
items) for the `1600·n²` half, and live-width (`≤ 2·n·budget`-sized)
save/restore plus a degree-aware `chainWidth` for the `60·n³` half.
-/

namespace Lax3Proofs.C0Probe

open Lax11.GraphEncoding

/-! ### Finding 1: a duplicate-bearing `EncodesGraph` word

`dupWord` encodes `K₂` with `edgeCount = 2`: row 0 is `[1, 1]` — vertex
`1` listed twice — and row 1 is `[0, 0]`. Every clause of
`EncodesGraph` holds (`adj_iff` only *exists* a slot), and
`CsrSimple`'s `nodup` fails at row 0. -/

/-- `K₂`, encoded with each row repeating its neighbour: header `2, 2`,
offsets `0, 2, 4`, targets `1, 1, 0, 0`. -/
def dupWord : List ℕ := [2, 2, 0, 2, 4, 1, 1, 0, 0]

-- the duplicate, cell by cell
#guard edgeCount dupWord = 2
#guard target dupWord 0 = 1
#guard target dupWord 1 = 1

/-- **`dupWord` is a genuine encoding of `K₂`.** Repetition is not a
defect of the word: the encoding's `adj_iff` is an existential, and the
concept's own notes state that repetitions are deliberately not
forbidden. -/
theorem encodesGraph_dupWord : EncodesGraph dupWord 2 (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro u v
  rw [SimpleGraph.top_adj]
  constructor
  · intro hne
    fin_cases u <;> fin_cases v
    · exact absurd rfl hne
    · exact ⟨0, by decide, by decide, by decide⟩
    · exact ⟨2, by decide, by decide, by decide⟩
    · exact absurd rfl hne
  · rintro ⟨j, h1, h2, h3⟩
    fin_cases u <;> fin_cases v
    · have hj : j < 2 := lt_of_lt_of_le h2 (by decide)
      interval_cases j
      · exact absurd h3 (by decide)
      · exact absurd h3 (by decide)
    · decide
    · decide
    · have hj2 : 2 ≤ j := le_trans (by decide) h1
      have hj4 : j < 4 := lt_of_lt_of_le h2 (by decide)
      interval_cases j
      · exact absurd h3 (by decide)
      · exact absurd h3 (by decide)

/-- **The same word fails `CsrSimple`** at the instantiation the root
theorem reads it at (`O = offset x`, `T = target x`,
`ns = 2 · edgeCount x`): row 0's slots `0` and `1` both name vertex
`1`. -/
theorem not_csrSimple_dupWord :
    ¬ RamElim.CsrSimple (⊤ : SimpleGraph (Fin 2)) 4 (offset dupWord) (target dupWord) := by
  intro h
  have h01 := h.nodup 0 (by omega) 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  omega

/-- **Finding 1, headline.** `EncodesGraph` does not imply the root
theorem's `hcsr` slot: there is a word encoding a graph whose decoded
block structure is not `CsrSimple`. So no producer can close slot #6
from C0's input predicate, and the driver needs a dedup guard (or an
equivalent repair) before C0 can be discharged. -/
theorem encodesGraph_not_csrSimple :
    ∃ (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)),
      EncodesGraph x n G ∧
        ¬ RamElim.CsrSimple G (2 * edgeCount x) (offset x) (target x) := by
  refine ⟨dupWord, 2, ⊤, encodesGraph_dupWord, ?_⟩
  have h4 : 2 * edgeCount dupWord = 4 := by decide
  rw [h4]
  exact not_csrSimple_dupWord

/-! ### Finding 2: the interface floor of the landed root theorem

The three hypotheses below are `driverRoot_decides_sentence`'s `hKs`,
`hKo` and `hKl`, byte for byte (`B` does not occur in them). The floor
holds for *every* instantiation of every free parameter — in
particular for every candidate discharge of C0 through the landed
theorem. -/

/-- **The carrier-width phase floor.** Any `Kl` admitted by the landed
side conditions at `ℓ ≥ 2` pays the ordering phase's carrier-width cost
on `n` turns: `n · (60·W + 1600·n) ≤ Kl 0 n`. The route: `hKl` at
`j = 1, m = 0` makes the nested level pay `orderPhaseCost n ns W` on
the *empty* arena (`hKo` is size-blind — the R1.6 debt); `hKs` makes a
turn pay its nested level (`turnCost` carries `Kin` additively); `hKl`
at `j = 0, m = t = n` runs `n` such turns (all block sizes zero, so the
mass side condition is free — the floor is not about the mass). -/
theorem level_interface_floor
    {n q_top cap mb ns W ℓ Kmass : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}
    (hℓ : 2 ≤ ℓ)
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      RamDriverRoot.turnCostSize n ns cap mb q_top j φ (Ksc j) t (Kl (j + 1) t) ≤ Ks j t)
    (hKo : ∀ j m, RamDriverCompose.orderPhaseCost n ns W ≤ Ko j m)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m) :
    n * (60 * W + 1600 * n) ≤ Kl 0 n := by
  -- the nested level pays the ordering phase on the empty arena
  have h10 : RamDriverCompose.orderPhaseCost n ns W ≤ Kl 1 0 := by
    have h := hKl 1 (by omega) 0 0 le_rfl (fun _ => 0) (by simp)
    simp only [Finset.range_zero, Finset.sum_empty] at h
    exact le_trans (hKo 1 0) (le_trans (Nat.le_add_right _ _) h)
  -- a turn pays its nested level
  have hks : Kl 1 0 ≤ Ks 0 0 := by
    have h := hKs 0 (by omega) 0
    simp only [Nat.zero_add] at h
    rw [RamDriverRoot.turnCostSize_eq] at h
    refine le_trans ?_ h
    simp only [RamDriverRoot.turnCost]
    omega
  -- the level at the root runs `n` turns
  have h0 := hKl 0 (by omega) n n le_rfl (fun _ => 0) (by simp)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h0
  have hP : n * (Ks 0 0 + 11) ≤ Kl 0 n :=
    calc n * (Ks 0 0 + 11)
        ≤ n * (Ks 0 0 + 11) + 6 := Nat.le_add_right _ _
      _ ≤ Kd 0 n + (n * (Ks 0 0 + 11) + 6) := Nat.le_add_left _ _
      _ ≤ Kc 0 n + (Kd 0 n + (n * (Ks 0 0 + 11) + 6)) := Nat.le_add_left _ _
      _ ≤ Ko 0 n + (Kc 0 n + (Kd 0 n + (n * (Ks 0 0 + 11) + 6))) := Nat.le_add_left _ _
      _ ≤ Kl 0 n := h0
  have hop : 60 * W + 1600 * n ≤ RamDriverCompose.orderPhaseCost n ns W := by
    simp only [RamDriverCompose.orderPhaseCost]
    omega
  calc n * (60 * W + 1600 * n)
      ≤ n * (Ks 0 0 + 11) :=
        mul_le_mul_right (le_trans hop (le_trans h10 (le_trans hks (Nat.le_add_right _ _)))) n
    _ ≤ Kl 0 n := hP

/-- **The floor at the C0 cost path.** The mass bound needs `R = R* > 0`
(`integration-design.md` §2.3), `orderImplementsR`'s `hWc` then pins
`chainWidth n d D₁ R ≤ W`, and `chainWidth` carries `n · n` for the
level's own graph — so the composed cost is at least `60 · n³`. C0's
budget on a sparse class member (`|x| ≤ 3·n + 3`) is
`c · (3·n + 4) ^ (1 + ε)` with `c` chosen before `n`: cubic loses to it
at no `ε < 2`. -/
theorem level_interface_floor_cubic
    {n q_top cap mb ns W ℓ Kmass d D₁ R : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}
    (hℓ : 2 ≤ ℓ)
    (hWc : TgtCoupling.chainWidth n d D₁ R ≤ W)
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      RamDriverRoot.turnCostSize n ns cap mb q_top j φ (Ksc j) t (Kl (j + 1) t) ≤ Ks j t)
    (hKo : ∀ j m, RamDriverCompose.orderPhaseCost n ns W ≤ Ko j m)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m) :
    60 * (n * n * n) ≤ Kl 0 n := by
  have hW : n * n ≤ W := by
    refine le_trans ?_ hWc
    simp only [TgtCoupling.chainWidth]
    exact le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ 1)
  calc 60 * (n * n * n)
      = n * (60 * (n * n)) := by ring
    _ ≤ n * (60 * W + 1600 * n) :=
        mul_le_mul_right (le_trans (mul_le_mul_right hW 60) (Nat.le_add_right _ _)) n
    _ ≤ Kl 0 n := level_interface_floor hℓ hKs hKo hKl

-- **The quantifier order kills the split**: at `ε = 1` and a constant as
-- generous as `10⁹`, the cubic floor exceeds the C0 budget
-- `c · (|x| + 1)²` on a sparse member (`|x| = 3·n + 3`) at `n = 10⁹`.
-- `c` is fixed before `n`, so one large instance is a refutation.
#guard 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2 < 60 * (10 ^ 9) ^ 3

-- and the `1600·n²` half alone — the R1.6 debt, alive even at `W = ns` —
-- already loses to the `ε = 1/2` budget `c · (3·n + 4) ^ (3/2)`: squaring
-- both sides, the check is `c² · (3·n + 4)³ < (1600 · n²)²`, here at
-- `c = 10⁶`, `n = 10⁸`.
#guard (10 ^ 6) ^ 2 * (3 * 10 ^ 8 + 4) ^ 3 < (1600 * (10 ^ 8) ^ 2) ^ 2

end Lax3Proofs.C0Probe
