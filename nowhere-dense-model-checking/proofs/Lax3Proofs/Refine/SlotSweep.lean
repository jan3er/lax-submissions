import Lax3Proofs.Refine.BridgeCrossing
import Lax3Proofs.C0Probe
import Lax3Proofs.UqwInstantiation

/-!
**The derivability sweep of the root theorem's hypothesis slots** — ND-MC
rebase, the B7 re-run's opening leaf (plan rev 3 delta 3).

Both of B7's gate failures were hypothesis slots that had been ruled fine
in prose and never checked: D4's "root input data" (`hcsr`, finding 1)
and §2.4's cost verdict (finding 2). Rev 3 therefore opens the re-run
with this: every slot of
`RamDriverRoot.driverRoot_decides_sentence` compiled against what a C0
discharge actually holds, before anything is restated or assembled.

**What a discharge holds.** C0
(`Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking`)
fixes a nowhere dense class `C`, a sentence `φ` and an `ε > 0`, then asks
for a program `p`, a constant `c` and a bound `T` with
`(T x : ℝ) ≤ c * (|x| + 1) ^ (1 + ε)`, such that at **every** `n`, `G`
with `C n G` and **every** word length `w`, `p` computes the answer on
`{x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (|x| + v + 1) ≤ 2 ^ w}` within
`T`. So the data available at a slot is: `EncodesGraph x n G`, the domain
word clause, `C n G` and nowhere-density of `C`, and free choices of
every parameter the root leaves open — all of the latter chosen **before**
`n`, `G`, `w` and `x`, because `p` and `c` are.

## The table

Thirty slots, in the root's own order. `producer` = closed here or by a
named landed theorem; `free` = discharged by choosing the parameter;
`BLOCKED` = compiled obstruction, no producer exists.

| # | slot | verdict | where |
|---|------|---------|-------|
| 1 | `hx` | free — C0's own hypothesis | `slot01_hx` |
| 2 | `hns` | free — defines `ns` | `slot02_hns` |
| 3 | `hO` | free — defines `O` | `slot03_hO` |
| 4 | `hT` | free — `T := padTarget x ns` | `slot04_hT` |
| 5 | `hxB` | producer — with the word bound of #12 | `slot05_hxB` |
| 6 | `hcsr` | **BLOCKED** at the landed root | §B |
| 7 | `hpad0` | free — same `T` | `slot07_hpad0` |
| 8 | `hrank` | free — `q_top := rank φ` | `slot08_hrank` |
| 9 | `hcap` | free — defines `cap` | `slot09_hcap` |
| 10 | `hmb` | free — defines `mb` | `slot10_hmb` |
| 11 | `hℓ` | free — defines `ℓ` | `slot11_hl` |
| 12 | `hB` | producer, **conditional on #26** | §C |
| 13 | `hWB` | free at `R = 0` (`W := ns`) | `slot13_hWB` |
| 14 | `hpow` | free — parameter constant | `slot14_hpow` |
| 15 | `hQ` | producer | `slot15_hQ` |
| 16 | `hbnd` | free — finite atom list, `B` large | note in §A |
| 17 | `hcostI` | free — defines `Ki` | note in §A |
| 18 | `hKsc` | free — defines `Ksc` | note in §A |
| 19 | `hKmono` | free — monotone `Kl` | note in §A |
| 20 | `hKs` | **BLOCKED** — cubic floor | §D |
| 21 | `hKbase` | free — defines `Kl ℓ` | note in §A |
| 22 | `hKo` | **BLOCKED** — size-blind carrier charge | §D |
| 23 | `hKc` | **BLOCKED** — `12 n²` + `coverCost`'s `100 n²` | §D |
| 24 | `hKd` | free — defines `Kd` | note in §A |
| 25 | `hbinj` | producer — `RamDriverRoot.blockInj_slot` | `slot25_hbinj` |
| 26 | `hdeg` | **BLOCKED** — no constant `Kmass` | §C |
| 27 | `hKl` | **BLOCKED** — turn sum × #20/#22/#23 | §D |
| 28 | `hKdec` | free — defines `Kdec` | note in §A |
| 29 | `hatoms` | free — finite atom list, `B` large | note in §A |
| 30 | `hKsent` | free — defines `Ksent` | note in §A |

Twenty-four slots are free or producered. **Six block**, in three
independent groups, and only the first was known when this leaf opened:

* **#6 `hcsr`** — B7 finding 1, repaired by G1 but *not yet at the root*:
  the repair lives in `RamDriverDedup.DecodeImplementsD`, and the root
  still reads its `CsrSimple` at the raw word. Dies at the `driverRootD`
  restatement (§B).
* **#26 `hdeg`, and hence #12 `hB`** — new here (§C). The slot is
  quantified over **every** permutation, and at a star with the centre
  ordered last the weakly-`2·cap`-reachable set is the whole vertex set.
  So no `Kmass` constant in `n` satisfies it on any class containing the
  stars, and `Refine.ArenaWidth`'s flip — which needs the degree
  parameter fixed before `n`, its own control 2
  (`no_wordConst_at_linear_degree`) — is not available through it. The
  intended producer, `RamDriverRoot.exists_wreachDeg_of_orderP`, delivers
  the bound only at orderings carrying `RamDriverCompose.OrderP R`, which
  is what the `levelAtR` / general-`R` restatement is for. Until that
  lands, finding 3's repair does not reach the root's own `hdeg`.
* **#20/#22/#23/#27, the cost group** — B7 finding 2, alive and sharper
  (§D). The root's own cost is at least `16 · n³`, from **two** slots
  (`hKs`, `hKl`) with no width path, no `chainWidth`, no `hWc` and no
  `W` anywhere in the derivation; at least `128 · n³` with `hKo` and
  `hKc` added. This is over C0's budget at every `ε < 2`.

**So C0 is not reachable through the root as it stands**, and the
obstruction is the cost residue (E-mem → member-driven interiors →
E-order re-run → E3b → E4c → R1.8), not anything the B7 re-run can
repair. §D names the responsible hypothesis shape for each blocked cost
slot, so the sweep is usable as that residue's work-list.

**A correction, recorded because it is in a landed commit message and a
landed plan section.** `Refine.BridgeSeamProbe.width_lt_two_pow` does
**not** close B7 finding 2. It says the `chainWidth n d D₁ R ≤ W` pin is
unaddressable as a matter of *word length*: `hWB` puts `W` under `B`,
`FitsWords` puts `B` under `2 ^ w`, and C0's smallest admissible `w` is
linear in `|x|`. That is a space statement about `W`. Finding 2 is a
*cost* statement about `Kl`, and §D derives it with `W` absent from both
the hypotheses used and the conclusion (`root_cost_floor_cubic`). The two
are compiled side by side in §E so the distinction is checkable rather
than asserted.
-/

namespace Lax3Proofs.Refine.SlotSweep

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax11.GraphEncoding
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamDriver
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax13Proofs.Compile (Layout)

/-! ## §A. The free and producered slots

Twenty-four of the thirty. The ones below are compiled; the remainder are
free by the same one-line argument and are recorded in the table rather
than restated here, because each is literally "instantiate the parameter
at the expression the slot bounds":

* **#16 `hbnd` / #29 `hatoms`** — `tablesAt q_top cap mb φ j` and
  `bcAtomsOf` produce **finite lists** determined by `q_top`, `cap`, `mb`
  and `φ` alone; `Kb`/`Kb₀` are the maxima of `RamDriverIO.atomCost n ns`
  over them, and the two `< B` clauses are finitely many constants of the
  parameters, so #12's bound covers them.
* **#17 `hcostI`, #18 `hKsc`, #21 `hKbase`, #24 `hKd`, #28 `hKdec`,
  #30 `hKsent`** — each bounds a closed expression by a free parameter;
  take the parameter to be that expression.
* **#19 `hKmono`** — `CostRecurrence`'s closed form is monotone in the
  size argument by construction.

None of these six-plus-six is where a gate has ever failed, and none of
them constrains another slot. The compiled ones below are the slots whose
producer is either C0's own data or a named landed theorem. -/

section Free

variable {n : ℕ} {q_top cap mb ns W ℓ : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {G : SimpleGraph (Fin n)} {x : List ℕ}

/-- **#1 `hx`.** C0's domain membership *is* the slot. -/
theorem slot01_hx (hx : EncodesGraph x n G) : EncodesGraph x n G := hx

/-- **#2 `hns`.** The slot count is a definition. -/
theorem slot02_hns (x : List ℕ) : 2 * edgeCount x = 2 * edgeCount x := rfl

/-- **#3 `hO`.** The offset function is a definition. -/
theorem slot03_hO (x : List ℕ) (n : ℕ) : ∀ i ≤ n, offset x i = offset x i := fun _ _ => rfl

/-- **#4 `hT`.** The target function the decode actually leaves in `tgt`
is `RamDriverDedup.padTarget`, and it agrees with the word below the slot
count. -/
theorem slot04_hT (x : List ℕ) (ns : ℕ) :
    ∀ i < ns, RamDriverDedup.padTarget x ns i = target x i :=
  fun _ h => RamDriverDedup.padTarget_lt h

/-- **#7 `hpad0`.** The same function pads with zeros above the slot
count, so the clause is free at the canonical choice. -/
theorem slot07_hpad0 (x : List ℕ) (ns W : ℕ) :
    ∀ z, ns ≤ z → z < W → RamDriverDedup.padTarget x ns z = 0 :=
  fun _ h _ => RamDriverDedup.padTarget_ge h

/-- **#8 `hrank`.** Take `q_top := rank φ`; `φ` is fixed before the
instance, as C0 requires. -/
theorem slot08_hrank (φ : Lax3.FirstOrder.FO 0) :
    Lax3.FirstOrder.rank φ ≤ Lax3.FirstOrder.rank φ := le_rfl

/-- **#9 `hcap`, #10 `hmb`, #11 `hℓ`.** Parameter definitions, in the
order they depend on one another: `cap` from `q_top`, `ℓ` from the
class's threshold function, `mb` from both. -/
theorem slot09_hcap (q_top : ℕ) : rhoMinus 0 q_top = rhoMinus 0 q_top := rfl

theorem slot10_hmb (ℓ cap : ℕ) : ℓ * (2 * cap + 1) = ℓ * (2 * cap + 1) := rfl

theorem slot11_hl (N : ℕ → ℕ) (s : ℕ) : N (2 * s + 2) = N (2 * s + 2) := rfl

/-- **#5 `hxB`, #13 `hWB`, #14 `hpow`, #12 `hB` — the four value-bound
clauses, together.** They are one slot in practice: all four ask for `B`
above something, and #12 is the only one with a nontrivial producer
(`Refine.ArenaWidth.word_size_for_encoded`, which also delivers
`FitsWords`). Stated here as the conjunction a discharge has to produce,
so that §C's obstruction attaches to the right place.

At `R = 0` the width may be taken to be the slot count (`W := ns`), which
is what makes #13 a consequence of #12's own clause rather than a new
demand; the general-`R` restatement re-imports a width pin, and §E is
where that is measured. -/
def ValueBounds (B n ns W cap mb ℓ Kmass : ℕ) (x : List ℕ) : Prop :=
  (∀ v ∈ x, v < B) ∧ WordBoundK B n Kmass ns cap mb ∧ n + W + 1 < B ∧
    2 ^ sigL cap mb ℓ < B

/-- **#13 at `W := ns`.** The width clause is `n + ns + 1 < B`, which
`WordBoundK`'s own arena clause already gives — so at `R = 0` this slot
costs nothing beyond #12. -/
theorem slot13_hWB {B n ns cap mb Kmass : ℕ} (hB : WordBoundK B n Kmass ns cap mb) :
    n + ns + 1 < B := by
  have := hB.1
  omega

/-- **#14.** `2 ^ sigL cap mb ℓ` is a constant of the parameters — no `n`,
no `ns`, no word — so a `B` above it is a choice, not a constraint on the
instance. Recorded as the shape of the demand. -/
theorem slot14_hpow {B cap mb ℓ : ℕ} (h : 2 ^ sigL cap mb ℓ < B) :
    2 ^ sigL cap mb ℓ < B := h

/-- **#15 `hQ`.** The campaign's mathematics, from Lax12: on a nowhere
dense class the threshold function and separator bound exist, uniformly
in the member. This is the producer, at the root's own reading. -/
theorem slot15_hQ (C : Lax12.GraphClasses.GraphClass)
    (hC : Lax12.NowhereDenseClasses.NowhereDense C) (cap : ℕ) :
    ∃ (N : ℕ → ℕ) (s : ℕ), ∀ (m : ℕ) (Gm : SimpleGraph (Fin m)), C m Gm →
      ∀ Pt : Set (Fin m), N (2 * s + 2) ≤ Pt.ncard →
        ∃ S Bd : Set (Fin m), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
          DistIndependent (deleteVerts Gm S) (2 * cap) Bd := by
  obtain ⟨N, s, h⟩ := UqwInstantiation.hQ_of_nowhereDense C hC cap
  exact ⟨N, s, fun m Gm hG => h m Gm hG⟩

/-- **#25 `hbinj`.** Producered, and already consumed at the root:
`RamDriverRoot.driverRoot_decides_sentence_binj` is the root minus this
slot. -/
theorem slot25_hbinj (G : SimpleGraph (Fin n)) (cap : ℕ) :
    ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (mm : ℕ),
      RamCover.CoverOut G M π ord cap mm Xoff Xmem asg → Refine.MassMath.BlockInj n Xoff Xmem :=
  RamDriverRoot.blockInj_slot G cap

end Free

/-! ## §B. Slot #6 `hcsr` — blocked at the landed root, producered at the
dedup'd data

B7 finding 1, restated so the sweep is self-contained: `EncodesGraph`
deliberately permits a row to name a neighbour twice, and the root reads
`RamElim.CsrSimple` at the raw word. G1 repaired this, but **in the
composed decode phase, not at the root**: `RamDriverDedup.decodeImplementsD`
delivers `CsrSimple` at `dedupNs x`, `dedupOffset x`, `dedupTarget x`,
and the root still asks for it at `2 * edgeCount x`, `offset x`,
`target x`. The slot therefore has no producer *today* and a producer the
moment the root is restated on the composed decode. -/

section Csr

/-- **The obstruction**, `C0Probe.encodesGraph_not_csrSimple` at the
root's own reading of the slot: `O := offset x`, `T := target x`,
`ns := 2 * edgeCount x`. -/
theorem slot06_hcsr_blocked :
    ∃ (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)),
      EncodesGraph x n G ∧
        ¬ RamElim.CsrSimple G (2 * edgeCount x) (offset x) (target x) :=
  C0Probe.encodesGraph_not_csrSimple

/-- **The producer, at the data the composed decode delivers.** Same
predicate, same graph, different triple — which is exactly why the repair
is a root restatement and not a lemma. -/
theorem slot06_hcsr_dedup {n : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) :
    RamElim.CsrSimple G (RamDriverDedup.dedupNs x) (RamDriverDedup.dedupOffset x)
      (RamDriverDedup.dedupTarget x) :=
  RamDriverDedup.csrSimple_dedup hx

end Csr

/-! ## §C. Slot #26 `hdeg` — no constant `Kmass`, and slot #12 falls with
it

This is the sweep's new finding, and it is the one that matters for
finding 3's repair.

The root's slot is

```lean
hdeg : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n),
  (Lax12.ColoringNumbers.wreach (RamBfs.masked G M) π (2 * cap) v).ncard ≤ Kmass
```

— quantified over **every** permutation. Weak reachability is a property
of the *ordering*, not of the graph: a graph of maximum degree `d` has an
ordering under which every weakly-`r`-reachable set is small, and (if it
has a vertex of degree `d`) an ordering under which one of them has `d+1`
elements. The slot asks for the bound under all of them.

At the star on `Fin n` with the centre ordered last, the centre weakly
reaches the whole vertex set at radius `1`, so the slot forces
`n ≤ Kmass`. Stars are members of essentially every nowhere dense class
one would state C0 for, so no `Kmass` chosen before `n` — which is what
C0's `∃ c` before `∀ n` requires — satisfies the slot.

The consequence for #12 is immediate and is exactly `ArenaWidth`'s own
control 2: `WordBoundK B n Kmass ns cap mb` with `Kmass ≥ n` *is* the
retired carrier bound `WordBound B n ns cap mb`, and
`ArenaWidth.no_wordConst_at_linear_degree` refutes the flip there. So the
E-mem/W1–W3 repair of finding 3 is sound at the *slot*, and not yet
usable at the *root*, because the root's `hdeg` is the wrong shape to
supply the constant it needs.

The producer that has the right shape exists:
`RamDriverRoot.exists_wreachDeg_of_orderP` bounds the degree at orderings
carrying `RamDriverCompose.OrderP R G M π ord`, on a nowhere dense class,
by `⌈c · n ^ δ⌉₊`. It is unavailable at `R = 0`, where `levelAt` supplies
`OrderP` as `True`. Threading it is the `levelAtR` / general-`R`
restatement — B7's own next piece. -/

section Deg

open Lax12.ColoringNumbers (wreach)

/-- The star on `Fin n` whose centre is the **last** vertex. Its centre
has degree `n - 1`; every other vertex has degree `1`. -/
def starLast (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ((u : ℕ) + 1 = n ∨ (v : ℕ) + 1 = n)
  symm := by intro u v h; exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The centre, as a vertex. -/
def centre (n : ℕ) (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

theorem centre_val {n : ℕ} (hn : 0 < n) : ((centre n hn : Fin n) : ℕ) + 1 = n := by
  simp only [centre]; omega

/-- Every vertex is at or below the centre in the identity ordering. -/
theorem le_centre {n : ℕ} (hn : 0 < n) (u : Fin n) : u ≤ centre n hn := by
  rw [Fin.le_def]
  simp only [centre]
  omega

/-- The centre is adjacent to everything else, in the arena of any mask
that keeps the vertices alive. -/
theorem adj_centre {n : ℕ} (hn : 0 < n) {M : ℕ → ℕ} (hM : ∀ v, M v ≠ 0) {u : Fin n}
    (hu : u ≠ centre n hn) : (masked (starLast n) M).Adj (centre n hn) u := by
  rw [RamBfs.masked_adj]
  exact ⟨⟨fun h => hu h.symm, Or.inl (centre_val hn)⟩, hM _, hM _⟩

/-- **The centre weakly reaches everything.** Under the identity ordering
the centre is the `π`-maximum, so every one-edge walk out of it has its
endpoint `π`-minimal on the walk's support — which is the whole content
of `wreach`. -/
theorem wreach_centre_univ {n r : ℕ} (hn : 0 < n) (hr : 1 ≤ r) {M : ℕ → ℕ}
    (hM : ∀ v, M v ≠ 0) :
    wreach (masked (starLast n) M) 1 r (centre n hn) = Set.univ := by
  refine Set.eq_univ_of_forall fun u => ?_
  by_cases hu : u = centre n hn
  · subst hu
    exact ⟨SimpleGraph.Walk.nil, by simp, by simp⟩
  · refine ⟨SimpleGraph.Walk.cons (adj_centre hn hM hu) SimpleGraph.Walk.nil, by simpa using hr,
      ?_⟩
    intro y hy
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact le_centre hn u
    · exact le_rfl

/-- …and there are `n` of them. -/
theorem ncard_wreach_centre {n r : ℕ} (hn : 0 < n) (hr : 1 ≤ r) {M : ℕ → ℕ}
    (hM : ∀ v, M v ≠ 0) :
    (wreach (masked (starLast n) M) 1 r (centre n hn)).ncard = n := by
  rw [wreach_centre_univ hn hr hM, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- **The slot, at one star.** `RamDriverRoot`'s `hdeg` hypothesis
verbatim, at `G := starLast n`, forces `n ≤ Kmass`. The radius clause is
free: `hcap` makes `cap` a power of nine, so `2 * cap ≥ 1`. -/
theorem deg_slot_at_starLast {n Kmass cap q_top : ℕ} (hn : 0 < n)
    (hcap : cap = rhoMinus 0 q_top)
    (hdeg : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n),
      (wreach (masked (starLast n) M) π (2 * cap) v).ncard ≤ Kmass) :
    n ≤ Kmass := by
  have hr : 1 ≤ 2 * cap := by
    have := Lax3Proofs.Horizon.one_le_rhoMinus 0 q_top
    omega
  have := hdeg (fun _ => 1) 1 (centre n hn)
  rwa [ncard_wreach_centre hn hr (fun _ => one_ne_zero)] at this

/-- **The obstruction, in C0's quantifier order.** No `Kmass` chosen
before the instance satisfies the slot at every star — which is what a
discharge for any class containing the stars would need, since C0 fixes
`c` and the program before `n`. -/
theorem slot26_hdeg_blocked {cap q_top : ℕ} (hcap : cap = rhoMinus 0 q_top) :
    ¬ ∃ Kmass : ℕ, ∀ n : ℕ, 0 < n →
        ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n),
          (wreach (masked (starLast n) M) π (2 * cap) v).ncard ≤ Kmass := by
  rintro ⟨Kmass, h⟩
  have := deg_slot_at_starLast (n := Kmass + 1) (Kmass := Kmass) (cap := cap) (q_top := q_top)
    (by omega) hcap (h (Kmass + 1) (by omega))
  omega

/-- **The negative control — the star is what does the work.** At the
edgeless graph, the same slot holds at `Kmass = 1` for every mask,
ordering and vertex, so the obstruction is not a defect of the slot's
shape or of `wreach`: it is the graph. (This is also why
`BridgeSeamProbe`'s `emptyWord` witness, and hence `ArenaWidth`'s flip,
is genuinely satisfiable at *that* instance.) -/
theorem deg_slot_at_bot {n cap : ℕ} (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n) :
    (wreach (masked (⊥ : SimpleGraph (Fin n)) M) π cap v).ncard ≤ 1 := by
  have hsub : wreach (masked (⊥ : SimpleGraph (Fin n)) M) π cap v ⊆ {v} := by
    rintro u ⟨w, -, -⟩
    have : u = v := by
      cases w with
      | nil => rfl
      | cons h _ => exact absurd (RamBfs.masked_adj.mp h).1 (by simp)
    simpa using this
  exact le_trans (Set.ncard_le_ncard hsub (Set.finite_singleton v)) (by simp)

/-- **The consequence for slot #12.** Where `hdeg` forces `n ≤ Kmass`,
the root's word-bound slot is the retired carrier bound again — the same
inequality `n * n + ns + 2 * cap + 2 < B` that
`BridgeSeamProbe.no_word_size_for_sparse` refutes at word lengths C0's
domain admits. So finding 3's repair does not survive the trip through
`hdeg` at its landed shape. -/
theorem wordBound_of_deg_slot {B n Kmass ns cap mb : ℕ} (hK : n ≤ Kmass)
    (hB : WordBoundK B n Kmass ns cap mb) : WordBound B n ns cap mb := by
  refine ⟨?_, hB.2⟩
  have h1 := hB.1
  have h2 : n * n ≤ n * Kmass := Nat.mul_le_mul_left n hK
  omega

/-- …and the refutation, joined: at a star instance the value bound and
the compile layout's fits-words condition are jointly unsatisfiable at
word lengths C0's domain admits, exactly as before the repair. Stated
against the *carrier* refutation so that no new arithmetic is introduced
— what is new is only that `hdeg` puts us back inside its scope. -/
theorem no_word_size_through_deg_slot {L : Layout} {B w n Kmass ns cap mb : ℕ}
    (hK : n ≤ Kmass) (hfit : L.FitsWords B w) (hB : WordBoundK B n Kmass ns cap mb) :
    n * n < 2 ^ w :=
  BridgeSeamProbe.sq_lt_two_pow_of_fits hfit (wordBound_of_deg_slot hK hB)

end Deg

/-! ## §D. Slots #20/#22/#23/#27 — the cost group, and the cubic floor

B7 finding 2, alive, and sharper than it was recorded.

`C0Probe.level_interface_floor` derived `n * (60 * W + 1600 * n) ≤ Kl 0 n`
from `hKs`, `hKo` and `hKl`, and `level_interface_floor_cubic` reached
`60 * n³` only through `hWc : chainWidth n d D₁ R ≤ W`, a hypothesis of
the *ordering phase* and not of the root. That extra hypothesis is not
needed. The `n²` is inside the **turn cost itself**:

```lean
RamDriverDescend.descendCost n ns cap j = 16 * (n * n) + 75 * n + 51 + …
```

and `RamDriverRoot.turnCost` opens with it. So `hKs` alone charges
`16 * n²` per turn, `hKl` runs `n` turns at the root, and the product is
cubic with `W` occurring nowhere.

**Which hypothesis shape is responsible** — the residue's work-list:

* **#20 `hKs`** — `turnCostSize … ≤ Ks j t` at a turn cost whose
  descent charges `16 * n²` for the level's *own* carrier, at every turn,
  independent of the block the turn processes (`turnCostSize` ignores its
  size slot `s`; `turnCostSize_eq`). Repair: the descent's block-driven
  interior (E4c, `descendCom` swap / `qd` layout / alive-mask hoist).
* **#22 `hKo`** — `orderPhaseCost n ns W ≤ Ko j m` is **size-blind** in
  `m`: it charges `1600 * n + 1350 * ns + 60 * W + 650` on the *empty*
  arena. Repair: E-mem member lists, then the member-driven order
  interior; E-order's no-escape theorem is the statement that no closed
  form survives an empty-arena carrier charge.
* **#23 `hKc`** — `coverPhaseCost n ns ≤ Kc j m`, also size-blind, and
  quadratic on its own face: `RamCover.coverCost n ns` is
  `100 * n * n + 50 * n * ns + …` and the phase adds `12 * (n * n)`.
  Repair: E3b (cover composition, `compactCom`-before-`coverSave`).
* **#27 `hKl`** — the level bill sums `Ks j (bs c)` over `t ≤ m` turns
  and adds `Ko j m + Kc j m + Kd j m` once. It is the multiplier: it is
  what turns any per-turn carrier charge into a cubic. It is also the
  slot that is *correct* — the sum over blocks is the shape the mass
  recursion needs — so the repair is in its summands, not in it.

Nothing here is about `hKd` (#24), whose `sweepCost` is linear in `n`,
nor about `hKbase` (#21). -/

section Floor

variable {n q_top cap mb ns W ℓ Kmass Kdec Ksent : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}

/-- **The descent's carrier charge, isolated.** One line, and it is the
whole mechanism of the cubic: a turn pays `16 * n²` before it has looked
at its block. -/
theorem descend_carrier (n ns cap j : ℕ) :
    16 * (n * n) ≤ RamDriverDescend.descendCost n ns cap j := by
  rw [RamDriverDescend.descendCost]; omega

/-- …and a turn pays the descent. -/
theorem turn_carrier (n ns cap mb q_top j : ℕ) (φ : Lax3.FirstOrder.FO 0) (Ksc Kin : ℕ) :
    16 * (n * n) ≤ RamDriverRoot.turnCost n ns cap mb q_top j φ Ksc Kin := by
  rw [RamDriverRoot.turnCost]
  have := descend_carrier n ns cap j
  omega

/-- **#20's contribution.** From `hKs` alone, the root level's turn budget
is quadratic in the carrier. -/
theorem hKs_carrier (hℓ : 1 ≤ ℓ)
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      RamDriverRoot.turnCostSize n ns cap mb q_top j φ (Ksc j) t (Kl (j + 1) t) ≤ Ks j t) :
    16 * (n * n) ≤ Ks 0 0 := by
  have h := hKs 0 (by omega) 0
  rw [RamDriverRoot.turnCostSize_eq] at h
  exact le_trans (turn_carrier n ns cap mb q_top 0 φ (Ksc 0) (Kl 1 0)) h

/-- **#27's contribution — the multiplier.** The root level runs `n`
turns, each paying its turn budget; the mass side condition is free at
the all-empty block profile, so the floor is not about the mass. -/
theorem hKl_turns (hℓ : 1 ≤ ℓ)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m) :
    n * (Ks 0 0 + 11) ≤ Kl 0 n := by
  have h0 := hKl 0 (by omega) n n le_rfl (fun _ => 0) (by simp)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h0
  calc n * (Ks 0 0 + 11)
      ≤ n * (Ks 0 0 + 11) + 6 := Nat.le_add_right _ _
    _ ≤ Kd 0 n + (n * (Ks 0 0 + 11) + 6) := Nat.le_add_left _ _
    _ ≤ Kc 0 n + (Kd 0 n + (n * (Ks 0 0 + 11) + 6)) := Nat.le_add_left _ _
    _ ≤ Ko 0 n + (Kc 0 n + (Kd 0 n + (n * (Ks 0 0 + 11) + 6))) := Nat.le_add_left _ _
    _ ≤ Kl 0 n := h0

/-- **The cubic floor, from two slots.** `hKs` (#20) and `hKl` (#27),
byte-identical to the root's, at `ℓ ≥ 1`: the root level's budget is at
least `16 · n³`.

`W` occurs in neither hypothesis used nor the conclusion, `hKo` and `hKc`
are not consumed, and there is no `chainWidth`, no `hWc` and no `R`. This
is what `C0Probe.level_interface_floor_cubic` needed the ordering phase's
width pin for and did not need. -/
theorem level_cost_floor_cubic (hℓ : 1 ≤ ℓ)
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      RamDriverRoot.turnCostSize n ns cap mb q_top j φ (Ksc j) t (Kl (j + 1) t) ≤ Ks j t)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m) :
    16 * (n * n * n) ≤ Kl 0 n := by
  have hs := hKs_carrier hℓ hKs
  calc 16 * (n * n * n) = n * (16 * (n * n)) := by ring
    _ ≤ n * (Ks 0 0 + 11) := Nat.mul_le_mul_left n (by omega)
    _ ≤ Kl 0 n := hKl_turns hℓ hKl

/-- **The sharper form, with the two size-blind phase slots added.**
`hKo` (#22) and `hKc` (#23) charge their phases on the *nested* level's
empty arena, and `hKs` carries the nested budget additively, so each
phase cost is paid once per turn as well. -/
theorem level_cost_floor_sharp (hℓ : 2 ≤ ℓ)
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      RamDriverRoot.turnCostSize n ns cap mb q_top j φ (Ksc j) t (Kl (j + 1) t) ≤ Ks j t)
    (hKo : ∀ j m, RamDriverCompose.orderPhaseCost n ns W ≤ Ko j m)
    (hKc : ∀ j m, RamDriverCompose.coverPhaseCost n ns ≤ Kc j m)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m) :
    128 * (n * n * n) ≤ Kl 0 n := by
  -- the nested level pays both size-blind phases on the empty arena
  have h10 : RamDriverCompose.orderPhaseCost n ns W + RamDriverCompose.coverPhaseCost n ns
      ≤ Kl 1 0 := by
    have h := hKl 1 (by omega) 0 0 le_rfl (fun _ => 0) (by simp)
    simp only [Finset.range_zero, Finset.sum_empty] at h
    have := hKo 1 0
    have := hKc 1 0
    omega
  -- a turn pays its own descent and the nested level
  have hks : 16 * (n * n) + Kl 1 0 ≤ Ks 0 0 := by
    have h := hKs 0 (by omega) 0
    simp only [Nat.zero_add] at h
    rw [RamDriverRoot.turnCostSize_eq, RamDriverRoot.turnCost] at h
    have hd := descend_carrier n ns cap 0
    omega
  have hcov : 112 * (n * n) ≤ RamDriverCompose.coverPhaseCost n ns := by
    rw [RamDriverCompose.coverPhaseCost, RamCover.coverCost]
    have : 100 * n * n = 100 * (n * n) := by ring
    omega
  calc 128 * (n * n * n) = n * (16 * (n * n) + 112 * (n * n)) := by ring
    _ ≤ n * (Ks 0 0 + 11) := Nat.mul_le_mul_left n (by omega)
    _ ≤ Kl 0 n := hKl_turns (by omega) hKl

/-! ### The plug check

The floor above is stated at hypothesis shapes; what says those shapes
are the root's is this application. The theorem takes
`RamDriverRoot.driverRoot_decides_sentence`'s hypothesis list verbatim
(plus `2 ≤ ℓ`, which is data about the class and not a slot) and returns
the root's own conclusion **together with** the floor on the root's own
cost expression. It elaborates only if every slot it forwards is the one
the root has. -/

open Classical in
/-- **The root, with its own cost floored.** The `Spec` is
`driverRoot_decides_sentence`'s, unweakened, and the second component
says its cost `Kdec + (Kl 0 (n + ns) + Ksent)` is at least `128 · n³`.

`hKmono` is what carries the floor from `Kl 0 n` to `Kl 0 (n + ns)`, so
the weight re-read of rebase E6 does not evade it. -/
theorem driverRoot_decides_sentence_floored {B s Kb Kb₀ : ℕ} {N Ki : ℕ → ℕ}
    {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ} {x : List ℕ}
    (hℓ2 : 2 ≤ ℓ)
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hO : ∀ i ≤ n, O i = offset x i) (hT : ∀ i < ns, T i = target x i)
    (hxB : ∀ v ∈ x, v < B) (hcsr : RamElim.CsrSimple G ns O T)
    (hpad0 : ∀ z, ns ≤ z → z < W → T z = 0)
    (hrank : Lax3.FirstOrder.rank φ ≤ q_top) (hcap : cap = rhoMinus 0 q_top)
    (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBoundK B n Kmass ns cap mb) (hWB : n + W + 1 < B)
    (hpow : 2 ^ sigL cap mb ℓ < B)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n ns σs.t ≤ Kb)
    (hcostI : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j)
    (hKsc : ∀ j < ℓ, Ki j * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc j)
    (hKmono : ∀ j, Monotone (Kl j))
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      RamDriverRoot.turnCostSize n ns cap mb q_top j φ (Ksc j) t (Kl (j + 1) t) ≤ Ks j t)
    (hKbase : ∀ m, RamDriverBot.baseCost q_top cap mb ℓ n φ ≤ Kl ℓ m)
    (hKo : ∀ j m, RamDriverCompose.orderPhaseCost n ns W ≤ Ko j m)
    (hKc : ∀ j m, RamDriverCompose.coverPhaseCost n ns ≤ Kc j m)
    (hKd : ∀ j m, Refine.DeadSweep.sweepCost q_top cap mb j n φ ≤ Kd j m)
    (hbinj : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (mm : ℕ),
      RamCover.CoverOut G M π ord cap mm Xoff Xmem asg → Refine.MassMath.BlockInj n Xoff Xmem)
    (hdeg : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n),
      (Lax12.ColoringNumbers.wreach (masked G M) π (2 * cap) v).ncard ≤ Kmass)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m)
    (hKdec : RamDriverIO.decodeCost n ns ≤ Kdec)
    (hatoms : ∀ s ∈ (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2,
      s.r + 1 < B ∧ s.t < B ∧ RamDriverIO.atomCost n ns s.t ≤ Kb₀)
    (hKsent : Kb₀ * (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2.length + 1 +
      (1 + (RamDriverIO.sentenceExpr q_top cap mb φ).size) ≤ Ksent) :
    Spec B (fun σ => DecodeMem n ns W σ ∧ LevelMem B n cap mb σ ∧ DepthMem n cap mb σ ∧
        OrderMem B n ns W σ ∧ TablesSized q_top cap mb φ n σ ∧
        BaseArrs B q_top cap mb ℓ φ σ ∧ σ.inp = x ∧ σ.out = [])
      (driverRoot q_top cap mb 0 ℓ φ)
      (fun _ σ' => σ'.out = [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
      (Kdec + (Kl 0 (n + ns) + Ksent)) ∧
    128 * (n * n * n) ≤ Kdec + (Kl 0 (n + ns) + Ksent) := by
  refine ⟨RamDriverRoot.driverRoot_decides_sentence hx hns hO hT hxB hcsr hpad0 hrank hcap
    hmb hℓ hB hWB hpow hQ hbnd hcostI hKsc hKmono hKs hKbase hKo hKc hKd hbinj hdeg hKl
    hKdec hatoms hKsent, ?_⟩
  have hfloor := level_cost_floor_sharp hℓ2 hKs hKo hKc hKl
  have hmono : Kl 0 n ≤ Kl 0 (n + ns) := hKmono 0 (Nat.le_add_right n ns)
  omega

/-! ### The controls

Each is a refutation, not an assertion, and each isolates one
ingredient. -/

/-- **Control 1 — the size-blindness is real, not an artefact of reading
the phase cost at a large arena.** `hKo`'s bound is charged at `m = 0`:
the ordering phase's carrier term is paid on an arena with nothing alive
in it. This is the shape E-mem/E-order have to remove. -/
theorem hKo_charges_empty_arena
    (hKo : ∀ j m, RamDriverCompose.orderPhaseCost n ns W ≤ Ko j m) (j : ℕ) :
    1600 * n + 650 ≤ Ko j 0 := by
  have := hKo j 0
  rw [RamDriverCompose.orderPhaseCost] at this
  omega

/-- **Control 2 — the same for `hKc`, and it is quadratic on its own
face.** The cover phase charges `112 * n²` at every arena including the
empty one. -/
theorem hKc_charges_empty_arena
    (hKc : ∀ j m, RamDriverCompose.coverPhaseCost n ns ≤ Kc j m) (j : ℕ) :
    112 * (n * n) ≤ Kc j 0 := by
  have h := hKc j 0
  rw [RamDriverCompose.coverPhaseCost, RamCover.coverCost] at h
  have : 100 * n * n = 100 * (n * n) := by ring
  omega

/-- **Control 3 — `hKd` is *not* responsible.** The dead-row sweep is
linear in the carrier, so a floor derivation that used it would be about
the wrong slot; the sweep's verdict for #24 is "free", and this is why.
-/
theorem sweepCost_linear (q_top cap mb jd : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∃ K : ℕ, ∀ n : ℕ, Refine.DeadSweep.sweepCost q_top cap mb jd n φ = K * n + 6 :=
  ⟨_, fun _ => rfl⟩

/-- **Control 4 — the turn's size slot is ignored, which is why the
carrier charge cannot be blamed on a large block.** `turnCostSize` is
`turnCost` at every value of its size argument, so the `16 * n²` of
`hKs_carrier` is paid by a turn processing an **empty** block. -/
theorem turnCostSize_size_blind (n ns cap mb q_top j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (Ksc s s' Kin : ℕ) :
    RamDriverRoot.turnCostSize n ns cap mb q_top j φ Ksc s Kin
      = RamDriverRoot.turnCostSize n ns cap mb q_top j φ Ksc s' Kin := by
  rw [RamDriverRoot.turnCostSize_eq, RamDriverRoot.turnCostSize_eq]

end Floor

/-! ### The floor against C0's budget

C0 asks for `(T x : ℝ) ≤ c * (|x| + 1) ^ (1 + ε)` at every `ε > 0`, with
`c` chosen before the instance. On a word encoding a graph,
`|x| = 3 + n + ns`, so at the edgeless member `|x| = n + 3` and the
budget at `ε = 1/2` is `c * (n + 4) ^ (3/2)`. Squaring both sides, the
check is `c² * (n + 4)³ < (128 · n³)²`, and one large instance settles it
because `c` is fixed first. -/

-- at `c = 10 ^ 6` and `n = 10 ^ 8`, the cubic floor is over the `ε = 1/2`
-- budget by twelve orders of magnitude
#guard (10 ^ 6) ^ 2 * (10 ^ 8 + 4) ^ 3 < (128 * (10 ^ 8) ^ 3) ^ 2

-- the negative control: the same comparison at `ε = 3` — a budget C0 does
-- *not* ask for at every `ε` — is satisfied, so the `#guard` above is
-- about the exponent and not about the constants
#guard 128 * (10 ^ 8) ^ 3 < 10 ^ 6 * (10 ^ 8 + 4) ^ 4

/-! ## §E. `width_lt_two_pow` does not close finding 2

Recorded because the opposite is written in a landed commit message and a
landed plan section, and a compiled distinction outlives both.

The two statements below are the whole of it. The first is a *space*
statement: it bounds `W`, the ordering phase's width parameter, by the
machine's addressable range, and it is what makes the general-`R`
`chainWidth n d D₁ R ≤ W` pin unaddressable rather than merely expensive.
The second is a *cost* statement: it bounds `Kl`, the level budget, from
below. Its derivation (`level_cost_floor_cubic`) mentions neither `W` nor
`2 ^ w` nor any layout, and its hypotheses are two slots that carry no
width.

So the `WordBoundK` repair and `width_lt_two_pow` between them close
finding 3 and re-read finding 2's *width* half; the cost floor is
untouched by both, and survives at `W = ns`, at `W = 0`, and with the
width path deleted entirely. -/

section Distinction

variable {n q_top cap mb ns W ℓ Kmass : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}

/-- The space statement, cited at its landed name. -/
theorem width_is_bounded {L : Layout} {B w : ℕ} (hfit : L.FitsWords B w)
    (hWB : n + W + 1 < B) : W < 2 ^ w :=
  BridgeSeamProbe.width_lt_two_pow hfit hWB

/-- The cost statement, with the width path deleted. `W` does not occur
in `level_cost_floor_cubic` — not in its hypotheses, not in its
conclusion, not anywhere in its proof — which is the point: no choice of
`W`, and no bound on `W` from any source, reaches the floor. This
restatement carries no `W` binder either, and is proved by that theorem
applied unchanged. -/
theorem floor_has_no_width (hℓ : 1 ≤ ℓ)
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      RamDriverRoot.turnCostSize n ns cap mb q_top j φ (Ksc j) t (Kl (j + 1) t) ≤ Ks j t)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m) :
    16 * (n * n * n) ≤ Kl 0 n :=
  level_cost_floor_cubic hℓ hKs hKl

end Distinction

/-! ## §F. The axiom check -/

#print axioms slot06_hcsr_blocked
#print axioms slot06_hcsr_dedup
#print axioms slot15_hQ
#print axioms slot25_hbinj
#print axioms deg_slot_at_starLast
#print axioms slot26_hdeg_blocked
#print axioms deg_slot_at_bot
#print axioms no_word_size_through_deg_slot
#print axioms level_cost_floor_cubic
#print axioms level_cost_floor_sharp
#print axioms driverRoot_decides_sentence_floored

end Lax3Proofs.Refine.SlotSweep
