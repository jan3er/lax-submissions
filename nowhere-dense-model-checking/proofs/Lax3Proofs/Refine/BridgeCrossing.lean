import Lax3Proofs.Refine.ArenaWidth

/-!
**The bridge seam, crossed** — ND-MC rebase, wave E-mem, leaf W3's
acceptance.

`Refine.BridgeSeamProbe` §5 (`no_word_size_for_sparse`) showed that the
landed root theorem could not cross the `Spec → ComputesInTime` bridge:
its word-bound slot was `RamDriver.WordBound`, whose arena clause pins
`n * n + ns + 2 * cap + 2 < B`, and that is jointly unsatisfiable with
`Compile.Layout.FitsWords B w` at word lengths C0's own domain admits.
`Refine.ArenaWidth` compiled the repair route — `RamDriver.WordBoundK`,
the same clause with the arena read at a degree parameter, and
`word_size_for_encoded`, which says a value bound exists at *every* word
of C0's domain. W1 and W2 re-walked the cover pass and threaded the new
slot through every phase; W3 restated the root at it.

This file is the acceptance: the repair, stated **at the root theorem's
own hypothesis**, not at a lookalike.

1. **§1** — `RootBound`, the root theorem's word-bound slot, named, with
   the plug check `driverRoot_decides_sentence_bound`: the root
   restated with the name in that position and proved by the root
   itself. It type-checks only if `RamDriverRoot`'s `hB` really is
   `WordBoundK` at the degree parameter its own `hdeg` slot bounds — a
   different degree, or the retired `WordBound`, and the term fails.
2. **§2** — the slot is satisfiable at every word of C0's domain and
   every word length that domain admits (`word_size_for_root`), in C0's
   own quantifier order, constant first (`exists_wordConst_root`).
3. **§3, the sharp form** — at the very instance where
   `no_word_size_for_sparse` kills the old bound *for every value
   bound*, the restated root's slot has one
   (`root_flip_at_the_refuting_instance`), and the probe's own theorem,
   restated at the root's slot, is **false** (`no_word_size_at_root`).
   The bridge is no longer refuted on space grounds.
4. **§4 — the controls, and they bite.** The same statement is false at
   the retired carrier bound, false when the degree parameter is allowed
   to grow with the instance, and false when the layout's array count
   does — so §2 rests on `Kmass` being a constant of the class (which is
   what `RamDriverRoot`'s `hdeg` says) and on the driver's array count
   being constant in `n`.

**Scope, stated exactly.** What is crossed here is finding 3, and only
finding 3. The seam's finding 4 — `RamDriver.OrderMem`'s live-width
scalar reading `ns ≤ 0` at `initEnv`
(`BridgeSeamProbe.rootPre_initEnv_iff_ns_zero`) — is untouched and still
open; its repair is one assignment inside the decode
(`BridgeSeamProbe.lwCom_spec`, cost `4`) and belongs to the B7 re-run,
which restates the root anyway. And this is a *space* result, not a cost
result: the cover pass still charges `RamCover.coverCost`'s
`100 * n * n + …`, which is the E-order/B7 residue.
-/

namespace Lax3Proofs.Refine.BridgeCrossing

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax11.GraphEncoding
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked CsrGraph)
open Lax3Proofs.RamDriver
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax13Proofs.Compile (Layout)
open Lax3Proofs.Refine.BridgeSeamProbe (emptyWord length_emptyWord mem_emptyWord
  encodesGraph_emptyWord no_word_size_for_sparse)

/-! ## 1. The root theorem's word-bound slot, named and plugged -/

/-- **The word bound `RamDriverRoot.driverRoot_decides_sentence` takes**
(rebase E-mem/W3): the value bound of a level with the cluster arena's
pointer ceiling read at the cover-degree parameter `Kmass` rather than
at the carrier.

`Kmass` is not a new parameter. It is the root theorem's own `hdeg`
slot — the constant bounding the weak `2·cap`-reachability degree of the
ordering the cover is taken along, produced on a nowhere dense class by
`RamDriverRoot.exists_wreachDeg_of_orderP` — and that identity is what
`driverRoot_decides_sentence_bound` below checks. -/
def RootBound (B n Kmass ns cap mb : ℕ) : Prop := WordBoundK B n Kmass ns cap mb

section Plug

variable {n : ℕ} {B q_top cap mb ns W ℓ s Kmass : ℕ} {N : ℕ → ℕ}
  {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ} {x : List ℕ}
  {Kb Kb₀ Kdec Ksent : ℕ} {Ki Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}

open Classical in
/-- **The plug check.** `RootBound` is the slot: this is
`RamDriverRoot.driverRoot_decides_sentence` with the inline word bound
replaced by the name, hypothesis for hypothesis, and it type-checks only
because the two agree — *including* the degree parameter, which is the
same `Kmass` the `hdeg` hypothesis two lines below bounds. Against the
pre-W3 root, whose slot was `RamDriver.WordBound`, this term does not
elaborate. -/
theorem driverRoot_decides_sentence_bound
    -- the input word
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hO : ∀ i ≤ n, O i = offset x i) (hT : ∀ i < ns, T i = target x i)
    (hxB : ∀ v ∈ x, v < B) (hcsr : RamElim.CsrSimple G ns O T)
    (hpad0 : ∀ z, ns ≤ z → z < W → T z = 0)
    -- the parameters
    (hrank : Lax3.FirstOrder.rank φ ≤ q_top) (hcap : cap = rhoMinus 0 q_top)
    (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : RootBound B n Kmass ns cap mb) (hWB : n + W + 1 < B)
    (hpow : 2 ^ sigL cap mb ℓ < B)
    -- the mathematics of the campaign
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    -- the value bounds and the costs
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧
          Refine.ScatterDeadTurn.deadAtomK σs.β n n mb n ns n σs.t ≤ Kb)
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
      (Lax12.ColoringNumbers.wreach (RamBfs.masked G M) π (2 * cap) v).ncard ≤ Kmass)
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
      (Kdec + (Kl 0 (n + ns) + Ksent)) :=
  RamDriverRoot.driverRoot_decides_sentence hx hns hO hT hxB hcsr hpad0 hrank hcap hmb hℓ
    hB hWB hpow hQ hbnd hcostI hKsc hKmono hKs hKbase hKo hKc hKd hbinj hdeg hKl
    hKdec hatoms hKsent

end Plug

/-! ## 2. The slot is satisfiable at every word of C0's domain

`Refine.ArenaWidth.word_size_for_encoded` at the root's own degree
parameter. C0 fixes its constant before the instance:

```
∃ p c T, … ∧ ∀ n G w, C n G → ComputesInTime w p
  {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w} … T
```

so the statement to prove is: **one** `c` — read off the compile layout
and the constant profile `(Kmass, cap, mb)`, all of them constants of
the class and the sentence — then every `n`, every admissible `w` and
every member `x` of the domain, then a value bound satisfying the
layout's fits-words condition *and* the root's slot. -/

section Satisfiable

variable {n ns w : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}

/-- **The root's word bound exists at every word of C0's domain.** -/
theorem word_size_for_root (L : Layout) (hA : 1 ≤ L.arrays.length) (Kmass cap mb : ℕ)
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hdom : ∀ v ∈ x, ArenaWidth.wordConst L Kmass cap mb * (x.length + v + 1) ≤ 2 ^ w) :
    ∃ B, L.FitsWords B w ∧ RootBound B n Kmass ns cap mb :=
  ArenaWidth.word_size_for_encoded L hA Kmass cap mb hx hns hdom

/-- The same in C0's own quantifier order: the constant first, then the
instance, the word and the word length. -/
theorem exists_wordConst_root (L : Layout) (hA : 1 ≤ L.arrays.length) (Kmass cap mb : ℕ) :
    ∃ c : ℕ, 0 < c ∧ ∀ (n ns w : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
      EncodesGraph x n G → ns = 2 * edgeCount x →
      (∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w) →
      ∃ B, L.FitsWords B w ∧ RootBound B n Kmass ns cap mb :=
  ArenaWidth.exists_wordConst L hA Kmass cap mb

end Satisfiable

/-! ## 3. The sharp form: the seam probe no longer refutes the root -/

section Sharp

/-- **The flip, at the refuting instance itself.** One `n`, one word,
one word length: the very `w` at which
`BridgeSeamProbe.no_word_size_for_sparse` refutes the retired
`RamDriver.WordBound` for *every* value bound admits a value bound for
the root's restated slot. The two halves are read off the same C0 domain
membership, so this is not two scopes compared — it is the same seam,
before and after the arena width left the word bound. -/
theorem root_flip_at_the_refuting_instance (L : Layout) (hA : 1 ≤ L.arrays.length)
    (Kmass cap mb n : ℕ)
    (hcross : 4 * ArenaWidth.wordConst L Kmass cap mb * (n + 2) ≤ n * n) :
    ∃ w : ℕ,
      (∀ B ns' cap' mb' : ℕ, L.FitsWords B w → ¬ WordBound B n ns' cap' mb') ∧
      (∃ B, L.FitsWords B w ∧ RootBound B n Kmass 0 cap mb) :=
  ArenaWidth.flip_at_the_refuting_instance L hA Kmass cap mb n hcross

/-- **The seam probe's own theorem, restated at the root's slot, is
false.** `BridgeSeamProbe.no_word_size_for_sparse` says: for every
constant and every instance past its crossover there is an admissible
word length at which no value bound satisfies both `FitsWords` and the
driver's word bound. With the driver's word bound replaced by the one
the root now carries, that statement fails — at the layout's own
constant, at the first instance past its crossover.

This is the acceptance criterion of W3: the argument that killed the
bridge does not merely fail to apply, it is refutable.

Two of the probe's universal quantifiers move outside, and they have to:
the layout and the constant profile `(Kmass, cap, mb)` are constants of
the class and the sentence, chosen before the instance. §4's controls
are what says that is not a loophole — the statement is false again the
moment the degree parameter or the array count is allowed to grow with
`n`. -/
theorem no_word_size_at_root (L : Layout) (hA : 1 ≤ L.arrays.length) (Kmass cap mb : ℕ) :
    ¬ ∀ (c n : ℕ), 0 < c → 4 * c * (n + 2) ≤ n * n →
      ∃ w : ℕ, EncodesGraph (emptyWord n) n (⊥ : SimpleGraph (Fin n)) ∧
        (∀ v ∈ emptyWord n, c * ((emptyWord n).length + v + 1) ≤ 2 ^ w) ∧
        ∀ (B ns : ℕ), L.FitsWords B w → ¬ RootBound B n Kmass ns cap mb := by
  intro h
  obtain ⟨c, hc⟩ : ∃ c, c = ArenaWidth.wordConst L Kmass cap mb := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; exact ArenaWidth.wordConst_pos L Kmass cap mb
  obtain ⟨n, hn⟩ : ∃ n, n = 8 * c + 16 := ⟨_, rfl⟩
  have hcross : 4 * c * (n + 2) ≤ n * n := by rw [hn]; nlinarith
  obtain ⟨w, -, hdom, hkill⟩ := h c n hcpos hcross
  obtain ⟨B, hfit, hwb⟩ :=
    word_size_for_root (n := n) (ns := 0) (w := w) L hA Kmass cap mb
      (G := (⊥ : SimpleGraph (Fin n))) (encodesGraph_emptyWord n)
      (by rw [show edgeCount (emptyWord n) = 0 from rfl])
      (by rw [← hc]; exact hdom)
  exact hkill B 0 hfit hwb

/-- **The control that makes the last theorem bite**: the *same
statement shape*, with the root's slot replaced by the bound the root
carried before W3, is **true** — it is
`BridgeSeamProbe.no_word_size_for_sparse`, with the layout and the
profile pulled out exactly as in `no_word_size_at_root`.

So the difference between the two is the slot and nothing else: not the
quantifier order, not the witness family, not the layout's position.
`no_word_size_at_root` refutes at `RootBound` precisely what this proves
at `RamDriver.WordBound`. -/
theorem word_size_at_carrier (L : Layout) (cap mb : ℕ) :
    ∀ (c n : ℕ), 0 < c → 4 * c * (n + 2) ≤ n * n →
      ∃ w : ℕ, EncodesGraph (emptyWord n) n (⊥ : SimpleGraph (Fin n)) ∧
        (∀ v ∈ emptyWord n, c * ((emptyWord n).length + v + 1) ≤ 2 ^ w) ∧
        ∀ (B ns : ℕ), L.FitsWords B w → ¬ WordBound B n ns cap mb := by
  intro c n hc hcross
  obtain ⟨w, henc, hdom, hkill⟩ := no_word_size_for_sparse c n hc hcross
  exact ⟨w, henc, hdom, fun B ns hfit => hkill L B ns cap mb hfit⟩

end Sharp

/-! ## 4. The controls, and they bite

Three refutations of §2's statement, each with one ingredient of the
root's slot changed back. They are `Refine.ArenaWidth`'s controls read
at `RootBound`, so that no control is refuting something this file also
needs. -/

section Controls

/-- **Control 1 — the arena width is what does the work.** At the
retired carrier bound the same statement is false: this is the seam
probe's finding 3 in §2's shape. -/
theorem no_wordConst_at_carrier (L : Layout) (cap mb : ℕ) :
    ¬ ∃ c : ℕ, 0 < c ∧ ∀ (n ns w : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
      EncodesGraph x n G → ns = 2 * edgeCount x →
      (∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w) →
      ∃ B, L.FitsWords B w ∧ WordBound B n ns cap mb :=
  ArenaWidth.no_wordConst_at_square L cap mb

/-- **Control 2 — `Kmass` must be a constant of the class, not of the
instance.** The root's `hdeg` slot bounds the cover degree by a `Kmass`
chosen before the instance (`RamDriverRoot.exists_wreachDeg_of_orderP`
produces it from nowhere denseness). If it were allowed to grow like
`n`, the root's slot would be the carrier bound again and control 1
would apply. -/
theorem no_wordConst_at_linear_degree (L : Layout) (cap mb : ℕ) :
    ¬ ∃ c : ℕ, 0 < c ∧ ∀ (n ns w : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
      EncodesGraph x n G → ns = 2 * edgeCount x →
      (∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w) →
      ∃ B, L.FitsWords B w ∧ RootBound B n n ns cap mb :=
  ArenaWidth.no_wordConst_at_linear_degree L cap mb

/-- **Control 3 — the layout's array count must be constant in the
instance.** With an array count growing like `n`, `span B = n * B` is
quadratic again and no constant works even at the almost-linear arena
width. The driver's own count is constant in `n`: its per-depth, colour
and table arrays are indexed by `ℓ`, `sigL cap mb j` and
`tablesAt q_top cap mb φ j`, all functions of the sentence and the
class. -/
theorem no_wordConst_growing_layout (Kmass cap mb : ℕ) :
    ¬ ∃ c : ℕ, 0 < c ∧ ∀ (n ns w : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
      EncodesGraph x n G → ns = 2 * edgeCount x →
      (∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w) →
      ∃ B, (ArenaWidth.bigLayout n).FitsWords B w ∧ RootBound B n Kmass ns cap mb :=
  ArenaWidth.no_wordConst_growing_layout Kmass cap mb

/-- **Control 4 — the crossing is not vacuous.** `FitsWords` and the
root's slot are jointly satisfiable at numerals: one array, no scalars,
no temps; cover degree `8`, radius cap `2`, padded width `10`; the
edgeless word on `200` vertices, `|x| = 203`, at the value bound
`ArenaWidth.boundAt 203 8 2 10 = 1844` and word length `w = 11`. -/
example : (⟨[], ["xmem"], 0⟩ : Layout).FitsWords 1844 11 ∧ RootBound 1844 200 8 0 2 10 :=
  ⟨⟨by norm_num, by norm_num, by norm_num [Lax13Proofs.Compile.Layout.span]⟩, by
    constructor <;> norm_num [WordBoundK]⟩

-- the same numbers, evaluated: the crossover instance of
-- `no_word_size_at_root` at the realistic profile
#guard ArenaWidth.wordConst ⟨[], ["xmem"], 0⟩ 8 2 10 = 27
#guard 4 * 27 * (200 + 2) ≤ 200 * 200
#guard ArenaWidth.boundAt 203 8 2 10 = 1844
-- the root's slot holds there …
#guard 200 * 8 + 200 + 0 + 2 * 2 + 2 < 1844 && 10 < 1844
-- … and the retired carrier bound does not, at the same value bound
#guard ¬ (200 * 200 + 0 + 2 * 2 + 2 < 1844)

end Controls

/-! ## 5. The axiom check -/

#print axioms driverRoot_decides_sentence_bound
#print axioms word_size_for_root
#print axioms exists_wordConst_root
#print axioms root_flip_at_the_refuting_instance
#print axioms no_word_size_at_root
#print axioms word_size_at_carrier
#print axioms no_wordConst_at_carrier
#print axioms no_wordConst_at_linear_degree
#print axioms no_wordConst_growing_layout

end Lax3Proofs.Refine.BridgeCrossing
