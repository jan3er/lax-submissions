import Lax3Proofs.RamDriverRoot
import Lax3Proofs.RamDriverDedup
import Lax13Proofs.Transfer

/-!
**The `Spec → ComputesInTime` bridge seam, probed** (ND-MC rebase, the
last never-probed seam; supervisor recommendation of the 2026-07-31
wrap).

`Lax13Proofs.Refine.Codegen.solves_of_spec` is the only door out of the
IMP+ layer, and it is narrow in four places at once. This file compiles
what each of them demands of
`RamDriverRoot.driverRoot_decides_sentence`, in the house style of
`C0Probe` and `Refine.G2CostProbe`: a witness where the seam closes, a
refutation where it does not, and negative controls on both.

**Finding 3 is REPAIRED** (rebase E-mem, leaves W1–W3; the repair route
is `Refine.ArenaWidth`, the crossing is `Refine.BridgeCrossing`). What
§5 proves is unchanged and still true — it is a statement about
`RamDriver.WordBound`, the carrier-width value bound — but that is no
longer the bound the root theorem carries. Since W3,
`RamDriverRoot.driverRoot_decides_sentence` takes
`RamDriver.WordBoundK B n Kmass ns cap mb`, whose arena clause is
`n * Kmass + n + …` with `Kmass` the cover-degree constant its own
`hdeg` slot bounds; `Refine.BridgeCrossing.no_word_size_at_root`
compiles that §5's own argument, restated at that slot, is **false**.
The account below is the finding as it stood, kept because the repair is
only intelligible against it.

**Finding 3 — the layout does not fit in the words C0 hands it.**
`§5`. This was the headline, and it is *unconditional*: it needs no
width path, no `chainWidth`, no cost side condition and no `R > 0`
coupling. The driver addresses an `n × n` cluster arena — `xmem` and
`xmmName j` are `n * n` cells in `RamDriver.LevelMem` / `DepthMem` —
so its value bound clause `RamDriver.WordBound` pinned
`n * n + ns + 2 * cap + 2 < B`. `Compile.Layout.FitsWords B w` pins
`B ≤ 2 ^ w`. And C0's domain only *guarantees* words above
`c · (|x| + v + 1)`, so at the smallest admissible word size
`2 ^ w ≤ 2 · c · (|x| + max x + 1)` — linear in `|x|`, where the driver
needs quadratic in `n`. On a sparse member the two are jointly
unsatisfiable for every `c` at every large enough `n`
(`no_word_size_for_sparse`, `#guard`ed at the crossover). Nothing in
the cost interface is involved: this is a *space* fact, and no cost
repair reaches it. The repair is at the level of the driver's memory —
the `n × n` block-membership arena must become an almost-linear
structure (the R1.6/R1.8 block-driven rewrite), which the two B7
findings already asked for on cost grounds and this finding now makes
mandatory for existence. **That reading of the repair was wrong, and
`Refine.ArenaWidth` §1 is why**: `Compile.Layout.span` never sees the
length of an IMP+ array, so the `n × n` allocation reaches the word
length only through the literal `n * n` inside `WordBound`. The arena
stays exactly where it is; what left the word bound is the *pointer
ceiling*.

**Finding 4 — the landed precondition is not `initEnv`-reachable.**
`§2`–`§4`. `solves_of_spec` demands the precondition be *exactly*
`σ = Imp.initEnv ext x`, and `initEnv` zeroes every scalar. Of the
eight conjuncts of the root theorem's precondition, seven are lengths,
zero-clauses and word-clauses, and all seven transfer to `initEnv` for
free — the array-allocation half of the prologue costs nothing, because
`ext` supplies it (`rootPre_initEnv_of_ns_zero`; this is the compiled
satisfiability half). The eighth is `RamDriver.OrderMem`'s live-width
scalar `ns ≤ σ.vars "lw"`, and at `initEnv` that reads `ns ≤ 0`. So the
landed `Spec` feeds `solves_of_spec` on edge-free inputs and on nothing
else (`rootPre_initEnv_iff_ns_zero`). A prologue cannot repair it in
place either: the same precondition demands `σ.inp = x`, the *untouched*
tape, because `RamDriver.decodeCom` re-reads the word itself — and a
run that leaves the tape whole has consumed nothing of it
(`prologue_consumes_nothing`), while `ns = 2 · edgeCount x` lives on
that tape and `.read` is the only rule of the semantics that mentions
it. The splice point is therefore *inside* the decode, next to
`.read "m"`, and the cost of the repair is one assignment
(`lwCom_spec`, cost `4`) — not a floor.
-/

namespace Lax3Proofs.Refine.BridgeSeamProbe

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax11.GraphEncoding
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked CsrGraph)
open Lax3Proofs.RamDriver
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## 1. The precondition of the landed root theorem, named

`RootPre` is `driverRoot_decides_sentence`'s precondition verbatim. The
plug check is `driverRoot_decides_sentence_pre` below: the root theorem
is restated with `RootPre` in place of the inline conjunction and proved
by the theorem itself, so the name is the driver's reading and not a
lookalike — it would break the moment either side drifted. -/

/-- The eight conjuncts a caller must produce to enter
`RamDriver.driverRoot`. -/
def RootPre (B n ns W q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) (x : List ℕ)
    (σ : Env) : Prop :=
  DecodeMem n ns W σ ∧ LevelMem B n cap mb σ ∧ DepthMem n cap mb σ ∧
    OrderMem B n ns W σ ∧ TablesSized q_top cap mb φ n σ ∧
    BaseArrs B q_top cap mb ℓ φ σ ∧ σ.inp = x ∧ σ.out = []

section Plug

variable {n : ℕ} {B q_top cap mb ns W ℓ s Kmass : ℕ} {N : ℕ → ℕ}
  {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ} {x : List ℕ}
  {Kb Kb₀ Ki₀ Kdec Ksent : ℕ} {Ki Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}

open Classical in
/-- **The plug check.** `RootPre` is the precondition the landed root
theorem actually has: this is `driverRoot_decides_sentence` with the
inline conjunction replaced by the name, hypothesis for hypothesis, and
it type-checks only because the two agree. -/
theorem driverRoot_decides_sentence_pre
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
    Spec B (RootPre B n ns W q_top cap mb ℓ φ x)
      (driverRoot q_top cap mb 0 ℓ φ)
      (fun _ σ' => σ'.out = [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
      (Kdec + (Kl 0 (n + ns) + Ksent)) :=
  RamDriverRoot.driverRoot_decides_sentence hx hns hO hT hxB hcsr hpad0 hrank hcap hmb hℓ
    hB hWB hpow hQ hbnd hcostI hKsc hKmono hKs hKbase hKo hKc hKd hbinj hdeg hKl
    hKdec hatoms hKsent

end Plug

/-! ## 2. Question 1, the refutation: `initEnv` cannot enter the driver

`solves_of_spec` wants the precondition to be *exactly*
`fun σ => σ = Imp.initEnv ext x`, and `Imp.initEnv` sets every scalar to
zero. `RamDriver.OrderMem`'s live-width clause asks for a scalar above
`ns`. -/

section InitEnv

variable {ext : String → ℕ} {x : List ℕ} {B n ns W : ℕ}

@[simp] theorem vars_initEnv (y : String) : (initEnv ext x).vars y = 0 := rfl

@[simp] theorem arrs_initEnv (a : String) :
    (initEnv ext x).arrs a = List.replicate (ext a) 0 := rfl

@[simp] theorem length_arrs_initEnv (a : String) :
    ((initEnv ext x).arrs a).length = ext a := by simp

/-- **The live width is the whole obstruction.** `OrderMem` asks
`ns ≤ σ.vars "lw"`; a fresh environment has no scalars. -/
theorem orderMem_initEnv (h : OrderMem B n ns W (initEnv ext x)) : ns = 0 := by
  have := h.2.1.1
  simp only [vars_initEnv] at this
  omega

/-- **Question 1, the refutation.** On any input word with an edge, no
choice of array lengths makes the fresh environment satisfy the landed
root theorem's precondition. -/
theorem not_rootPre_initEnv {q_top cap mb ℓ : ℕ} {φ : Lax3.FirstOrder.FO 0} (hns : 0 < ns) :
    ¬ RootPre B n ns W q_top cap mb ℓ φ x (initEnv ext x) := by
  intro h
  have := orderMem_initEnv h.2.2.2.1
  omega

/-- …and the consequence at the door. The only route from the landed
`Spec` to the shape `solves_of_spec` consumes is precondition
weakening, and weakening needs exactly the fact refuted above. -/
theorem spec_initEnv_of_rootSpec {q_top cap mb ℓ K : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {c : Com} {Q : Env → Env → Prop}
    (h : Spec B (RootPre B n ns W q_top cap mb ℓ φ x) c Q K)
    (hpre : RootPre B n ns W q_top cap mb ℓ φ x (initEnv ext x)) :
    Spec B (fun σ => σ = initEnv ext x) c Q K := by
  intro σ hσ; subst hσ; exact h _ hpre

end InitEnv

/-! ## 3. Question 1, the witness: the array half of the prologue is free

Every other conjunct of the precondition is a length, a
"these cells are zero" or a "these cells are words", and `initEnv`'s
arrays are `ext a` zeros. So an environment satisfying the memory
clauses is copied onto `initEnv` by reading its own array lengths off as
`ext` — no program, no cost. This is the satisfiability half of the
seam, in the standing rule's sense: the repair target is shown reachable
before any repair is proposed. -/

section Transfer

variable {x : List ℕ} {B n ns W q_top cap mb ℓ : ℕ} {φ : Lax3.FirstOrder.FO 0} {σ : Env}

/-- The array lengths of an environment, as a marshalling descriptor. -/
def extOf (σ : Env) : String → ℕ := fun a => (σ.arrs a).length

@[simp] theorem length_arrs_initEnv_extOf (a : String) :
    ((initEnv (extOf σ) x).arrs a).length = (σ.arrs a).length := by
  simp [extOf]

/-- A fresh array of the right length is an `arrOf`. -/
theorem arrOf_initEnv {a : String} {k : ℕ} (h : (σ.arrs a).length = k) :
    ∃ g : ℕ → ℕ, (initEnv (extOf σ) x).arrs a = arrOf k g := by
  refine ⟨fun _ => 0, ?_⟩
  rw [arrs_initEnv, show extOf σ a = k from h]
  simp [arrOf, List.map_const']

/-- A `Sized` clause is a statement about lengths, so it transfers. -/
theorem sized_initEnv {l : List (String × ℕ)} (h : Sized l σ) :
    Sized l (initEnv (extOf σ) x) := fun _p hp => arrOf_initEnv (h.length hp)

/-- The cells of a fresh array are zero, so every zero clause and every
word clause transfers (the latter as soon as the bound is nontrivial). -/
theorem mem_initEnv_eq_zero {ext : String → ℕ} {a : String} {v : ℕ}
    (h : v ∈ (initEnv ext x).arrs a) : v = 0 := by
  rw [arrs_initEnv] at h
  exact List.eq_of_mem_replicate h

theorem mem_initEnv_lt {ext : String → ℕ} {a : String} {v : ℕ} (hB : 0 < B)
    (h : v ∈ (initEnv ext x).arrs a) : v < B := by
  rw [mem_initEnv_eq_zero h]; exact hB

theorem getD_arrs_initEnv {ext : String → ℕ} (a : String) (j : ℕ) :
    ((initEnv ext x).arrs a).getD j 0 = 0 := by
  rw [arrs_initEnv, List.getD_eq_getElem?_getD]
  rcases lt_or_ge j (ext a) with h | h
  · rw [List.getElem?_replicate_of_lt h]; rfl
  · rw [List.getElem?_eq_none (by simpa using h)]; rfl

theorem decodeMem_initEnv (h : DecodeMem n ns W σ) :
    DecodeMem n 0 W (initEnv (extOf σ) x) := by
  obtain ⟨h1, h2, -, h4, h5⟩ := h
  exact ⟨by simpa using h1, by simpa using h2, fun j _ _ => getD_arrs_initEnv _ _,
    by simpa using h4, by simpa using h5⟩

theorem levelMem_initEnv (hB : 0 < B) (h : LevelMem B n cap mb σ) :
    LevelMem B n cap mb (initEnv (extOf σ) x) :=
  ⟨sized_initEnv h.1, fun _ hv => mem_initEnv_lt hB hv, fun _ hv => mem_initEnv_lt hB hv⟩

theorem depthMem_initEnv (h : DepthMem n cap mb σ) :
    DepthMem n cap mb (initEnv (extOf σ) x) := fun j =>
  ⟨sized_initEnv (h j).1, fun c hc => by
    obtain ⟨g, hg⟩ := (h j).2 c hc
    exact arrOf_initEnv (by rw [hg, length_arrOf])⟩

theorem tablesSized_initEnv (h : TablesSized q_top cap mb φ n σ) :
    TablesSized q_top cap mb φ n (initEnv (extOf σ) x) := fun j => sized_initEnv (h j)

theorem baseArrs_initEnv (h : BaseArrs B q_top cap mb ℓ φ σ) :
    BaseArrs B q_top cap mb ℓ φ (initEnv (extOf σ) x) :=
  ⟨sized_initEnv h.1,
    fun jd i hi => botMem_of_length (fun a => length_arrs_initEnv_extOf a) _ "bb" (h.2 jd i hi)⟩

theorem orderMem_initEnv_of (hB : 0 < B) (h : OrderMem B n ns W σ) :
    OrderMem B n 0 W (initEnv (extOf σ) x) := by
  obtain ⟨-, -, hsz, hz⟩ := h
  exact ⟨Nat.zero_le _, ⟨Nat.zero_le _, Nat.zero_le _⟩, sized_initEnv hsz,
    fun _ hv => mem_initEnv_eq_zero hv, fun _ hv => mem_initEnv_eq_zero hv,
    fun _ hv => mem_initEnv_eq_zero hv, fun _ hv => mem_initEnv_eq_zero hv,
    fun _ hv => mem_initEnv_eq_zero hv, fun _ hv => mem_initEnv_eq_zero hv,
    fun _ hv => mem_initEnv_eq_zero hv, fun _ hv => mem_initEnv_eq_zero hv,
    fun _ hv => mem_initEnv_lt hB hv, fun _ hv => mem_initEnv_lt hB hv⟩

/-- **Question 1, the witness.** Any environment that satisfies the
memory clauses hands them to a fresh environment on the same input, at
`ns = 0` — the whole array-allocation half of the prologue is `ext`, and
`ext` is free. -/
theorem rootPre_initEnv_of_ns_zero (hB : 0 < B) (h : RootPre B n ns W q_top cap mb ℓ φ x σ) :
    RootPre B n 0 W q_top cap mb ℓ φ x (initEnv (extOf σ) x) :=
  ⟨decodeMem_initEnv h.1, levelMem_initEnv hB h.2.1, depthMem_initEnv h.2.2.1,
    orderMem_initEnv_of hB h.2.2.2.1, tablesSized_initEnv h.2.2.2.2.1,
    baseArrs_initEnv h.2.2.2.2.2.1, rfl, rfl⟩

/-- **The seam, sharp.** Given that the precondition is satisfiable at
all, it is satisfiable at a *fresh* environment exactly when the input
word has no edges. Seven of the eight conjuncts cost nothing; the
eighth is unreachable. -/
theorem rootPre_initEnv_iff_ns_zero (hB : 0 < B)
    (hsat : RootPre B n ns W q_top cap mb ℓ φ x σ) :
    (∃ ext, RootPre B n ns W q_top cap mb ℓ φ x (initEnv ext x)) ↔ ns = 0 := by
  constructor
  · rintro ⟨ext, h⟩; exact orderMem_initEnv h.2.2.2.1
  · rintro rfl; exact ⟨extOf σ, rootPre_initEnv_of_ns_zero hB hsat⟩

end Transfer

/-! ## 4. Question 2, the prologue: the tape is locked, the repair is one
assignment

The array half being free (§3), what a prologue owes is the single
scalar `ns ≤ σ.vars "lw"`. Its value is `2 · edgeCount x`, which lives
on the input tape — and the same precondition asks for `σ.inp = x`,
because `RamDriver.decodeCom` re-reads the word itself. The two are
incompatible: a run hands on a *suffix* of the tape it was given
(`bigStep_inp_suffix` — `.read` is the only rule of `Imp.BigStep` that
mentions `inp`), so a prologue that hands on the whole word has consumed
none of it (`prologue_consumes_nothing`), and a prologue that consumes
even one cell has already broken the conjunct (`read_breaks_inp`).

So the splice point is *inside* the decode, next to `.read "m"`, and
the cost of the repair is one assignment (`lwCom_spec`, cost `4`): the
prologue is not a floor. What it is, is a **frozen-surface repair** —
`RamDriver.decodeCom`, `RamDriverIO.decodeImplements` and hence the root
statement move — which is why it belongs with the `driverRootD`
restatement of the B7 re-run and not before it. -/

section Prologue

/-- **The tape only shrinks, and only at a `read`.** -/
theorem bigStep_inp_suffix {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStep c σ σ' k) :
    ∃ pre, σ.inp = pre ++ σ'.inp := by
  induction h with
  | skip => exact ⟨[], rfl⟩
  | assign _ => exact ⟨[], rfl⟩
  | store _ _ _ => exact ⟨[], rfl⟩
  | seq _ _ ih ih' =>
    obtain ⟨p₁, h₁⟩ := ih
    obtain ⟨p₂, h₂⟩ := ih'
    exact ⟨p₁ ++ p₂, by rw [h₁, h₂, List.append_assoc]⟩
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' =>
    obtain ⟨p₁, h₁⟩ := ih
    obtain ⟨p₂, h₂⟩ := ih'
    exact ⟨p₁ ++ p₂, by rw [h₁, h₂, List.append_assoc]⟩
  | while_false _ => exact ⟨[], rfl⟩
  | read h => exact ⟨[_], by simpa using h⟩
  | write _ => exact ⟨[], rfl⟩

theorem run_inp_suffix {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) :
    ∃ pre, σ.inp = pre ++ σ'.inp := by
  obtain ⟨k, -, hbs⟩ := h
  exact bigStep_inp_suffix hbs.bigStep

/-- **The tape lock.** A prologue that must hand `driverRoot` the
untouched word has taken nothing off it: every consumed prefix is
empty. -/
theorem prologue_consumes_nothing {B : ℕ} {p : Com} {σ σ' : Env} {K : ℕ}
    (h : Run B p σ σ' K) (heq : σ'.inp = σ.inp) :
    ∃ pre, σ.inp = pre ++ σ'.inp ∧ pre = [] := by
  obtain ⟨pre, hpre⟩ := run_inp_suffix h
  refine ⟨pre, hpre, ?_⟩
  have hlen := congrArg List.length hpre
  rw [List.length_append, heq] at hlen
  simpa using hlen.symm

/-- …and one cell is already one too many: a prologue that reads breaks
the conjunct the decode needs. -/
theorem read_breaks_inp {B : ℕ} {y : String} {σ σ' : Env} {K v : ℕ} {rest : List ℕ}
    (h : Run B (.read y) σ σ' K) (hσ : σ.inp = v :: rest) : σ'.inp ≠ σ.inp := by
  obtain ⟨k, -, hbs⟩ := h
  cases hbs.bigStep with
  | read h' =>
    rw [hσ] at h'
    cases h'
    rw [hσ]
    simp

/-- The repair: the live width, set from the decode's own slot count. -/
def lwCom : Com := .assign "lw" (.add (.var "m") (.var "m"))

/-- Its cost, as a numeral. -/
example : 1 + (Expr.add (.var "m") (.var "m")).size = 4 := rfl

/-- Setting the live width is all the memory clause is missing: at
`ns = 0` the clause is exactly the arrays, and a scalar assignment
carries them across. -/
theorem orderMem_of_lw {B n ns W v : ℕ} {σ : Env} (h : OrderMem B n 0 W σ)
    (hle : ns ≤ v) (hv : v ≤ W) : OrderMem B n ns W (σ.setVar "lw" v) := by
  obtain ⟨-, -, hsz, hz⟩ := h
  refine ⟨le_trans hle hv, ⟨?_, ?_⟩, hsz.setVar _ _, ?_⟩
  · rw [vars_setVar, if_pos rfl]; exact hle
  · rw [vars_setVar, if_pos rfl]; exact hv
  · simpa using hz

/-- **The repair, compiled.** One assignment, cost `4`, lands the clause
the fresh environment cannot carry — provided the decode's slot-count
scalar is in hand, which it is only *after* `decodeCom`'s `.read "m"`. -/
theorem lwCom_spec {B n ns W e : ℕ} (hB : 2 * e < B) :
    Spec B (fun σ => σ.vars "m" = e ∧ OrderMem B n 0 W σ ∧ ns ≤ 2 * e ∧ 2 * e ≤ W)
      lwCom (fun _ σ' => OrderMem B n ns W σ') 4 := by
  rintro σ ⟨hm, hmem, hns, hW⟩
  have hev : (Expr.add (.var "m") (.var "m")).evalB B σ = some (2 * e) := by
    have hlt : e < B := by omega
    simp only [Expr.evalB, hm, fit_self hlt, Option.bind_some, Bop.apply]
    rw [show e + e = 2 * e by ring]
    exact fit_self hB
  exact ⟨_, Run.assign (x := "lw") hev, orderMem_of_lw hmem hns hW⟩

/-! ### Where the repair lands

G1's composed decode already carries the defect and already computes the
number: `RamDriverDedup.dedupCom` opens with
`.assign "dq" (.add (.var "m") (.var "m"))` — the slot count, off the
decode's own `m`, in exactly `lwCom`'s shape — while
`RamDriverDedup.DecodeImplementsD`'s precondition still asks for
`RamDriver.OrderMem B n ns W`, the unreachable form. Its other memory
clause `RamDriverDedup.DedupMem` is a length and a zero clause, so it is
free at `initEnv` like the rest. The repair is therefore local to the
composed decode phase: set `"lw"` beside `"dq"`, and let the phase's
precondition ask for `OrderMem B n 0 W` and its postcondition deliver
`OrderMem B n ns W`. -/

theorem dedupMem_initEnv {n : ℕ} {σ : Env} {x : List ℕ} (h : RamDriverDedup.DedupMem n σ) :
    RamDriverDedup.DedupMem n (initEnv (extOf σ) x) :=
  ⟨by rw [length_arrs_initEnv_extOf]; exact h.1, fun _ hv => mem_initEnv_eq_zero hv⟩

/-- **G1's decode Prop inherits the obstruction**, and the application is
the plug: `DecodeImplementsD` is consumed at its own precondition, so
the conjunct list is the landed one and not a lookalike. If the composed
decode could ever start from a fresh environment, the word would have no
edges. -/
theorem decodeImplementsD_initEnv_edgeless {n : ℕ} {G : SimpleGraph (Fin n)}
    {B ns W K : ℕ} {T : ℕ → ℕ} {x : List ℕ} {ext : String → ℕ}
    (hD : RamDriverDedup.DecodeImplementsD B x G ns W T K)
    (h1 : ∀ v ∈ x, v < B) (h2 : n + 1 < B) (h3 : ns < B) (h4 : W < B) (h5 : ns ≤ W)
    (h6 : ∀ z, ns ≤ z → z < W → T z = 0)
    (hdec : DecodeMem n ns W (initEnv ext x)) (hord : OrderMem B n ns W (initEnv ext x))
    (hded : RamDriverDedup.DedupMem n (initEnv ext x)) : ns = 0 := by
  obtain ⟨-, -, -⟩ := hD h1 h2 h3 h4 h5 h6 (initEnv ext x) ⟨hdec, hord, hded, rfl, rfl⟩
  exact orderMem_initEnv hord

/-- **The one step of §4 that is not compiled here.** A prologue that
consumes nothing of the tape can still, in principle, be handed
different *array lengths* on different inputs, and `ext` is chosen per
input; ruling that out is a bisimulation over the array-length
component of the state (the two runs' contents agree wherever both are
in range, and where only one is in range the other has no derivation at
all). It is stated, not proved, because nothing in this file's findings
rests on it: §5's refutation is unconditional and kills the assembly on
its own, and the placement conclusion of §4 already follows from
`read_breaks_inp` for any prologue that reads. -/
def PrologueBlind : Prop :=
  ∀ (p : Com) (B : ℕ) (ext₁ ext₂ : String → ℕ) (x₁ x₂ : List ℕ) (σ₁ σ₂ : Env) (K₁ K₂ : ℕ),
    Run B p (initEnv ext₁ x₁) σ₁ K₁ → Run B p (initEnv ext₂ x₂) σ₂ K₂ →
    σ₁.inp = x₁ → σ₂.inp = x₂ → σ₁.vars = σ₂.vars

end Prologue

/-! ## 5. Question 3, the refutation: the layout does not fit in C0's words

`computesInTime_of_spec` adds `L.FitsWords (B x) w`, whose `bound` field
is `B ≤ 2 ^ w`. `RamDriver.WordBound` — the root theorem's `hB` slot
until W3, at `R = 0`, with no width path and no cost side condition in
sight — is `n * n + ns + 2 * cap + 2 < B`, because the cover pass forms
the cluster arena's pointer as a *value* and the arena is `n * n` cells
(`RamDriver.LevelMem`, `RamDriver.DepthMem`). So the assembly needed
`n * n < 2 ^ w`.

**The root no longer carries this bound** (rebase E-mem/W3): its slot is
`RamDriver.WordBoundK B n Kmass ns cap mb`, and everything below is
therefore a theorem about the *retired* form. It is kept, and kept
sharp, because it is what the repair is measured against —
`Refine.ArenaWidth`'s flip and `Refine.BridgeCrossing`'s crossing are
both stated against `no_word_size_for_sparse` at the very instance it
kills.

C0 gives the opposite. Its domain is
`{x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w}`,
which *admits* every word length above `c · (|x| + max x + 1)` — and the
statement quantifies over **all** `w`, so the smallest admissible one is
in scope, where `2 ^ w ≤ 2 · c · (|x| + max x + 1)`. On a sparse member
that is linear in `n` where the driver needs `n ^ 2`.

The constant is chosen before the instance, exactly as in
`C0Probe`, so one large instance is the refutation.

**Scope, stated exactly.** The witness is the edgeless graph on `n`
vertices — a member of a nowhere dense class, so it is an instance C0
demands — and what is refuted is the *route*:
`driverRoot_decides_sentence` fed to
`Codegen.computesInTime_of_spec`. Nothing here refutes C0 itself, and
nothing here is about the cost interface. The same arithmetic bites at
every class member whose word is sub-quadratic in `n`, which is
asymptotically every member of a nowhere dense class; that general form
needs the class's own density theorem and is not compiled here. -/

section Layout

/-- The word of the edgeless graph on `n` vertices: two header cells and
`n + 1` zero offsets, no targets. `|x| = n + 3`, every cell `n` or
`0`. -/
def emptyWord (n : ℕ) : List ℕ := n :: 0 :: List.replicate (n + 1) 0

theorem length_emptyWord (n : ℕ) : (emptyWord n).length = n + 3 := by
  simp [emptyWord]

theorem mem_emptyWord {n v : ℕ} (h : v ∈ emptyWord n) : v = n ∨ v = 0 := by
  simp only [emptyWord, List.mem_cons] at h
  rcases h with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr (List.eq_of_mem_replicate h)

theorem getD_replicate_zero (k j : ℕ) : (List.replicate k (0 : ℕ)).getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge j k with h | h
  · rw [List.getElem?_replicate_of_lt h]; rfl
  · rw [List.getElem?_eq_none (by simpa using h)]; rfl

theorem offset_emptyWord (n i : ℕ) : offset (emptyWord n) i = 0 := by
  rw [offset, show 2 + i = i + 1 + 1 by omega]
  simp only [emptyWord, List.getD_cons_succ]
  exact getD_replicate_zero _ _

/-- The witness is a genuine encoding. -/
theorem encodesGraph_emptyWord (n : ℕ) :
    EncodesGraph (emptyWord n) n (⊥ : SimpleGraph (Fin n)) where
  vertexCount_eq := rfl
  length_eq := by
    rw [length_emptyWord, show edgeCount (emptyWord n) = 0 from rfl]; omega
  offset_zero := offset_emptyWord n 0
  offset_last := by rw [offset_emptyWord]; rfl
  offset_mono := fun i _ => by rw [offset_emptyWord, offset_emptyWord]
  target_lt := fun j hj => by simp [edgeCount, emptyWord] at hj
  adj_iff := fun u v => by
    rw [SimpleGraph.bot_adj]
    constructor
    · exact fun h => h.elim
    · rintro ⟨j, -, hj, -⟩
      rw [offset_emptyWord] at hj
      exact absurd hj (by omega)

/-- Every positive number is between a power of two and its double. -/
theorem exists_pow_between {m : ℕ} (hm : 0 < m) : ∃ w : ℕ, m ≤ 2 ^ w ∧ 2 ^ w ≤ 2 * m := by
  refine ⟨Nat.log 2 m + 1, le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) m), ?_⟩
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))

/-- **What the layout demanded of the word length** at the carrier
bound: it is above `n ^ 2`, and every value of the layout is a word. -/
theorem sq_lt_two_pow_of_fits {L : Lax13Proofs.Compile.Layout} {B w n ns cap mb : ℕ}
    (hfit : L.FitsWords B w) (hB : WordBound B n ns cap mb) : n * n < 2 ^ w := by
  have h := hB.1
  have := hfit.bound
  omega

/-- **The same bound, read at the width parameter.** `hWB` of the root
theorem is `n + W + 1 < B`, so the free width `W` of the ordering phase
is itself below the word length — and hence, on C0's domain, below
`2 · c · (|x| + max x + 1)`. This is B7's finding 2 seen from the other
side: the `chainWidth n d D₁ R ≤ W` pin that made the cost cubic is not
merely expensive, it is unaddressable. -/
theorem width_lt_two_pow {L : Lax13Proofs.Compile.Layout} {B w n W : ℕ}
    (hfit : L.FitsWords B w) (hWB : n + W + 1 < B) : W < 2 ^ w := by
  have := hfit.bound
  omega

/-- **Question 3, the refutation — and the third boundary fact.** For
every constant `c`, at every sparse instance past the constant's
crossover, C0's own domain admits a word length at which the *carrier*
value bound and the compile layout's fits-words condition are jointly
unsatisfiable. No cost repair reaches it: the quantities are `n * n`
(the cluster arena's pointer ceiling) against `2 ^ w` (the machine's
addressable range), and the cost interface does not occur.

This is the theorem the repair is measured against.
`Refine.ArenaWidth.flip_at_the_refuting_instance` and
`Refine.BridgeCrossing` both consume *this* `w`: at the very word length
that kills `WordBound` for every value bound, the root's restated slot
has one. -/
theorem no_word_size_for_sparse (c n : ℕ) (hc : 0 < c) (hcross : 4 * c * (n + 2) ≤ n * n) :
    ∃ w : ℕ, EncodesGraph (emptyWord n) n (⊥ : SimpleGraph (Fin n)) ∧
      (∀ v ∈ emptyWord n, c * ((emptyWord n).length + v + 1) ≤ 2 ^ w) ∧
      ∀ (L : Lax13Proofs.Compile.Layout) (B ns cap mb : ℕ),
        L.FitsWords B w → ¬ WordBound B n ns cap mb := by
  obtain ⟨w, hw1, hw2⟩ := exists_pow_between (m := c * (2 * n + 4)) (by positivity)
  refine ⟨w, encodesGraph_emptyWord n, ?_, ?_⟩
  · intro v hv
    refine le_trans ?_ hw1
    rw [length_emptyWord]
    rcases mem_emptyWord hv with rfl | rfl <;> exact Nat.mul_le_mul_left c (by omega)
  · intro L B ns cap mb hfit hB
    have hsq : n * n < 2 ^ w := sq_lt_two_pow_of_fits hfit hB
    have : n * n < n * n :=
      calc n * n < 2 ^ w := hsq
        _ ≤ 2 * (c * (2 * n + 4)) := hw2
        _ = 4 * c * (n + 2) := by ring
        _ ≤ n * n := hcross
    omega

-- **The crossover is inhabited**: `c` is fixed before `n`, so at a
-- constant as generous as `10 ^ 9` the hypothesis of the refutation
-- holds at `n = 10 ^ 12`.
#guard 4 * 10 ^ 9 * (10 ^ 12 + 2) ≤ 10 ^ 12 * 10 ^ 12

-- **The negative control**: below the crossover the hypothesis fails,
-- so the theorem is not a statement about every instance — it is the
-- quantifier order, exactly as in `C0Probe`.
#guard ¬ (4 * 10 ^ 9 * (5 + 2) ≤ 5 * 5)

-- **The second negative control**: `FitsWords` and `WordBound` are not
-- contradictory on their own — they are jointly satisfiable as soon as
-- the word length is free. The refutation is about the word length C0's
-- domain admits, and nothing else.
example : (⟨[], ["a"], 1⟩ : Lax13Proofs.Compile.Layout).FitsWords 8 8 ∧
    WordBound 8 2 0 0 0 :=
  ⟨⟨by norm_num, by norm_num, by norm_num [Lax13Proofs.Compile.Layout.span]⟩, by
    constructor <;> norm_num [WordBound]⟩

end Layout

/-! ## 6. Question 4, the output side: closed

`solves_of_spec` wants `σ'.out = f x` with C0's
`f = fun _ => if Sat G Fin.elim0 φ then [1] else [0]`, and the root
theorem's postcondition is `σ'.out = [if Sat G Fin.elim0 φ then 1 else 0]`
— the same list, with the branch inside rather than outside. There is no
epilogue to pay for: the write is `RamDriver.sentenceCom`'s own, inside
`driverRoot`, so `Harness.writeScalar` / `writeArr` never enter the
seam. The entry conjunct `σ.out = []` is `initEnv`'s, for free. -/

section Output

open Classical in
theorem out_shape {n : ℕ} {G : SimpleGraph (Fin n)} {φ : Lax3.FirstOrder.FO 0} (σ' : Env)
    (x : List ℕ) :
    σ'.out = [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0] ↔
      σ'.out = (fun _ : List ℕ => if Lax3.FirstOrder.Sat G Fin.elim0 φ then [1] else [0]) x := by
  by_cases h : Lax3.FirstOrder.Sat G Fin.elim0 φ <;> simp [h]

theorem out_initEnv {ext : String → ℕ} {x : List ℕ} : (initEnv ext x).out = [] := rfl

end Output

/-! ## 7. The axiom check -/

#print axioms driverRoot_decides_sentence_pre
#print axioms not_rootPre_initEnv
#print axioms rootPre_initEnv_iff_ns_zero
#print axioms read_breaks_inp
#print axioms lwCom_spec
#print axioms decodeImplementsD_initEnv_edgeless
#print axioms no_word_size_for_sparse

end Lax3Proofs.Refine.BridgeSeamProbe
