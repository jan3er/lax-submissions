import Mathlib.Data.Nat.Log
import Lax13Proofs.Refine.NREST.Automation
import Lax13Proofs.Refine.NREST.FlattenCurrencies

/-!
The currency-vector budget spine of the pinned introsort example.

Source-derived material comes from `isabelle_llvm_time` at
`42dd7f59998d76047bb4b6bce76d8f67b53a08b6`:

* `Sorting_Quicksort_Scheme.thy` supplies `introsort_aux_cost`, the
  first-phase account used by `partitionBudget`, and the abstract
  `introsort3` composition;
* `Sorting_Quicksort_Partition.thy` makes the `partition_c` phase
  concrete (Hoare partition plus median selection);
* `Sorting_Final_insertion_Sort.thy` supplies the linear finishing phase;
* `Sorting_Introsort.thy` supplies the depth `2 * log n`, the heap
  fallback, the final operation upper bound `introsort_cost3`, and its
  exact all-currencies projection.

The Lean glue is deliberately smaller than a sorting correctness port.
`IntrosortAccount` records the source's visible budget components and the
parameters determining the named operation upper bound; `introsortSpine`
witnesses one coherent stage's consumption in NREST.  No declaration below
claims functional correctness of an introsort implementation.

The source's final vector still contains LLVM-level currencies absent
from this repository's small verified IR (`load`, `store`, `ofs_ptr`,
and comparisons).  Therefore it would be false accounting to use the
local code-generator's `cashExchangeRate`, which prices those names at
zero.  `sourceCashRate` is instead the source's `project_all` boundary:
every currency in the displayed vector costs one Unit coin.  The only
scalar theorem exchanges through that finite rate and then uses P3.A's
`flatCurrs`/`flatCost` boundary.
-/

namespace Lax13Proofs.Refine.IntrosortBudget

open Lax13Proofs.Refine
open Lax13Proofs.Refine.NRest

/-! ## Source-shaped constructors and phase accounts -/

/-- Build one phase account from named operation/currency balances. -/
def phaseCost (entries : List (String × ℕ)) : ECost :=
  entries.foldr (fun e c => ACost.cost e.1 (e.2 : ℕ∞) + c) 0

/-- Isabelle's `Discrete.log`, represented by the same floor logarithm
at base two. -/
def ilog (n : ℕ) : ℕ := Nat.log 2 n

/-- One recursive-node charge in `introsort_aux_cost`. -/
def controlUnit : ECost := phaseCost
  [("if", 2), ("eq", 1), ("lt", 1), ("call", 1),
   ("list_length", 1), ("sub", 1), ("list_append", 1)]

/-- Exact port of `introsort_aux_cost μ (n,d)` from
`Sorting_Quicksort_Scheme.thy`: recursive control, `d*n` partition work,
and the depth-zero `sort_c` fallback. -/
def partitionBudget (μ : ℕ → ℕ) (n d : ℕ) : ECost :=
  ((d + 1) * n) • controlUnit +
    phaseCost [("sort_c", μ n), ("partition_c", d * n)]

/-- The visibly separated components of the source budget spine.
`operationVector` is their source-derived final upper-bound formula in
`Sorting_Introsort.introsort_cost3`; the other fields retain the
algorithm-specific currencies used before that exchange. -/
structure IntrosortAccount where
  ltCurr : String
  size : ℕ
  control : ECost
  partitionWork : ECost
  heapFallback : ECost
  phaseDispatch : ECost
  firstPhaseToken : ECost
  insertionFinish : ECost

/-- Exact `introsort_aux_cost`: recursive control, partition work, and
the heap fallback at depth zero. -/
def IntrosortAccount.recursiveAccount (b : IntrosortAccount) : ECost :=
  b.control + b.partitionWork + b.heapFallback

/-- Exact `introsort3_cost`: dispatch, the still-abstract first-phase
token, and the final insertion-sort token. -/
def IntrosortAccount.topLevelAccount (b : IntrosortAccount) : ECost :=
  b.phaseDispatch + b.firstPhaseToken + b.insertionFinish

/-- The coherent account after the source TId exchange replaces
`slice_part_sorted` by `introsort_aux_cost`. -/
def IntrosortAccount.expandedAccount (b : IntrosortAccount) : ECost :=
  b.phaseDispatch + b.recursiveAccount + b.insertionFinish

/-! ## The exact final operation upper-bound vector -/

/-- The exact formula named `introsort_cost3`, with the locale-parametric
comparison currency kept explicit.  Upstream obtains this as an upper
bound on the synthesized exchange row, not as an equality to that row. -/
def operationBudget (ltCurr : String) (n : ℕ) : ECost :=
  let l := ilog n
  let nl := n * l
  phaseCost
    [("mul", 1 + nl * 14),
     ("ofs_ptr", 1241 + 108 * nl + 68 * n),
     ("add", 48 * nl + 21 + n + l),
     ("store", 612 + 34 * n + 54 * nl),
     ("sub", 35 * n + 596 + 44 * nl),
     ("load", 629 + 34 * n + 54 * nl),
     ("if", 40 * nl + 633 + l + 20 * n),
     (ltCurr, 306 + 17 * n + 20 * nl),
     ("and", nl * 6),
     ("icmp_slt", 20 + 2 * n + 25 * nl + l),
     ("udiv", 1 + 18 * nl + l),
     ("call", 343 + 22 * nl + 19 * n + l),
     ("icmp_eq", 289 + n + l * 2 * n),
     ("icmp_sle", 1)]

/-- The final vector is derived from the source parameters stored in the
account, rather than being an unconstrained record field. -/
def IntrosortAccount.operationVector (b : IntrosortAccount) : ECost :=
  operationBudget b.ltCurr b.size

/-- The complete, visibly multi-stage introsort budget.  Its fields retain
both the exact `introsort3_cost` tokens and the exact `introsort_aux_cost`
replacement at depth `2*log n`; the operation upper-bound vector is
derived separately from `ltCurr` and `size`. -/
def introsortBudget (ltCurr : String) (n : ℕ) : IntrosortAccount :=
  let l := ilog n
  let d := 2 * l
  let μ := fun m => m * ilog m
  { ltCurr := ltCurr
    size := n
    control := ((d + 1) * n) • controlUnit
    partitionWork := phaseCost [("partition_c", d * n)]
    heapFallback := phaseCost [("sort_c", μ n)]
    phaseDispatch := phaseCost [("sub", 1), ("lt", 1), ("if", 1)]
    firstPhaseToken := phaseCost [("slice_part_sorted", 1)]
    insertionFinish := phaseCost [("slice_sort", 1)]
  }

theorem partitionBudget_eq_introsort_fields (ltCurr : String) (n : ℕ) :
    partitionBudget (fun m => m * ilog m) n (2 * ilog n) =
      (introsortBudget ltCurr n).recursiveAccount := by
  simp [partitionBudget, introsortBudget, IntrosortAccount.recursiveAccount, phaseCost]
  ac_rfl

/-- Exact canonical upper-bound vector before any scalar projection. -/
theorem introsortBudget_normal (ltCurr : String) (n : ℕ) :
    (introsortBudget ltCurr n).operationVector =
      let l := ilog n
      let nl := n * l
      ACost.cost "mul" ((1 + nl * 14 : ℕ) : ℕ∞) +
      ACost.cost "ofs_ptr" ((1241 + 108 * nl + 68 * n : ℕ) : ℕ∞) +
      ACost.cost "add" ((48 * nl + 21 + n + l : ℕ) : ℕ∞) +
      ACost.cost "store" ((612 + 34 * n + 54 * nl : ℕ) : ℕ∞) +
      ACost.cost "sub" ((35 * n + 596 + 44 * nl : ℕ) : ℕ∞) +
      ACost.cost "load" ((629 + 34 * n + 54 * nl : ℕ) : ℕ∞) +
      ACost.cost "if" ((40 * nl + 633 + l + 20 * n : ℕ) : ℕ∞) +
      ACost.cost ltCurr ((306 + 17 * n + 20 * nl : ℕ) : ℕ∞) +
      ACost.cost "and" ((nl * 6 : ℕ) : ℕ∞) +
      ACost.cost "icmp_slt" ((20 + 2 * n + 25 * nl + l : ℕ) : ℕ∞) +
      ACost.cost "udiv" ((1 + 18 * nl + l : ℕ) : ℕ∞) +
      ACost.cost "call" ((343 + 22 * nl + 19 * n + l : ℕ) : ℕ∞) +
      ACost.cost "icmp_eq" ((289 + n + l * 2 * n : ℕ) : ℕ∞) +
      ACost.cost "icmp_sle" (1 : ℕ∞) := by
  apply le_antisymm
  · simp only [introsortBudget, IntrosortAccount.operationVector, operationBudget,
      phaseCost, List.foldr, add_zero, norm_cost]
    sc_solve
    simp
  · simp only [introsortBudget, IntrosortAccount.operationVector, operationBudget,
      phaseCost, List.foldr, add_zero, norm_cost]
    sc_solve
    simp

/-! ## A source-shaped NREST consumer -/

/-- Consume the coherent top-level `introsort3_cost` stage: dispatch,
the abstract first-phase token, then insertion sort. -/
noncomputable def introsortSpine (ltCurr : String) (n : ℕ) : NRest Unit ECost :=
  let b := introsortBudget ltCurr n
  consume (consume (consume (returnT ()) b.phaseDispatch)
    b.firstPhaseToken) b.insertionFinish

/-- The multi-phase computation consumes exactly the top-level account;
this is a budget theorem, not sorting functional correctness. -/
theorem introsortSpine_consumes (ltCurr : String) (n : ℕ) :
    introsortSpine ltCurr n =
      consume (returnT ()) (introsortBudget ltCurr n).topLevelAccount := by
  simp [introsortSpine, IntrosortAccount.topLevelAccount, consume_consume,
    add_comm, add_left_comm]

/-! ## Refute-before-prove gates -/

/-- Boundary evaluation of the source recurrence. -/
theorem partition_boundary_gate :
    (partitionBudget (fun m => m) 0 0).toFun "sort_c" = 0 := by
  simp [partitionBudget, controlUnit, phaseCost]

/-- Nontrivial evaluation: `n=8`, `d=6`, and `μ(n)=n*log₂ n`. -/
theorem partition_nontrivial_gate :
    (partitionBudget (fun m => m * ilog m) 8 6).toFun "partition_c" = 48 ∧
    (partitionBudget (fun m => m * ilog m) 8 6).toFun "sort_c" = 24 ∧
    (partitionBudget (fun m => m * ilog m) 8 6).toFun "if" = 112 := by
  decide

/-- Negative control: deleting the real heap-fallback phase strictly
underprices `sort_c` on a nontrivial source input. -/
theorem heapFallback_negative_gate :
    ((((6 + 1) * 8) • controlUnit + phaseCost [("partition_c", 6 * 8)] : ECost).toFun
      "sort_c") <
    (partitionBudget (fun m => m * ilog m) 8 6).toFun "sort_c" := by
  decide

/-- Positive control: the final account still has an operation coordinate
before cash. -/
theorem vector_before_cash_positive_gate :
    ((introsortBudget "cmp" 8).operationVector).toFun "mul" = 337 := by
  decide

/-- The source's first-phase result token is retained in the top-level
account, rather than silently absorbed into the finishing charge. -/
theorem slicePartSorted_positive_gate :
    ((introsortBudget "cmp" 8).firstPhaseToken).toFun "slice_part_sorted" = 1 := by
  decide

/-- The expanded stage has replaced, rather than retained, the abstract
first-phase token. -/
theorem expanded_replaces_token_gate :
    ((introsortBudget "cmp" 8).expandedAccount).toFun "slice_part_sorted" = 0 := by
  decide

/-! ## Source-shaped stage exchanges -/

/-- The source's `TId` update: every currency is preserved at unit rate,
except `slice_part_sorted`, which is replaced by `introsort_aux_cost`. -/
def recursiveUpdateRate (b : IntrosortAccount) (k : String) : ECost :=
  Function.update (TId : String → ECost) "slice_part_sorted" b.recursiveAccount k

/-- The source-shaped update replaces the first-phase token; it does not
retain the token and add recursive work beside it. -/
theorem topLevel_to_expanded (ltCurr : String) (n : ℕ) :
    timerefineA (recursiveUpdateRate (introsortBudget ltCurr n))
        (introsortBudget ltCurr n).topLevelAccount =
      (introsortBudget ltCurr n).expandedAccount := by
  let b := introsortBudget ltCurr n
  change timerefineA (recursiveUpdateRate b)
      (b.phaseDispatch + b.firstPhaseToken + b.insertionFinish) =
    b.phaseDispatch + b.recursiveAccount + b.insertionFinish
  have hR : wfR'' (recursiveUpdateRate (introsortBudget ltCurr n)) := by
    exact wfR''.update (by simp) "slice_part_sorted" _
  change wfR'' (recursiveUpdateRate b) at hR
  have hdispatch : timerefineA (recursiveUpdateRate b) b.phaseDispatch =
      b.phaseDispatch := by
    change timerefineA (recursiveUpdateRate b)
        (phaseCost [("sub", 1), ("lt", 1), ("if", 1)]) =
      phaseCost [("sub", 1), ("lt", 1), ("if", 1)]
    simp [phaseCost, NRest.timerefineA_add hR, recursiveUpdateRate,
      NRest.TId_apply]
  rw [NRest.timerefineA_add hR, NRest.timerefineA_add hR]
  rw [hdispatch]
  simp [b, IntrosortAccount.recursiveAccount, recursiveUpdateRate,
    introsortBudget, phaseCost, norm_cost]

/-! ## The source's outer token and collapsed operation upper bound -/

/-- `slice_sort_spec` charges this single algorithm-level token. -/
def topLevelToken : ECost := phaseCost [("slice_sort", 1)]

/-- A finite collapsed rate exposing exact `introsort3_cost`.  It packages
the source-visible top-level stage without claiming to be one of the
upstream synthesized exchange matrices. -/
def abstractPhaseRate (b : IntrosortAccount) (k : String) : ECost :=
  if k = "slice_sort" then b.topLevelAccount else 0

/-- The collapsed upper-bound rate maps the outer token directly to
`introsort_cost3`.  It deliberately does not claim to reify the source's
intermediate `introsort5_TR` matrices. -/
def operationUpperRate (ltCurr : String) (n : ℕ) (k : String) : ECost :=
  if k = "slice_sort" then operationBudget ltCurr n else 0

theorem abstractPhaseRate_wf (b : IntrosortAccount) : wfR'' (abstractPhaseRate b) := by
  intro k
  exact Set.finite_singleton "slice_sort" |>.subset (by
    intro s hs
    by_contra hne
    have hne' : s ≠ "slice_sort" := by simpa using hne
    apply hs
    simp [abstractPhaseRate, hne'])

theorem operationUpperRate_wf (ltCurr : String) (n : ℕ) :
    wfR'' (operationUpperRate ltCurr n) := by
  intro k
  exact Set.finite_singleton "slice_sort" |>.subset (by
    intro s hs
    by_contra hne
    have hne' : s ≠ "slice_sort" := by simpa using hne
    apply hs
    simp [operationUpperRate, hne'])

/-- The collapsed phase rate maps the outer token to exact
`introsort3_cost`. -/
theorem topLevel_to_abstract (ltCurr : String) (n : ℕ) :
    timerefineA (abstractPhaseRate (introsortBudget ltCurr n)) topLevelToken =
      (introsortBudget ltCurr n).topLevelAccount := by
  simp [topLevelToken, phaseCost, abstractPhaseRate, norm_cost]

/-- Formal connection between the source top-level currency and its
canonical final upper bound.  This is the collapsed representation of
the source theorem that names `introsort_cost3`, not equality to
`introsort5_TR`. -/
theorem topLevel_to_operationUpper (ltCurr : String) (n : ℕ) :
    timerefineA (operationUpperRate ltCurr n) topLevelToken =
      (introsortBudget ltCurr n).operationVector := by
  simp [topLevelToken, phaseCost, operationUpperRate, introsortBudget,
    IntrosortAccount.operationVector, norm_cost]

/-- Compiled boundary refutation: the local verified IR has no source
`load` operation, so its code-generation cash map assigns this real
source currency price zero. -/
theorem localIRCash_drops_source_load_gate :
    flatCost (timerefineA cashExchangeRate (phaseCost [("load", 1)])) = 0 := by
  rw [flatCost_timerefineA_cashExchangeRate]
  simp [phaseCost, Lax13Proofs.Refine.Codegen.ecash,
    Lax13Proofs.Refine.Ir.Currency.all,
    Lax13Proofs.Refine.Ir.Currency.skip, Lax13Proofs.Refine.Ir.Currency.const,
    Lax13Proofs.Refine.Ir.Currency.copy, Lax13Proofs.Refine.Ir.Currency.aget,
    Lax13Proofs.Refine.Ir.Currency.aset, Lax13Proofs.Refine.Ir.Currency.ite,
    Lax13Proofs.Refine.Ir.Currency.«while», Lax13Proofs.Refine.Ir.Currency.add,
    Lax13Proofs.Refine.Ir.Currency.sub, Lax13Proofs.Refine.Ir.Currency.mul,
    Lax13Proofs.Refine.Ir.Currency.div, Lax13Proofs.Refine.Ir.Currency.and,
    Lax13Proofs.Refine.Ir.Currency.or, Lax13Proofs.Refine.Ir.Currency.xor,
    Lax13Proofs.Refine.Ir.Currency.shiftl, Lax13Proofs.Refine.Ir.Currency.shiftr]

/-! ## Source `project_all`: exchange once, then flatten -/

/-- Exact support of the final displayed source vector. -/
def sourceCurrencies (ltCurr : String) : List String :=
  ["mul", "ofs_ptr", "add", "store", "sub", "load", "if", ltCurr,
   "and", "icmp_slt", "udiv", "call", "icmp_eq", "icmp_sle"]

/-- The source's unit projection: each displayed operation costs one
Unit coin, and every other currency costs zero. -/
def sourceCashRate (ltCurr k : String) : ACost Unit ℕ∞ :=
  if k ∈ sourceCurrencies ltCurr then ACost.cost () 1 else 0

theorem sourceCashRate_wf (ltCurr : String) : wfR'' (sourceCashRate ltCurr) := by
  intro u
  cases u
  exact (sourceCurrencies ltCurr).toFinset.finite_toSet.subset (by
    intro k hk
    simp only [Finset.mem_coe, List.mem_toFinset]
    by_contra hmem
    apply hk
    simp [sourceCashRate, hmem])

variable {α : Type}

/-- The source-specific exchange and P3.A's structural Unit flattening. -/
noncomputable def sourceCollapse (ltCurr : String) (m : NRest α ECost) : NRest α ℕ∞ :=
  flatCurrs (timerefine (sourceCashRate ltCurr) m)

theorem flatCost_sourceCashRate_cost (ltCurr k : String) (x : ℕ∞)
    (hk : k ∈ sourceCurrencies ltCurr) :
    flatCost (timerefineA (sourceCashRate ltCurr) (ACost.cost k x)) = x := by
  rw [NRest.timerefineA_cost]
  simp [flatCost, sourceCashRate, hk]

/-- The single scalar boundary.  It reproduces the pinned source theorem
`introsort3_allcost_simplified` and does not invoke the local IR price map. -/
theorem introsortBudget_cash (ltCurr : String) (n : ℕ) :
    sourceCollapse ltCurr
        (spec (fun _ : Unit => True)
          (fun _ => (introsortBudget ltCurr n).operationVector)) =
      spec (fun _ : Unit => True) (fun _ =>
        ((4693 + 5 * ilog n + 231 * n + 455 * (n * ilog n) : ℕ) : ℕ∞)) := by
  rw [sourceCollapse, timerefine_spec, flatCurrs_spec]
  congr 1
  funext u
  rw [introsortBudget_normal]
  simp only [NRest.timerefineA_add (sourceCashRate_wf ltCurr), flatCost_add]
  rw [flatCost_sourceCashRate_cost ltCurr "mul" _ (by simp [sourceCurrencies])]
  rw [flatCost_sourceCashRate_cost ltCurr "ofs_ptr" _ (by simp [sourceCurrencies])]
  rw [flatCost_sourceCashRate_cost ltCurr "add" _ (by simp [sourceCurrencies])]
  rw [flatCost_sourceCashRate_cost ltCurr "store" _ (by simp [sourceCurrencies])]
  rw [flatCost_sourceCashRate_cost ltCurr "sub" _ (by simp [sourceCurrencies])]
  rw [flatCost_sourceCashRate_cost ltCurr "load" _ (by simp [sourceCurrencies])]
  rw [flatCost_sourceCashRate_cost ltCurr "if" _ (by simp [sourceCurrencies])]
  rw [flatCost_sourceCashRate_cost ltCurr ltCurr _ (by simp [sourceCurrencies])]
  rw [flatCost_sourceCashRate_cost ltCurr "and" _ (by simp [sourceCurrencies])]
  rw [flatCost_sourceCashRate_cost ltCurr "icmp_slt" _ (by simp [sourceCurrencies])]
  rw [flatCost_sourceCashRate_cost ltCurr "udiv" _ (by simp [sourceCurrencies])]
  rw [flatCost_sourceCashRate_cost ltCurr "call" _ (by simp [sourceCurrencies])]
  rw [flatCost_sourceCashRate_cost ltCurr "icmp_eq" _ (by simp [sourceCurrencies])]
  rw [flatCost_sourceCashRate_cost ltCurr "icmp_sle" _ (by simp [sourceCurrencies])]
  push_cast
  ring

/-! ## Axiom gates -/

/-- info: 'Lax13Proofs.Refine.IntrosortBudget.topLevel_to_expanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms topLevel_to_expanded

/-- info: 'Lax13Proofs.Refine.IntrosortBudget.introsortBudget_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms introsortBudget_normal

/-- info: 'Lax13Proofs.Refine.IntrosortBudget.introsortSpine_consumes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms introsortSpine_consumes

/-- info: 'Lax13Proofs.Refine.IntrosortBudget.introsortBudget_cash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms introsortBudget_cash

end Lax13Proofs.Refine.IntrosortBudget
