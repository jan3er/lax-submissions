import Lax11Proofs.TreeFoldRun
import Lax13Proofs.Transfer

/-!
The tree fold, end to end.

The phases are proved; what is left is to run them in a row, hand each
one the frame conditions of the ones before, and cash the result in at
the machine. The result is the schema's theorem: for every table there
is a machine program that reads a parent-pointer tree and writes the
fold of that table over it, in time linear in the length of the word, at
every word length that admits the word and the table.

Three things about the constants deserve saying out loud, because the
schema will be instantiated with a table nobody wants to look at.

*The table is paid for once, and it is a constant.* Materializing it
costs three units per entry, so `3 * (L + V + V²)` before the tree is
even seeded. That is not linear in the input — it does not depend on
the input at all — and it is legitimate exactly because of the order of
the quantifiers: the table comes first, the program is generated from
it, and only then is the tree given. A bound of the form
`c * (|x| + 1)` with `c` chosen after the table is what the statement
asks for, and `c` is allowed to be as monstrous as the table is.

*The per-node cost is a constant number of array operations*, and it is
the same constant whatever the table says: seeding is two reads and a
store, pushing is a parent read, two accumulator reads, two table reads
and a store. Nothing in the loops scales with `V` or `L`. This is the
property the eventual instantiation needs — the type table may have a
tower of types in it, and the fold over the decomposition still takes
`O(N)` steps with the tower living entirely in the constant.

*The word length, though, does see the table.* A label indexes the seed
array and a cell of the square table is indexed by two values at once,
so `L` and `V²` are numbers the machine holds; a machine whose words
cannot number the table's entries cannot run the table. That is what
`Table.Fits` says, and the same constant that pays for materializing the
table pays for holding its indices, so the statement carries one
constant and not two.
-/

namespace Lax11Proofs.TreeFold

open Lax13.Ram Lax13.RamComputes Lax13Proofs.Imp Lax13Proofs.Compile
open Lax13Proofs.Reasoning Lax13Proofs.Transfer
open Lax11Proofs.CC (readLoop readLoop_run)

/-! ### The extents

The three arrays holding the tree have one entry per node; the three
holding the table have one entry per table entry. As always the extents
are chosen per input (D17): they are not represented in the compiled
program, and exist only to say which accesses are in range. -/

/-- The array extents the schema runs with. -/
def foldExt (T : Table) (N : ℕ) (a : String) : ℕ :=
  if a = "ini" then T.L else if a = "row" then T.V else if a = "tab" then T.V * T.V else N

/-- What the table costs: three units per entry of the three arrays,
plus the schema's fixed overhead. It is a constant of the table, paid
before the input is looked at. -/
def tableCost (T : Table) : ℕ := 3 * (T.L + T.V + T.V * T.V) + 35

/-- How wide the table alone asks the word to be: one number per label,
and one per cell of the square combination table. -/
def tableWidth (T : Table) : ℕ := T.L + T.V * T.V

/-- Materializing the table costs at least three units per number the
table makes the machine hold; both count the table's entries. -/
theorem tableWidth_le_tableCost (T : Table) : 3 * tableWidth T + 35 ≤ tableCost T := by
  simp only [tableWidth, tableCost]
  omega

/-- The bound the schema runs under on the word `x`: the length of the
word, its largest entry, and the size of the table. -/
def foldBound (T : Table) (x : List ℕ) : ℕ := x.length + maxEntry x + tableWidth T + 1

theorem table_fits_foldBound (T : Table) (x : List ℕ) : T.Fits (foldBound T x) :=
  ⟨by simp only [foldBound, tableWidth]; omega, by simp only [foldBound, tableWidth]; omega⟩

/-- The whole run of the schema on an encoded tree: the root's value
comes out, and the cost is linear in the length of the word plus the
table's own materialization. Every phase was bounded loosely and this
is the sum of those bounds. -/
theorem foldCom_run {B : ℕ} {T : Table} (hT : T.Wf) (hTB : T.Fits B) {x : List ℕ} {N : ℕ}
    {par lab : ℕ → ℕ} (hx : EncodesTree x N par lab T.L)
    (hxB : ∀ v ∈ x, v < B) (hlenB : x.length < B) :
    ∃ (σ' : Env) (K : ℕ), Run B (foldCom T) (initEnv (foldExt T N) x) σ' K ∧
      σ'.out = [val T par lab (N - 1)] ∧ K ≤ 60 * (x.length + 1) + tableCost T := by
  obtain ⟨hN1, hxeq, hpar, hlab⟩ := hx
  have hlen : x.length = 1 + N + N := by rw [hxeq]; simp; omega
  have hparN : ∀ i, i + 1 < N → par i < N := fun i hi => (hpar i hi).2
  have hNB : N < B := by omega
  have hVB := hTB.value_le
  have hLB := hTB.label_le
  have hsqB := hTB.square_le
  have hparB : ∀ v ∈ arrOf N par, v < B := fun v hv =>
    hxB v (by rw [hxeq]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hv))
  have hlabB : ∀ v ∈ arrOf N lab, v < B := fun v hv =>
    hxB v (by rw [hxeq]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hv))
  -- the header
  set σ₀ : Env := initEnv (foldExt T N) x with hσ₀
  have hσ₀arr : ∀ a, σ₀.arrs a = List.replicate (foldExt T N a) 0 := fun a => by rw [hσ₀]; rfl
  set σ₁ : Env := { σ₀.setVar "N" N with inp := arrOf N par ++ arrOf N lab } with hσ₁
  have r₁ : Run B (.read "N") σ₀ σ₁ 1 := Run.read (by rw [hσ₀]; simpa [initEnv] using hxeq)
  have hσ₁arr : ∀ a, σ₁.arrs a = List.replicate (foldExt T N a) 0 := fun a => by
    rw [hσ₁]; simpa using hσ₀arr a
  -- the parents
  obtain ⟨σ₂, p₂, r₂, hpar₂, hp₂, hinp₂⟩ :=
    readLoop_run (B := B) (a := "par") (lim := "N") (by decide) (by decide) (σ := σ₁)
      (g := fun _ => 0) (k := N) (ys := arrOf N par) (rest := arrOf N lab)
      (by rw [hσ₁arr "par"]; simp [foldExt, replicate_eq_arrOf])
      (by simp [hσ₁]) (by simp) (by simp [hσ₁]) hNB hparB
  have hpararr₂ : σ₂.arrs "par" = arrOf N par := by
    rw [hpar₂]; exact arrOf_congr fun i hi => by rw [hp₂ i hi, getD_arrOf _ hi]
  -- the labels
  obtain ⟨σ₃, l₃, r₃, hlab₃, hl₃, hinp₃⟩ :=
    readLoop_run (B := B) (a := "lab") (lim := "N") (by decide) (by decide) (σ := σ₂)
      (g := fun _ => 0) (k := N) (ys := arrOf N lab) (rest := [])
      (by rw [r₂.frame_arr "lab" (by decide), hσ₁arr "lab"]; simp [foldExt, replicate_eq_arrOf])
      (by rw [r₂.frame_var "N" (by decide), hσ₁]; simp) (by simp) (by simp [hinp₂])
      hNB hlabB
  have hlabarr₃ : σ₃.arrs "lab" = arrOf N lab := by
    rw [hlab₃]; exact arrOf_congr fun i hi => by rw [hl₃ i hi, getD_arrOf _ hi]
  have hN₃ : σ₃.vars "N" = N := by
    rw [r₃.frame_var "N" (by decide), r₂.frame_var "N" (by decide), hσ₁]; simp
  -- the table, materialized: seeds, row bases, combinations
  obtain ⟨σ₄, r₄, hini₄, harr₄, hvar₄, hinp₄, hout₄⟩ :=
    stores_arrOf_run (B := B) (a := "ini") (n := T.L) (σ := σ₃) (f := fun _ => 0) (h := T.init)
      (by rw [r₃.frame_arr "ini" (by decide), r₂.frame_arr "ini" (by decide), hσ₁arr "ini"]
          simp [foldExt, replicate_eq_arrOf])
      hLB (fun l hl => lt_of_lt_of_le (hT.init_lt l hl) hVB)
  obtain ⟨σ₅, r₅, hrow₅, harr₅, hvar₅, hinp₅, hout₅⟩ :=
    stores_arrOf_run (B := B) (a := "row") (n := T.V) (σ := σ₄) (f := fun _ => 0)
      (h := fun a => a * T.V)
      (by rw [harr₄ "row" (by decide), r₃.frame_arr "row" (by decide), r₂.frame_arr "row" (by decide),
              hσ₁arr "row"]
          simp [foldExt, replicate_eq_arrOf])
      hVB (fun a ha => by
        show a * T.V < B
        have hstep : (a + 1) * T.V ≤ T.V * T.V := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at hstep
        omega)
  obtain ⟨σ₆, r₆, htab₆, harr₆, hvar₆, hinp₆, hout₆⟩ :=
    stores_arrOf_run (B := B) (a := "tab") (n := T.V * T.V) (σ := σ₅) (f := fun _ => 0)
      (h := fun k => T.step (k / T.V) (k % T.V))
      (by rw [harr₅ "tab" (by decide), harr₄ "tab" (by decide), r₃.frame_arr "tab" (by decide),
              r₂.frame_arr "tab" (by decide), hσ₁arr "tab"]
          simp [foldExt, replicate_eq_arrOf])
      hsqB (fun j hj => by
        have hV : 0 < T.V := by
          rcases Nat.eq_zero_or_pos T.V with h0 | h0
          · rw [h0] at hj; simp at hj
          · exact h0
        exact lt_of_lt_of_le
          (hT.step_lt _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)) _
            (Nat.mod_lt _ hV)) hVB)
  -- what the seeding phase starts from
  have hacc₆ : σ₆.arrs "acc" = arrOf N (fun _ => 0) := by
    rw [harr₆ "acc" (by decide), harr₅ "acc" (by decide), harr₄ "acc" (by decide),
      r₃.frame_arr "acc" (by decide), r₂.frame_arr "acc" (by decide), hσ₁arr "acc"]
    simp [foldExt, replicate_eq_arrOf]
  have hlabarr₆ : σ₆.arrs "lab" = arrOf N lab := by
    rw [harr₆ "lab" (by decide), harr₅ "lab" (by decide), harr₄ "lab" (by decide), hlabarr₃]
  have hpararr₆ : σ₆.arrs "par" = arrOf N par := by
    rw [harr₆ "par" (by decide), harr₅ "par" (by decide), harr₄ "par" (by decide),
      r₃.frame_arr "par" (by decide), hpararr₂]
  have hini₆ : σ₆.arrs "ini" = arrOf T.L T.init := by
    rw [harr₆ "ini" (by decide), harr₅ "ini" (by decide), hini₄]
  have hrow₆ : σ₆.arrs "row" = arrOf T.V (fun a => a * T.V) := by
    rw [harr₆ "row" (by decide), hrow₅]
  have hN₆ : σ₆.vars "N" = N := by rw [hvar₆, hvar₅, hvar₄, hN₃]
  have hout₆' : σ₆.out = [] := by
    rw [hout₆, hout₅, hout₄, r₃.out_eq (by decide), r₂.out_eq (by decide), hσ₁]; simp [hσ₀, initEnv]
  -- the seeds
  obtain ⟨σ₇, r₇, hacc₇, harr₇, hinp₇, hout₇, hvar₇⟩ :=
    seedLoop_run (B := B) (T := T) hT hTB (lab := lab) (N := N) (σ := σ₆) (f := fun _ => 0)
      hacc₆ hlabarr₆ hini₆ hN₆ hlab hNB
  -- the sweep
  obtain ⟨σ₈, r₈, hacc₈, harr₈, hinp₈, hout₈, hvar₈⟩ :=
    pushLoop_run (B := B) (T := T) hT hTB (par := par) (lab := lab) (N := N) (σ := σ₇) hacc₇
      (by rw [harr₇ "par" (by decide), hpararr₆])
      (by rw [harr₇ "row" (by decide), hrow₆])
      (by rw [harr₇ "tab" (by decide), htab₆])
      (by rw [hvar₇ "N" (by decide), hN₆]) hN1 hpar hlab hNB
  -- the root's value, written out
  have hN₈ : σ₈.vars "N" = N := by
    rw [hvar₈ "N" (by decide) (by decide), hvar₇ "N" (by decide), hN₆]
  have hrootlt : val T par lab (N - 1) < T.V := by
    rw [← sweep_eq_val T par lab (j := N - 1) (fun c hc => (hpar c (by omega)).1) (le_refl _)]
    exact sweep_lt hT hlab hparN _ (by omega) _ (by omega)
  have hidxeval : (Expr.sub (.var "N") (.lit 1)).evalB B σ₈ = some (N - 1) := by
    have h := evalB_bin (op := .sub) (evalB_var (show σ₈.vars "N" < B by rw [hN₈]; omega))
      (evalB_lit (show (1 : ℕ) < B by omega)) (by simp [hN₈]; omega)
    simpa [hN₈] using h
  have heval : (Expr.get "acc" (.sub (.var "N") (.lit 1))).evalB B σ₈ =
      some (val T par lab (N - 1)) :=
    evalB_get hidxeval (by rw [hacc₈]; exact getElem?_arrOf _ (show N - 1 < N by omega))
      (lt_of_lt_of_le hrootlt hVB)
  have r₉ : Run B (.write (.get "acc" (.sub (.var "N") (.lit 1)))) σ₈
      { σ₈ with out := σ₈.out ++ [val T par lab (N - 1)] } 5 :=
    (Run.write heval).mono (by simp)
  -- the phases in a row
  refine ⟨_, _, Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄ (Run.seq r₅
    (Run.seq r₆ (Run.seq r₇ (Run.seq r₈ r₉))))))), ?_, ?_⟩
  · rw [show σ₈.out = [] by rw [hout₈, hout₇, hout₆']]; simp
  · rw [tableCost]; omega

/-! ### The schema, at the machine

The layout has six arrays, so an index computation is eight
instructions and the machine pays thirty-seven steps per unit of IMP+
cost. -/

/-- The machine pays thirty-seven steps per unit of IMP+ cost. -/
theorem const_eq : layout.const = 37 := by
  simp [Layout.const, Layout.idxLen, layout]

/-- What the pipeline asks of the schema: on every encoded tree it
computes the root's value, at sixty units per entry of the word plus the
table's fixed price, with every value it produces below the length of
the word, its largest entry and the size of the table. -/
theorem foldCom_solves {T : Table} (hT : T.Wf) (N : ℕ) (par lab : ℕ → ℕ) (w : ℕ) :
    Solves layout (foldCom T)
      {x | EncodesTree x N par lab T.L ∧
        ∀ v ∈ x, 37 * (60 + tableCost T) * (x.length + v + 1) ≤ 2 ^ w}
      (fun _ => [val T par lab (N - 1)]) (foldBound T)
      (fun x => 60 * (x.length + 1) + tableCost T) where
  ok := foldCom_ok T
  inp := fun x _ v hv => by
    have := le_maxEntry hv
    simp only [foldBound]
    omega
  run := by
    rintro x ⟨hx, -⟩
    have hlen : x.length = 1 + N + N := by rw [hx.2.1]; simp; omega
    obtain ⟨σ', K, hrun, hout, hK⟩ :=
      foldCom_run (B := foldBound T x) hT (table_fits_foldBound T x) hx
        (fun v hv => by have := le_maxEntry hv; simp only [foldBound]; omega)
        (by simp only [foldBound]; omega)
    exact ⟨foldExt T N, σ', hrun.mono hK, hout⟩

/-- **The tree-fold schema.** For every well-formed table there is a
machine program that computes the table's fold over any parent-pointer
tree given in the schema's encoding, in time linear in the length of the
word, at every word length at which that constant multiple of the length
and of each entry of the word fits.

The constant depends on the table and the program is generated from it:
this is the non-uniformity the eventual instantiation needs, and it is
the reason the table may be as large — and as noncomputable — as the
mathematics that produces it. The word length hypothesis quantifies over
the entries of the word because the encoding does not bound them all:
the root's own parent entry is never read and never constrained, and the
machine still has to hold it. -/
theorem exists_linearTime_program_treeFold {T : Table} (hT : T.Wf) :
    ∃ (p : Program) (c : ℕ), ∀ (N : ℕ) (par lab : ℕ → ℕ) (w : ℕ),
      ComputesInTime w p
        {x | EncodesTree x N par lab T.L ∧ ∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w}
        (fun _ => [val T par lab (N - 1)]) (fun x => c * (x.length + 1)) := by
  refine ⟨foldProgram T, 37 * (60 + tableCost T), fun N par lab w =>
    computesInTime_of_solves (foldCom_solves hT N par lab w) ?_ ?_⟩
  · rintro x ⟨hx, hw⟩
    set c := 37 * (60 + tableCost T) with hc
    have hne : x ≠ [] := by rw [hx.2.1]; simp
    have hlen1 : 1 ≤ x.length := List.length_pos_of_ne_nil hne
    have hmax := hw _ (maxEntry_mem hne)
    have hcost := tableWidth_le_tableCost T
    have hS : 1 ≤ x.length + maxEntry x + 1 := by omega
    have hdist : c * (x.length + maxEntry x + 1) =
        6 * (x.length + maxEntry x + 1) + (c - 6) * (x.length + maxEntry x + 1) := by
      rw [← Nat.add_mul, show 6 + (c - 6) = c from by omega]
    have hslack : (c - 6) * 1 ≤ (c - 6) * (x.length + maxEntry x + 1) :=
      Nat.mul_le_mul_left _ hS
    refine fitsWords_of_max_le (by simp only [foldBound]; omega) ?_
    simp only [Layout.span, layout, foldBound, List.length_cons, List.length_nil]
    omega
  · rintro x -
    rw [const_eq]
    calc 37 * (60 * (x.length + 1) + tableCost T)
        ≤ 37 * ((60 + tableCost T) * (x.length + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          have h₁ : tableCost T ≤ tableCost T * (x.length + 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          rw [Nat.add_mul]
          omega
      _ = 37 * (60 + tableCost T) * (x.length + 1) := by rw [Nat.mul_assoc]

/-! ### The encoding, checked

The machine runs of `TreeFold.lean` are driven by `encTree`, and the
theorem quantifies over `EncodesTree`. That the first produces words of
the shape the second describes is one line and worth having: it is the
only join between the tested harness and the proved statement. -/

#guard encTree [4, 4, 5, 5, 5, 0] [1, 2, 0, 1, 0, 1] =
  6 :: (arrOf 6 (fun i => [4, 4, 5, 5, 5, 0].getD i 0) ++
    arrOf 6 (fun i => [1, 2, 0, 1, 0, 1].getD i 0))

end Lax11Proofs.TreeFold
