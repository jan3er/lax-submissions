import Lax11Proofs.TreeFoldRun

/-!
The tree fold, end to end.

The phases are proved; what is left is to run them in a row, hand each
one the frame conditions of the ones before, and cash the result in at
the machine. The result is the schema's theorem: for every table there
is a machine program that reads a parent-pointer tree and writes the
fold of that table over it, in time linear in the length of the word.

Two things about the constant deserve saying out loud, because the
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
-/

namespace Lax11Proofs.TreeFold

open Lax11.Ram Lax11.RamComputes Lax11Proofs.Imp Lax11Proofs.Compile Lax11Proofs.Reasoning
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

/-- The whole run of the schema on an encoded tree: the root's value
comes out, and the cost is linear in the length of the word plus the
table's own materialization. Every phase was bounded loosely and this
is the sum of those bounds. -/
theorem foldCom_run {T : Table} (hT : T.Wf) {x : List ℕ} {N : ℕ} {par lab : ℕ → ℕ}
    (hx : EncodesTree x N par lab T.L) :
    ∃ (σ' : Env) (K : ℕ), Run (foldCom T) (initEnv (foldExt T N) x) σ' K ∧
      σ'.out = [val T par lab (N - 1)] ∧ K ≤ 60 * (x.length + 1) + tableCost T := by
  obtain ⟨hN1, hxeq, hpar, hlab⟩ := hx
  have hlen : x.length = 1 + N + N := by rw [hxeq]; simp; omega
  have hparN : ∀ i, i + 1 < N → par i < N := fun i hi => (hpar i hi).2
  -- the header
  set σ₀ : Env := initEnv (foldExt T N) x with hσ₀
  have hσ₀arr : ∀ a, σ₀.arrs a = List.replicate (foldExt T N a) 0 := fun a => by rw [hσ₀]; rfl
  set σ₁ : Env := { σ₀.setVar "N" N with inp := arrOf N par ++ arrOf N lab } with hσ₁
  have r₁ : Run (.read "N") σ₀ σ₁ 1 := Run.read (by rw [hσ₀]; simpa [initEnv] using hxeq)
  have hσ₁arr : ∀ a, σ₁.arrs a = List.replicate (foldExt T N a) 0 := fun a => by
    rw [hσ₁]; simpa using hσ₀arr a
  -- the parents
  obtain ⟨σ₂, p₂, r₂, hpar₂, hp₂, harr₂, hinp₂, hout₂, hvar₂⟩ :=
    readLoop_run (a := "par") (lim := "N") (by decide) (by decide) (σ := σ₁)
      (g := fun _ => 0) (k := N) (ys := arrOf N par) (rest := arrOf N lab)
      (by rw [hσ₁arr "par"]; simp [foldExt, replicate_eq_arrOf])
      (by simp [hσ₁]) (by simp) (by simp [hσ₁])
  have hpararr₂ : σ₂.arrs "par" = arrOf N par := by
    rw [hpar₂]; exact arrOf_congr fun i hi => by rw [hp₂ i hi, getD_arrOf _ hi]
  -- the labels
  obtain ⟨σ₃, l₃, r₃, hlab₃, hl₃, harr₃, hinp₃, hout₃, hvar₃⟩ :=
    readLoop_run (a := "lab") (lim := "N") (by decide) (by decide) (σ := σ₂)
      (g := fun _ => 0) (k := N) (ys := arrOf N lab) (rest := [])
      (by rw [harr₂ "lab" (by decide), hσ₁arr "lab"]; simp [foldExt, replicate_eq_arrOf])
      (by rw [hvar₂ "N" (by decide) (by decide), hσ₁]; simp) (by simp) (by simp [hinp₂])
  have hlabarr₃ : σ₃.arrs "lab" = arrOf N lab := by
    rw [hlab₃]; exact arrOf_congr fun i hi => by rw [hl₃ i hi, getD_arrOf _ hi]
  have hN₃ : σ₃.vars "N" = N := by
    rw [hvar₃ "N" (by decide) (by decide), hvar₂ "N" (by decide) (by decide), hσ₁]; simp
  -- the table, materialized: seeds, row bases, combinations
  obtain ⟨σ₄, r₄, hini₄, harr₄, hvar₄, hinp₄, hout₄⟩ :=
    stores_arrOf_run (a := "ini") (n := T.L) (σ := σ₃) (f := fun _ => 0) (h := T.init)
      (by rw [harr₃ "ini" (by decide), harr₂ "ini" (by decide), hσ₁arr "ini"]
          simp [foldExt, replicate_eq_arrOf])
  obtain ⟨σ₅, r₅, hrow₅, harr₅, hvar₅, hinp₅, hout₅⟩ :=
    stores_arrOf_run (a := "row") (n := T.V) (σ := σ₄) (f := fun _ => 0)
      (h := fun a => a * T.V)
      (by rw [harr₄ "row" (by decide), harr₃ "row" (by decide), harr₂ "row" (by decide),
              hσ₁arr "row"]
          simp [foldExt, replicate_eq_arrOf])
  obtain ⟨σ₆, r₆, htab₆, harr₆, hvar₆, hinp₆, hout₆⟩ :=
    stores_arrOf_run (a := "tab") (n := T.V * T.V) (σ := σ₅) (f := fun _ => 0)
      (h := fun k => T.step (k / T.V) (k % T.V))
      (by rw [harr₅ "tab" (by decide), harr₄ "tab" (by decide), harr₃ "tab" (by decide),
              harr₂ "tab" (by decide), hσ₁arr "tab"]
          simp [foldExt, replicate_eq_arrOf])
  -- what the seeding phase starts from
  have hacc₆ : σ₆.arrs "acc" = arrOf N (fun _ => 0) := by
    rw [harr₆ "acc" (by decide), harr₅ "acc" (by decide), harr₄ "acc" (by decide),
      harr₃ "acc" (by decide), harr₂ "acc" (by decide), hσ₁arr "acc"]
    simp [foldExt, replicate_eq_arrOf]
  have hlabarr₆ : σ₆.arrs "lab" = arrOf N lab := by
    rw [harr₆ "lab" (by decide), harr₅ "lab" (by decide), harr₄ "lab" (by decide), hlabarr₃]
  have hpararr₆ : σ₆.arrs "par" = arrOf N par := by
    rw [harr₆ "par" (by decide), harr₅ "par" (by decide), harr₄ "par" (by decide),
      harr₃ "par" (by decide), hpararr₂]
  have hini₆ : σ₆.arrs "ini" = arrOf T.L T.init := by
    rw [harr₆ "ini" (by decide), harr₅ "ini" (by decide), hini₄]
  have hrow₆ : σ₆.arrs "row" = arrOf T.V (fun a => a * T.V) := by
    rw [harr₆ "row" (by decide), hrow₅]
  have hN₆ : σ₆.vars "N" = N := by rw [hvar₆, hvar₅, hvar₄, hN₃]
  have hout₆' : σ₆.out = [] := by
    rw [hout₆, hout₅, hout₄, hout₃, hout₂, hσ₁]; simp [hσ₀, initEnv]
  -- the seeds
  obtain ⟨σ₇, r₇, hacc₇, harr₇, hinp₇, hout₇, hvar₇⟩ :=
    seedLoop_run (T := T) (lab := lab) (N := N) (σ := σ₆) (f := fun _ => 0)
      hacc₆ hlabarr₆ hini₆ hN₆ hlab
  -- the sweep
  obtain ⟨σ₈, r₈, hacc₈, harr₈, hinp₈, hout₈, hvar₈⟩ :=
    pushLoop_run (T := T) hT (par := par) (lab := lab) (N := N) (σ := σ₇) hacc₇
      (by rw [harr₇ "par" (by decide), hpararr₆])
      (by rw [harr₇ "row" (by decide), hrow₆])
      (by rw [harr₇ "tab" (by decide), htab₆])
      (by rw [hvar₇ "N" (by decide), hN₆]) hN1 hpar hlab
  -- the root's value, written out
  have hN₈ : σ₈.vars "N" = N := by
    rw [hvar₈ "N" (by decide) (by decide), hvar₇ "N" (by decide), hN₆]
  have heval : (Expr.get "acc" (.sub (.var "N") (.lit 1))).eval σ₈ =
      some (val T par lab (N - 1)) := by
    simp [hacc₈, hN₈, getElem?_arrOf _ (show N - 1 < N by omega)]
  have r₉ : Run (.write (.get "acc" (.sub (.var "N") (.lit 1)))) σ₈
      { σ₈ with out := σ₈.out ++ [val T par lab (N - 1)] } 5 :=
    (Run.write heval).mono (by simp [Expr.size])
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

/-- **The tree-fold schema.** For every well-formed table there is a
machine program that computes the table's fold over any parent-pointer
tree given in the schema's encoding, in time linear in the length of
the word.

The constant depends on the table and the program is generated from it:
this is the non-uniformity the eventual instantiation needs, and it is
the reason the table may be as large — and as noncomputable — as the
mathematics that produces it. -/
theorem exists_linearTime_program_treeFold {T : Table} (hT : T.Wf) :
    ∃ (p : Program) (c : ℕ), ∀ (N : ℕ) (par lab : ℕ → ℕ),
      ComputesInTime p {x | EncodesTree x N par lab T.L}
        (fun _ => [val T par lab (N - 1)]) (fun x => c * (x.length + 1)) := by
  refine ⟨foldProgram T, 37 * (60 + tableCost T), fun N par lab =>
    computesInTime_of_run (foldCom_ok T) ?_⟩
  intro x hx
  obtain ⟨σ', K, hrun, hout, hK⟩ := foldCom_run hT hx
  refine ⟨foldExt T N, σ', K, hrun, hout, ?_⟩
  have h₁ : tableCost T ≤ tableCost T * (x.length + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h₂ : K ≤ (60 + tableCost T) * (x.length + 1) := by rw [Nat.add_mul]; omega
  calc layout.const * K = 37 * K := by rw [const_eq]
    _ ≤ 37 * ((60 + tableCost T) * (x.length + 1)) := Nat.mul_le_mul_left _ h₂
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
