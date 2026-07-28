import Lax11.Courcelle
import Lax11Proofs.CourcelleDriver
import Lax13Proofs.Transfer

/-!
Courcelle's theorem, cashed in at the concept surface.

Two things happen here. First the driver's phases are run in a row —
the two header reads, the four read loops, the four table prologues,
the seed pass, the sweep and the accept write — each handed the frame
conditions of the ones before it, which is the same assembly the
connected-components driver and the fold schema were closed with.
Second the resulting `Run` is bundled as the pipeline's `Solves`
predicate and handed to `computesInTime_of_solves`, which discharges the
compiler, the layout invariant and the machine in one step; the accept
bit is turned into the sentence by `MsoTable.acceptVal_val`.

The constant is a monster and is meant to be. It is `46` machine steps
per unit of IMP+ cost — nine arrays make one index computation eleven
instructions long — times a hundred per entry of the input word, plus
three times the size of the four tables. The last term is where the
tower in the sentence and the width lives: the table has one row and
one column per `q`-type of a `k`-labelled region, so it is a constant of
`φ` and `k` alone, paid before the input is looked at, and the
quantifier order of the statement is what makes that legitimate.

The word length is dealt with in the same step and in the same place.
The bound the driver runs under is the length of the input word, its
largest entry, and the size of the tables; the same constant that pays
for the time pays for that too, which is why the statement carries one
constant and not two.
-/

namespace Lax11Proofs.Courcelle

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding Lax11.Mso Lax11.CliqueExpr
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax13Proofs.Transfer
open Lax11Proofs.TreeFold Lax11Proofs.MsoTypes Lax11Proofs.MsoTable
open Lax11Proofs.CC (readLoop readLoop_run)
open Lax11.InstanceEncoding (EncodesModelCheckingInstance)

/-! ### The run

The four tables are paid for once, before the input is touched; the
rest is linear in the length of the word, at a hundred units per entry,
every bound loose. -/

/-- What the four tables cost: three units per entry, plus the driver's
fixed overhead. A constant of the table, paid before the input is
looked at. -/
def driverCost (T : Table) : ℕ := 3 * (T.L + T.V + T.V * T.V + T.V) + 60

/-- How wide the table alone asks the word to be: one number per label,
and one per cell of the square combination table. -/
def tableSpan (T : Table) : ℕ := T.L + T.V * T.V

/-- Materializing the table costs at least three units per number the
table makes the machine hold. The two constants are related because both
count the table's entries, which is why one constant serves the time
bound and the word-length hypothesis together. -/
theorem tableSpan_le_driverCost (T : Table) : 3 * tableSpan T + 60 ≤ driverCost T := by
  simp only [tableSpan, driverCost]
  omega

/-- The bound the driver runs under on the word `x`: the length of the
word, its largest entry, and the size of the tables. Everything the run
produces is below one of the three — a count of entries, an entry, a
label or a cell of the square table. -/
def driverBound (T : Table) (x : List ℕ) : ℕ := x.length + maxEntry x + tableSpan T + 1

theorem table_fits (T : Table) (x : List ℕ) : T.Fits (driverBound T x) :=
  ⟨by simp only [driverBound, tableSpan]; omega, by simp only [driverBound, tableSpan]; omega⟩

/-- **The driver, run.** On a word laid out as an instance word is —
two header entries, the rest of the graph block, the node count, and
three arrays of one entry per node — the driver writes the accepting-set
entry of the fold's value at the root, and the cost is linear in the
length of the word plus the tables' fixed price. -/
theorem driverCom_run {B : ℕ} {T : Table} (hT : T.Wf) (hTB : T.Fits B) {acp : ℕ → ℕ}
    {x : List ℕ} {n m N : ℕ} {gr tr : List ℕ}
    (hx : x = n :: m :: (gr ++ N :: tr))
    (hgr : gr.length = n + 1 + (m + m)) (htr : tr.length = 3 * N) (hN : 1 ≤ N)
    (hpar : ∀ i, i + 1 < N → i < tr.getD i 0 ∧ tr.getD i 0 < N)
    (hlab : ∀ i < N, tr.getD (N + i) 0 < T.L)
    (hlt : val T (fun i => tr.getD i 0) (fun i => tr.getD (N + i) 0) (N - 1) < T.V)
    (hxB : ∀ v ∈ x, v < B) (hlenB : x.length < B) (hacpB : ∀ a < T.V, acp a < B) :
    ∃ (σ' : Env) (K : ℕ), Run B (driverCom T acp) (initEnv (driverExt T n m N) x) σ' K ∧
      σ'.out = [acp (val T (fun i => tr.getD i 0) (fun i => tr.getD (N + i) 0) (N - 1))] ∧
      K ≤ 100 * (x.length + 1) + driverCost T := by
  have hxlen : x.length = 3 + gr.length + 3 * N := by rw [hx]; simp; omega
  set par : ℕ → ℕ := fun i => tr.getD i 0 with hpardef
  set lab : ℕ → ℕ := fun i => tr.getD (N + i) 0 with hlabdef
  -- what the bound covers
  have hNB : N < B := by omega
  have hgrB : gr.length < B := by omega
  have hnB : n < B := hxB n (by rw [hx]; exact List.mem_cons_self ..)
  have hmB : m < B := hxB m (by rw [hx]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have h1B : 1 < B := by omega
  have hgrmem : ∀ v ∈ gr, v < B := fun v hv =>
    hxB v (by rw [hx]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_left _ hv)))
  have htrmem : ∀ v ∈ tr, v < B := fun v hv =>
    hxB v (by rw [hx]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_right _ (List.mem_cons_of_mem _ hv))))
  have hVB := hTB.value_le
  have hLB := hTB.label_le
  have hsqB := hTB.square_le
  -- the header
  set σ₀ : Env := initEnv (driverExt T n m N) x with hσ₀
  have hσ₀arr : ∀ a, σ₀.arrs a = List.replicate (driverExt T n m N a) 0 := fun a => by
    rw [hσ₀]; rfl
  set σ₁ : Env := { σ₀.setVar "n" n with inp := m :: (gr ++ N :: tr) } with hσ₁
  have r₁ : Run B (.read "n") σ₀ σ₁ 1 := Run.read (by rw [hσ₀]; simpa [initEnv] using hx)
  set σ₂ : Env := { σ₁.setVar "m" m with inp := gr ++ N :: tr } with hσ₂
  have r₂ : Run B (.read "m") σ₁ σ₂ 1 := Run.read (by rw [hσ₁])
  set σ₃ : Env := σ₂.setVar "len" (n + 1 + (m + m)) with hσ₃
  have r₃ : Run B (.assign "len" (.add (.add (.var "n") (.lit 1)) (.add (.var "m") (.var "m"))))
      σ₂ σ₃ 8 :=
    (Run.assign (v := n + 1 + (m + m)) (by rw [hσ₂, hσ₁]; simp; omega)).mono (by simp)
  have hσ₃arr : ∀ a, σ₃.arrs a = List.replicate (driverExt T n m N a) 0 := fun a => by
    rw [hσ₃, hσ₂, hσ₁]; simpa using hσ₀arr a
  -- the graph block, read and discarded
  obtain ⟨σ₄, _, r₄, _, _, hinp₄⟩ :=
    readLoop_run (B := B) (a := "csr") (lim := "len") (by decide) (by decide) (σ := σ₃)
      (g := fun _ => 0) (k := gr.length) (ys := gr) (rest := N :: tr)
      (by rw [hσ₃arr "csr"]; simp [driverExt, hgr, replicate_eq_arrOf])
      (by rw [hσ₃]; simp [hgr]) rfl (by rw [hσ₃, hσ₂]; simp) hgrB hgrmem
  have hA₄ : ∀ a, a ≠ "csr" → σ₄.arrs a = List.replicate (driverExt T n m N a) 0 :=
    fun a ha => by rw [r₄.frame_arr a (by simp [ha]), hσ₃arr a]
  -- the node count
  set σ₅ : Env := { σ₄.setVar "N" N with inp := tr } with hσ₅
  have r₅ : Run B (.read "N") σ₄ σ₅ 1 := Run.read (by rw [hinp₄])
  have hA₅ : ∀ a, a ≠ "csr" → σ₅.arrs a = List.replicate (driverExt T n m N a) 0 :=
    fun a ha => by rw [hσ₅]; simpa using hA₄ a ha
  have hN₅ : σ₅.vars "N" = N := by rw [hσ₅]; simp
  -- the parents
  obtain ⟨σ₆, p₆, r₆, hpar₆, hp₆, hinp₆⟩ :=
    readLoop_run (B := B) (a := "par") (lim := "N") (by decide) (by decide) (σ := σ₅)
      (g := fun _ => 0) (k := N) (ys := tr.take N) (rest := tr.drop N)
      (by rw [hA₅ "par" (by decide)]; simp [driverExt, replicate_eq_arrOf])
      hN₅ (by simp; omega) (by rw [hσ₅]; simp) hNB
      (fun v hv => htrmem v (List.mem_of_mem_take hv))
  have hpararr₆ : σ₆.arrs "par" = arrOf N par := by
    rw [hpar₆]
    exact arrOf_congr fun i hi => by rw [hp₆ i hi, getD_take hi, hpardef]
  have hA₆ : ∀ a, a ≠ "csr" → a ≠ "par" → σ₆.arrs a = List.replicate (driverExt T n m N a) 0 :=
    fun a h1 h2 => by rw [r₆.frame_arr a (by simp [h2]), hA₅ a h1]
  have hN₆ : σ₆.vars "N" = N := by rw [r₆.frame_var "N" (by decide), hN₅]
  -- the op codes
  obtain ⟨σ₇, l₇, r₇, hlab₇, hl₇, hinp₇⟩ :=
    readLoop_run (B := B) (a := "lab") (lim := "N") (by decide) (by decide) (σ := σ₆)
      (g := fun _ => 0) (k := N) (ys := (tr.drop N).take N) (rest := (tr.drop N).drop N)
      (by rw [hA₆ "lab" (by decide) (by decide)]; simp [driverExt, replicate_eq_arrOf])
      hN₆ (by simp; omega) (by rw [hinp₆]; simp) hNB
      (fun v hv => htrmem v (List.mem_of_mem_drop (List.mem_of_mem_take hv)))
  have hlabarr₇ : σ₇.arrs "lab" = arrOf N lab := by
    rw [hlab₇]
    exact arrOf_congr fun i hi => by
      rw [hl₇ i hi, getD_take hi, getD_drop, hlabdef]
  have hA₇ : ∀ a, a ≠ "csr" → a ≠ "par" → a ≠ "lab" →
      σ₇.arrs a = List.replicate (driverExt T n m N a) 0 :=
    fun a h1 h2 h3 => by rw [r₇.frame_arr a (by simp [h3]), hA₆ a h1 h2]
  have hN₇ : σ₇.vars "N" = N := by rw [r₇.frame_var "N" (by decide), hN₆]
  have hpararr₇ : σ₇.arrs "par" = arrOf N par := by
    rw [r₇.frame_arr "par" (by decide), hpararr₆]
  -- the vertex names, read and discarded
  obtain ⟨σ₈, _, r₈, _, _, hinp₈⟩ :=
    readLoop_run (B := B) (a := "ids") (lim := "N") (by decide) (by decide) (σ := σ₇)
      (g := fun _ => 0) (k := N) (ys := (tr.drop N).drop N) (rest := [])
      (by rw [hA₇ "ids" (by decide) (by decide) (by decide)];
          simp [driverExt, replicate_eq_arrOf])
      hN₇ (by simp; omega) (by rw [hinp₇]; simp) hNB
      (fun v hv => htrmem v (List.mem_of_mem_drop (List.mem_of_mem_drop hv)))
  have hA₈ : ∀ a, a ≠ "csr" → a ≠ "par" → a ≠ "lab" → a ≠ "ids" →
      σ₈.arrs a = List.replicate (driverExt T n m N a) 0 :=
    fun a h1 h2 h3 h4 => by rw [r₈.frame_arr a (by simp [h4]), hA₇ a h1 h2 h3]
  have hN₈ : σ₈.vars "N" = N := by rw [r₈.frame_var "N" (by decide), hN₇]
  have hpararr₈ : σ₈.arrs "par" = arrOf N par := by
    rw [r₈.frame_arr "par" (by decide), hpararr₇]
  have hlabarr₈ : σ₈.arrs "lab" = arrOf N lab := by
    rw [r₈.frame_arr "lab" (by decide), hlabarr₇]
  -- the four tables, materialized
  obtain ⟨σ₉, r₉, hini₉, harr₉, hvar₉, hinp₉, hout₉⟩ :=
    stores_arrOf_run (B := B) (a := "ini") (n := T.L) (σ := σ₈) (f := fun _ => 0) (h := T.init)
      (by rw [hA₈ "ini" (by decide) (by decide) (by decide) (by decide)]
          simp [driverExt, replicate_eq_arrOf])
      hLB (fun l hl => lt_of_lt_of_le (hT.init_lt l hl) hVB)
  obtain ⟨σ₁₀, r₁₀, hrow₁₀, harr₁₀, hvar₁₀, hinp₁₀, hout₁₀⟩ :=
    stores_arrOf_run (B := B) (a := "row") (n := T.V) (σ := σ₉) (f := fun _ => 0)
      (h := fun a => a * T.V)
      (by rw [harr₉ "row" (by decide), hA₈ "row" (by decide) (by decide) (by decide) (by decide)]
          simp [driverExt, replicate_eq_arrOf])
      hVB (fun a ha => by
        show a * T.V < B
        have hstep : (a + 1) * T.V ≤ T.V * T.V := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at hstep
        omega)
  obtain ⟨σ₁₁, r₁₁, htab₁₁, harr₁₁, hvar₁₁, hinp₁₁, hout₁₁⟩ :=
    stores_arrOf_run (B := B) (a := "tab") (n := T.V * T.V) (σ := σ₁₀) (f := fun _ => 0)
      (h := fun k => T.step (k / T.V) (k % T.V))
      (by rw [harr₁₀ "tab" (by decide), harr₉ "tab" (by decide),
            hA₈ "tab" (by decide) (by decide) (by decide) (by decide)]
          simp [driverExt, replicate_eq_arrOf])
      hsqB (fun j hj => by
        have hV : 0 < T.V := by
          rcases Nat.eq_zero_or_pos T.V with h0 | h0
          · rw [h0] at hj; simp at hj
          · exact h0
        exact lt_of_lt_of_le
          (hT.step_lt _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)) _
            (Nat.mod_lt _ hV)) hVB)
  obtain ⟨σ₁₂, r₁₂, hacp₁₂, harr₁₂, hvar₁₂, hinp₁₂, hout₁₂⟩ :=
    stores_arrOf_run (B := B) (a := "acp") (n := T.V) (σ := σ₁₁) (f := fun _ => 0) (h := acp)
      (by rw [harr₁₁ "acp" (by decide), harr₁₀ "acp" (by decide), harr₉ "acp" (by decide),
            hA₈ "acp" (by decide) (by decide) (by decide) (by decide)]
          simp [driverExt, replicate_eq_arrOf])
      hVB hacpB
  -- what the seeding phase starts from
  have hacc₁₂ : σ₁₂.arrs "acc" = arrOf N (fun _ => 0) := by
    rw [harr₁₂ "acc" (by decide), harr₁₁ "acc" (by decide), harr₁₀ "acc" (by decide),
      harr₉ "acc" (by decide), hA₈ "acc" (by decide) (by decide) (by decide) (by decide)]
    simp [driverExt, replicate_eq_arrOf]
  have hlabarr₁₂ : σ₁₂.arrs "lab" = arrOf N lab := by
    rw [harr₁₂ "lab" (by decide), harr₁₁ "lab" (by decide), harr₁₀ "lab" (by decide),
      harr₉ "lab" (by decide), hlabarr₈]
  have hpararr₁₂ : σ₁₂.arrs "par" = arrOf N par := by
    rw [harr₁₂ "par" (by decide), harr₁₁ "par" (by decide), harr₁₀ "par" (by decide),
      harr₉ "par" (by decide), hpararr₈]
  have hini₁₂ : σ₁₂.arrs "ini" = arrOf T.L T.init := by
    rw [harr₁₂ "ini" (by decide), harr₁₁ "ini" (by decide), harr₁₀ "ini" (by decide), hini₉]
  have hrow₁₂ : σ₁₂.arrs "row" = arrOf T.V (fun a => a * T.V) := by
    rw [harr₁₂ "row" (by decide), harr₁₁ "row" (by decide), hrow₁₀]
  have htab₁₂ : σ₁₂.arrs "tab" =
      arrOf (T.V * T.V) (fun k => T.step (k / T.V) (k % T.V)) := by
    rw [harr₁₂ "tab" (by decide), htab₁₁]
  have hN₁₂ : σ₁₂.vars "N" = N := by rw [hvar₁₂, hvar₁₁, hvar₁₀, hvar₉, hN₈]
  have hout₅ : σ₅.out = σ₄.out := rfl
  have hout₃ : σ₃.out = σ₀.out := rfl
  have hout₀ : σ₀.out = [] := rfl
  have hout₁₂' : σ₁₂.out = [] := by
    rw [hout₁₂, hout₁₁, hout₁₀, hout₉, r₈.out_eq (by decide), r₇.out_eq (by decide), r₆.out_eq (by decide), hout₅, r₄.out_eq (by decide), hout₃, hout₀]
  -- the seeds
  obtain ⟨σ₁₃, r₁₃, hacc₁₃, harr₁₃, hinp₁₃, hout₁₃, hvar₁₃⟩ :=
    seedLoop_run (B := B) (T := T) hT hTB (lab := lab) (N := N) (σ := σ₁₂) (f := fun _ => 0)
      hacc₁₂ hlabarr₁₂ hini₁₂ hN₁₂ hlab hNB
  -- the sweep
  obtain ⟨σ₁₄, r₁₄, hacc₁₄, harr₁₄, hinp₁₄, hout₁₄, hvar₁₄⟩ :=
    pushLoop_run (B := B) (T := T) hT hTB (par := par) (lab := lab) (N := N) (σ := σ₁₃) hacc₁₃
      (by rw [harr₁₃ "par" (by decide), hpararr₁₂])
      (by rw [harr₁₃ "row" (by decide), hrow₁₂])
      (by rw [harr₁₃ "tab" (by decide), htab₁₂])
      (by rw [hvar₁₃ "N" (by decide), hN₁₂]) hN hpar hlab hNB
  -- the accept bit, written out
  have hN₁₄ : σ₁₄.vars "N" = N := by
    rw [hvar₁₄ "N" (by decide) (by decide), hvar₁₃ "N" (by decide), hN₁₂]
  have hacp₁₄ : σ₁₄.arrs "acp" = arrOf T.V acp := by
    rw [harr₁₄ "acp" (by decide), harr₁₃ "acp" (by decide), hacp₁₂]
  have hidxeval : (Expr.sub (.var "N") (.lit 1)).evalB B σ₁₄ = some (N - 1) := by
    have h := evalB_bin (op := .sub) (evalB_var (show σ₁₄.vars "N" < B by rw [hN₁₄]; omega))
      (evalB_lit (show (1 : ℕ) < B by omega)) (by simp [hN₁₄]; omega)
    simpa [hN₁₄] using h
  have heval : (Expr.get "acp" (.get "acc" (.sub (.var "N") (.lit 1)))).evalB B σ₁₄ =
      some (acp (val T par lab (N - 1))) :=
    evalB_get
      (evalB_get hidxeval (by rw [hacc₁₄]; exact getElem?_arrOf _ (show N - 1 < N by omega))
        (lt_of_lt_of_le hlt hVB))
      (by rw [hacp₁₄]; exact getElem?_arrOf _ hlt) (hacpB _ hlt)
  have r₁₅ : Run B (.write (.get "acp" (.get "acc" (.sub (.var "N") (.lit 1))))) σ₁₄
      { σ₁₄ with out := σ₁₄.out ++ [acp (val T par lab (N - 1))] } 6 :=
    (Run.write heval).mono (by simp)
  -- the phases in a row
  refine ⟨_, _, Run.seq r₁ <| Run.seq r₂ <| Run.seq r₃ <| Run.seq r₄ <| Run.seq r₅ <|
      Run.seq r₆ <| Run.seq r₇ <| Run.seq r₈ <| Run.seq r₉ <| Run.seq r₁₀ <|
      Run.seq r₁₁ <| Run.seq r₁₂ <| Run.seq r₁₃ <| Run.seq r₁₄ r₁₅, ?_, ?_⟩
  · rw [show σ₁₄.out = [] by rw [hout₁₄, hout₁₃, hout₁₂']]
    simp
  · rw [driverCost]; omega

/-! ### The theorem

The table of `MsoTable.lean` at `q = rank φ`, the accepting set of C9
as the last of the four arrays, and the constant `46` machine steps per
unit of IMP+ cost. -/

/-- The machine pays forty-six steps per unit of IMP+ cost: nine arrays
make one index computation eleven instructions long. -/
theorem const_eq : layout.const = 46 := by
  simp [Layout.const, Layout.idxLen, layout]

open Classical in
/-- The accepting-set array of the driver: `1` at the number of a type
that the sentence holds in, `0` everywhere else. -/
noncomputable def acpArr (q k : ℕ) (φ : MSO 0 0) (a : ℕ) : ℕ :=
  if acceptVal q k φ a then 1 else 0

theorem acpArr_lt_two {q k : ℕ} {φ : MSO 0 0} (a : ℕ) : acpArr q k φ a < 2 := by
  rw [acpArr]; split <;> omega

open Classical in
/-- What the pipeline asks of the driver: on every admissible input it
decides the sentence, at a cost of a hundred per entry of the input word
plus the tables' fixed price, with every value it produces below the
length of the word, its largest entry and the size of the tables. -/
theorem driverCom_solves (φ : MSO 0 0) (k n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ) :
    Solves layout (driverCom (table (rank φ) k) (acpArr (rank φ) k φ))
      {x | EncodesModelCheckingInstance x n G k ∧
        ∀ v ∈ x, 46 * (100 + driverCost (table (rank φ) k)) * (x.length + v + 1) ≤ 2 ^ w}
      (fun _ => if Sat G Fin.elim0 Fin.elim0 φ then [1] else [0])
      (driverBound (table (rank φ) k))
      (fun x => 100 * (x.length + 1) + driverCost (table (rank φ) k)) where
  ok := driverCom_ok _ _
  inp := fun x _ v hv => by
    have := le_maxEntry hv
    simp only [driverBound]
    omega
  run := by
    rintro x ⟨hx, -⟩
    set q := rank φ with hq
    set T := table q k with hTdef
    set B := driverBound T x with hBdef
    obtain ⟨m, N, gr, tr, e, hxeq, hgr, htr, hN, hNx, hgrx, hpar, hlab, hvf, henc⟩ :=
      instance_tape hx
    -- the root's value is the number of the root's type
    have hroot : val T (fun i => tr.getD i 0) (fun i => tr.getD (N + i) 0) (N - 1) =
        enc (Val.done (typeOf q e)) :=
      val_eq_typeOf q e (ValidFor.toValid hvf) (N - 1) henc
    have hlt : val T (fun i => tr.getD i 0) (fun i => tr.getD (N + i) 0) (N - 1) < T.V := by
      rw [hroot]; exact enc_lt _
    have hxlen : x.length = 3 + gr.length + 3 * N := by rw [hxeq]; simp; omega
    have hxB : ∀ v ∈ x, v < B := fun v hv => by
      have := le_maxEntry hv; simp only [hBdef, driverBound]; omega
    have hlenB : x.length < B := by simp only [hBdef, driverBound]; omega
    obtain ⟨σ', K, hrun, hout, hK⟩ :=
      driverCom_run (B := B) (T := T) (table_wf q k) (table_fits T x)
        (acp := acpArr q k φ) hxeq hgr htr hN hpar hlab hlt hxB hlenB
        (fun a _ => lt_of_lt_of_le (acpArr_lt_two a) (by simp only [hBdef, driverBound]; omega))
    refine ⟨driverExt T n m N, σ', hrun.mono hK, ?_⟩
    rw [hout, acpArr]
    by_cases hs : Sat G Fin.elim0 Fin.elim0 φ
    · rw [if_pos hs, if_pos ((acceptVal_val q φ (le_of_eq hq.symm) hvf henc).mpr hs)]
    · rw [if_neg hs]
      have hnot : ¬ (acceptVal q k φ
          (val T (fun i => tr.getD i 0) (fun i => tr.getD (N + i) 0) (N - 1)) = true) :=
        fun h => hs ((acceptVal_val q φ (le_of_eq hq.symm) hvf henc).mp h)
      rw [if_neg hnot]

open Classical in
/--
---
conclusion: Lax11.Courcelle.exists_linearTime_program_modelChecking
---
Model checking monadic second-order logic is linear time on a word
random access machine for graphs presented together with a
`k`-expression: for every sentence and every width bound there is one
program which, on a compressed sparse row block followed by a
`k`-expression that evaluates to it, writes `1` if the sentence holds in
the graph and `0` if it does not, within a constant multiple of the
length of the input, at every word length at which that constant
multiple of the length and of each entry of the input fits into a word.

# Proof strategy

The witness is the compiled driver `driverProgram (table q k)`, with
`q = rank φ` — the tree-fold schema of `TreeFold.lean`, instantiated
with the type table of `MsoTable.lean` and given the instance word's
front end.

The mathematics is finished before the program is looked at.
`val_eq_typeOf` says the fold's value at a node is the number of the
`q`-type of the subexpression rooted there, by structural induction on
the expression with one congruence of `MsoCliqueOps.lean` per
constructor; `acceptVal_val` turns the value at the root into the truth
of the sentence, by adequacy and the root conditions of `ValidFor`.
Both are statements about the *pure* fold, with no environment in them.

What is left is the word. `instance_tape` decomposes an admissible input
into the segments the reads consume — two header entries, the rest of
the graph block, the node count, and three arrays of one entry per node
— and `encExpr_of_encodesExpr` forgets the surface encoding relation to
the one the induction is stated against. `driverCom_run` then runs the
phases in a row: the graph block and the vertex-name array are read into
arrays nothing ever reads again, the parents and the op codes into the
schema's own, the four tables are materialized by
`stores_arrOf_run`, and `seedLoop_run` and `pushLoop_run` do the fold.
The epilogue is one `write` of `acp[acc[N-1]]`, which is in range
because the root's value is the number of a type.

`computesInTime_of_solves` discharges the compiler, the layout invariant
and the machine, charging `layout.const = 46` machine steps per unit of
IMP+ cost. The array extents are chosen per input, as that lemma allows.

# Where the constant comes from

The bound is `46 * (100 + driverCost (table q k))` per entry of the
input word. The first factor is the layout — nine arrays, so one array
access compiles to eleven instructions — and the hundred is the driver's
own per-entry cost, every loop bounded loosely and nothing fought over.
The third term is the price of materializing the four tables, three
units per entry, and it is where the tower lives: the type table has one
row and one column per `q`-type of a `k`-labelled region, a number that
grows faster than any tower of exponentials in `q`. It is paid once,
before the input is read, which the order of the quantifiers permits —
the sentence and the width bound come first, then the program and the
constant, then the graph.

What the theorem claims about that constant is that it depends on the
sentence and the width bound *alone*: the tables are materialized before
the input is read, and the per-node work of the fold is a fixed number
of array accesses whatever the size of the alphabet. What it does not
claim is any bound on it. None is computed anywhere in the development,
and the absence is deliberate rather than an oversight — every known
proof of Courcelle's theorem makes the dependence non-elementary.

# Where the word length is paid for

The machine truncates every value modulo `2 ^ w`, so the run on the
machine is the run in the unbounded semantics only as long as nothing
the program computes reaches `2 ^ w`. The bound the driver is proved
under is `driverBound`: the length of the input word, plus its largest
entry, plus the size of the tables. All three summands are needed and
none of them is loose.

*The length.* Every count the program keeps — the number of nodes, the
length of the graph block, the loop counters, the offsets into the four
arrays of the expression block — is a count of entries of the word.

*The largest entry.* Most entries of an instance are small: vertex
numbers, offsets and node numbers are below the length of the word, and
an operation code is below the number of operations at width `k`, which
the tables' size already covers. Two families are not, because the
encoding deliberately does not constrain them — the parent entry of the
root, which nothing points through, and
the vertex name at a node whose operation creates no vertex. The machine
reads its whole tape whatever it does with it, so those entries pass
through the accumulator and have to be words; there is nothing to prove
about them and nothing to be gained by pretending they are small, so the
bound names the largest entry and the statement's fitting condition
supplies it. That is the only reason the condition quantifies over the
entries of the word rather than over its length alone.

*The tables.* A label indexes the array of seeds and a cell of the
square combination table is indexed by two values at once, so `T.L` and
`T.V * T.V` are numbers the machine holds. This is the one place where
the size of the type alphabet — the tower — reaches the word length
rather than only the constant, and it is honest that it does: a machine
whose words cannot number the types cannot run the table. It costs the
statement nothing, because the constant is chosen after the sentence and
the width bound, and `tableSpan_le_driverCost` says the constant that
pays for materializing the table already pays for holding its indices.

So the compiled program needs `11 + 9 * driverBound` cells to be words,
and the statement's hypothesis — that
`46 * (100 + driverCost) * (|x| + v + 1)` is a word for every entry `v`
— gives that at the largest entry, with a margin nobody has to compute.

# Formalization notes

These are the honesty items of the theorem: what the statement claims,
where it and a textbook proof part company, and what a reader is
entitled to know was decided rather than proved. The definitions carry
their own notes — the logic in `Lax11.Mso`, `k`-expressions in
`Lax11.CliqueExpr`, the input format in `Lax11.InstanceEncoding` — and what is
said there is not repeated here.

*The width measure is cliquewidth, and the conversion from treewidth is
not formalized.* What is proved is the Courcelle–Makowsky–Rotics form:
MSO₁ model checking in linear time on graphs presented with a
`k`-expression. Bounded treewidth implies bounded cliquewidth, so the
class covered here contains every class of bounded treewidth; but
getting the treewidth form of the statement out of this one needs a
conversion of a tree decomposition of width `w` into a `k`-expression
with `k` bounded in terms of `w`, and that conversion is not formalized.
Anyone who wants the treewidth statement should treat it as unproved
here. The same holds one level up, at the input: the theorem takes a
`k`-expression, it does not compute one. Deciding cliquewidth is
NP-hard and approximating it is the theorem of Oum and Seymour; neither
is in this submission. That is exactly the status a linear-time
treewidth algorithm would have had — a separate theorem, with its own
proof, which composes with this one to give an algorithm that takes only
the graph.

*The expression is a certificate, and the program reads only two of its
arrays.* The program never looks at the compressed sparse row block, and
never at the vertex-name array of the expression block: it reads the
whole word, because it must get past the graph block to reach the
expression block and because the machine reads its tape in order, but it
*uses* only the parent array and the operation-code array. The other two
go into arrays no later expression of the program mentions. This is not
laziness dressed up: the type of a subexpression is a function of the
types of its children and of the operation at its root, and of nothing
else. The graph block is what makes `Sat G φ` refer to a graph in the
first place, and the vertex names are what make the second block a
`k`-expression rather than the shape of one, so that a reviewer can
check the certificate against the graph. Both only lengthen the input,
so reading past them costs a constant per entry and the bound is
unaffected.

*The type table is noncomputable, and that is the shape of the
statement.* The fold is driven by a table — a finite value alphabet, an
initial value per operation symbol, a binary combination. Here the
values are the `q`-types of `k`-labelled regions, and the table is
extracted from the composition congruences by `Fintype` together with
choice: for each pair of types the entry is *a* type realized by some
gluing of two regions with those types, and the congruences say that the
choice does not matter. Nothing in the development computes this table,
and nothing could — the statement is an existential over programs, and
the truth of a monadic second-order sentence in an arbitrary graph is
not something the meta level decides on the way to constructing one. A
reader who wants the machine to *print* the table is asking for an
effective bound on the type space, which is the tower this development
declines to estimate. What the noncomputability does not touch is the
program: `table q k` is a noncomputable inhabitant of an ordinary
structure type and the generator consumes it as data, so the same
generator applied to a computable table produces a program that runs.
The table's content is carried by proof; the program text around it is
carried by evaluation.

*The multiplication instruction is never used.* The machine of
`Lax13.Ram` has one, and under a unit-cost measure a linear-time claim
that leans on it is at risk of being an artifact of the model. The fold
indexes a two-dimensional table, which is where a multiplication would
naturally appear — the entry for `a` and `b` sits at `a·V + b`. Instead
the row bases `a·V` are themselves materialized, once, in the prologue,
as the array `row`, and a lookup is `tab[row[a] + b]`: two array reads
and an addition. The prologue that fills `row` is a sequence of stores
whose length is the table's size, a constant fixed before the input is
read. So the compiled program contains no multiplication anywhere —
`CourcelleDriver.lean` checks that by filtering the generated
instruction list, since it is a property of the program text and the
program text is the same for every table — and the claim survives the
strictest reading of the cost model, the one that would charge for a
product of two words, rather than depending on a generous one.

*The machine-versus-model check runs a stand-in table.* House
discipline in this submission is that every program is run — by `#eval`
inside the build, against the pure model it is proved to implement —
before anything about it is proved. The driver is run that way, but it
cannot be run with the type table, which is noncomputable by
construction. `CourcelleDriver.lean` therefore instantiates the
*generic* driver with `edgeTable`: a hand-written table over the same
operation alphabet, decoded by the same `Op.decode`, whose values are
three bits — class `0` is nonempty, class `1` is nonempty, there is an
edge — together with the partial states the sequential fold needs. That
is a genuine cliquewidth dynamic program, and the two sentences it
decides on the path `0—1—2` are "some two vertices are adjacent" and its
negation; the machine writes `1` and `0`, and `#guard`s check that
against the pure fold. So every line of program text is exercised: the
same reads, the same prologue, the same seed and push loops, the same
epilogue, the same decoder. What is not exercised is the content of the
real table, and that is exactly what `val_eq_typeOf` carries. Plumbing
is machine-checked, mathematics is proof-carried, and neither is asked
to vouch for the other.

*`TreeDecomp.lean` is kept, as theory that no longer feeds the theorem.*
The pivot to cliquewidth stranded a file of tree-decomposition set
theory: descendants as parent-map iteration, validity and width, the
tree order, the highest node containing a vertex, subtrees as unions of
bags, the separation lemma and the edge-placement lemmas. Nothing in the
proof of the theorem imports it. It is kept anyway, and the argument is
that it is not scaffolding but a self-contained piece of mathematics
that happens to be stated in the shape this machine wants — nodes are
numbers, and the parent map is the same `ℕ → ℕ` the fold sweeps.
Deleting it would cost a future MSO₂ or treewidth submission its whole
combinatorial layer for no gain beyond a smaller build; keeping it costs
one file that imports only mathlib and is imported by nothing. It is
named here so that no reviewer spends time looking for the place where
it is used.

*One device on the trust surface is not textbook.* Everything a reader
has to check by eye — the machine, what it means to compute within a
time bound, the graph encoding, the syntax and satisfaction of the
logic, `k`-expressions and their evaluation, the input format, and the
statement itself — is written to be the object a paper would write, with
one exception, and it should be named plainly. Variables in formulas are
de Bruijn positions, so a reader checking `Lax11.Mso` against a textbook
must translate between `∃x. ∃y. adj(x, y)` and
`MSO.exV (MSO.exV (MSO.adj 0 1))`, and must hold in mind that a
quantifier binds at the *last* position, so that the outermost variable
is `0` and no index is ever shifted. Every other deviation in this
development is inside the proof package, where the kernel is the
reviewer. This one is not, and it is the price paid for keeping
substitution off the surface entirely.

# Attribution

Courcelle's theorem in the Courcelle–Makowsky–Rotics form: monadic
second-order model checking in linear time on graphs of bounded
cliquewidth, given a `k`-expression. The type algebra and the
composition lemma are the standard Ehrenfeucht–Fraïssé argument; the
program is the textbook bottom-up fold.
-/
theorem exists_linearTime_program_modelChecking :
    ∀ (φ : MSO 0 0) (k : ℕ),
      ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ),
        ComputesInTime w p
          {x | EncodesModelCheckingInstance x n G k ∧
            ∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w}
          (fun _ => if Sat G Fin.elim0 Fin.elim0 φ then [1] else [0])
          (fun x => c * (x.length + 1)) := by
  intro φ k
  refine ⟨driverProgram (table (rank φ) k) (acpArr (rank φ) k φ),
    46 * (100 + driverCost (table (rank φ) k)), fun n G w =>
      computesInTime_of_solves (driverCom_solves φ k n G w) ?_ ?_⟩
  · rintro x ⟨hx, hw⟩
    set T := table (rank φ) k with hTdef
    set c := 46 * (100 + driverCost T) with hc
    -- the word has to hold the bound and the cells the layout addresses
    have hne : x ≠ [] := by
      obtain ⟨_, _, _, _, _, hxeq, _⟩ := instance_tape hx
      rw [hxeq]; simp
    have hlen1 : 1 ≤ x.length := List.length_pos_of_ne_nil hne
    have hmax := hw _ (maxEntry_mem hne)
    have hcost := tableSpan_le_driverCost T
    have hS : 1 ≤ x.length + maxEntry x + 1 := by omega
    have hdist : c * (x.length + maxEntry x + 1) =
        9 * (x.length + maxEntry x + 1) + (c - 9) * (x.length + maxEntry x + 1) := by
      rw [← Nat.add_mul, show 9 + (c - 9) = c from by omega]
    have hslack : (c - 9) * 1 ≤ (c - 9) * (x.length + maxEntry x + 1) :=
      Nat.mul_le_mul_left _ hS
    refine fitsWords_of_max_le (by simp only [driverBound]; omega) ?_
    simp only [Layout.span, layout, driverBound, List.length_cons, List.length_nil]
    omega
  · rintro x -
    rw [const_eq]
    set T := table (rank φ) k with hTdef
    calc 46 * (100 * (x.length + 1) + driverCost T)
        ≤ 46 * ((100 + driverCost T) * (x.length + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          have h₁ : driverCost T ≤ driverCost T * (x.length + 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          rw [Nat.add_mul]
          omega
      _ = 46 * (100 + driverCost T) * (x.length + 1) := by rw [Nat.mul_assoc]

end Lax11Proofs.Courcelle
