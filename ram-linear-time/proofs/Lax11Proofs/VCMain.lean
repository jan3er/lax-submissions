import Lax11Proofs.VCLoop
import Lax11Proofs.CCSweep

/-!
The second theorem, cashed in at the concept surface.

The read phase is the components driver's, one `read` longer; the
search is the loop of `VCLoop`; what is left is the arithmetic. The
layout has six arrays, so one index computation is eight instructions
and the machine pays thirty-seven steps per unit of IMP+ cost; the run
itself costs at most nine hundred times `2 ^ k` per entry of the input
word. The product is the constant of the statement, and no part of it
was fought over.
-/

namespace Lax11Proofs.VCMain

open Lax11.Ram Lax11.RamComputes Lax11.GraphEncoding Lax11.VertexCover
open Lax11Proofs.Imp Lax11Proofs.Compile Lax11Proofs.Reasoning Lax11Proofs.VC

/-- The array extents the driver runs with. -/
def vcExt (n m k : ℕ) (a : String) : ℕ :=
  if a = "off" then n + 1 else if a = "tgt" then 2 * m
  else if a = "mark" then n else k

/-- The machine pays thirty-seven steps per unit of IMP+ cost: six
arrays make one index computation eight instructions long. -/
theorem const_eq : layout.const = 37 := by
  simp [Layout.const, Layout.idxLen, layout]

/-- The whole run of the driver on an encoded instance: the answer
comes out, and the cost is `2 ^ k` times linear in the length of the
word. Every phase was bounded loosely, and this is the sum of those
bounds. -/
theorem vcCom_run {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k m : ℕ}
    (hx : EncodesInstance x n G k) (hm : edgeCount x = m) :
    ∃ (σ' : Env) (K : ℕ), Run vcCom (initEnv (vcExt n m k) x) σ' K ∧
      σ'.out = [if G.vertexCoverNum ≤ (k : ℕ∞) then 1 else 0] ∧
      K ≤ 900 * 2 ^ k * (x.length + 1) := by
  obtain ⟨g, rfl, hg⟩ := hx
  -- the graph block's own edge count: the appended parameter sits past index one
  have hglen := hg.length_eq
  have hmg : edgeCount g = m := by
    rw [← hm]
    simp only [edgeCount, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show 1 < g.length by omega)]
  rw [hmg] at hglen
  -- the word: the two header entries, then the offsets, the targets and the parameter
  obtain ⟨rest, hxr⟩ : ∃ rest, g = n :: m :: rest := by
    rcases g with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hglen; omega
    · simp at hglen; omega
    · have ha : a = n := by simpa [vertexCount] using hg.vertexCount_eq
      have hb : b = m := by simpa [edgeCount] using hmg
      exact ⟨rest, by rw [ha, hb]⟩
  subst hxr
  have hrest : rest.length = 1 + n + 2 * m := by simp at hglen; omega
  set ys := rest.take (n + 1) with hys_def
  set zs := rest.drop (n + 1) with hzs_def
  have hys : ys.length = n + 1 := by rw [hys_def, List.length_take]; omega
  have hzs : zs.length = 2 * m := by rw [hzs_def, List.length_drop]; omega
  have hsplit : rest = ys ++ zs := (List.take_append_drop _ _).symm
  -- what the two arrays hold once they are read in
  have hyd : ∀ i < n + 1, ys.getD i 0 = offset (n :: m :: rest) i := by
    intro i hi
    rw [hys_def, CC.getD_take hi, offset, CC.getD_cons_cons]
  have hzd : ∀ j < 2 * m, zs.getD j 0 = target (n :: m :: rest) j := by
    intro j _
    rw [hzs_def, CC.getD_drop, target, hg.vertexCount_eq]
    have h : 3 + n + j = 2 + (n + 1 + j) := by omega
    rw [h, CC.getD_cons_cons]
  -- the reads
  have e₁ : (initEnv (vcExt n m k) (n :: m :: rest ++ [k])).inp
      = n :: (m :: (rest ++ [k])) := rfl
  set σ₁ : Env := { (initEnv (vcExt n m k) (n :: m :: rest ++ [k])).setVar "n" n with
    inp := m :: (rest ++ [k]) } with hσ₁
  set σ₂ : Env := { σ₁.setVar "m" m with inp := rest ++ [k] } with hσ₂
  set σ₃ : Env := σ₂.setVar "len" (n + 1) with hσ₃
  have r₁ : Run (.read "n") (initEnv (vcExt n m k) (n :: m :: rest ++ [k])) σ₁ 1 :=
    Run.read e₁
  have r₂ : Run (.read "m") σ₁ σ₂ 1 := Run.read rfl
  have r₃ : Run (.assign "len" (.add (.var "n") (.lit 1))) σ₂ σ₃ 4 :=
    (Run.assign (v := n + 1) (by simp [hσ₂, hσ₁, initEnv])).mono (by simp)
  -- the offsets
  obtain ⟨σ₄, O, r₄, hoff₄, hO₄, harr₄, hinp₄, hout₄, hvar₄⟩ :=
    CC.readLoop_run (a := "off") (lim := "len") (by decide) (by decide) (σ := σ₃)
      (g := fun _ => 0) (k := n + 1) (ys := ys) (rest := zs ++ [k])
      (by simp [hσ₃, hσ₂, hσ₁, initEnv, vcExt, replicate_eq_arrOf])
      (by simp [hσ₃]) hys (by simp [hσ₃, hσ₂, hsplit])
  have hO : ∀ i ≤ n, O i = offset (n :: m :: rest) i := fun i hi => by
    rw [hO₄ i (by omega), hyd i (by omega)]
  -- the targets
  set σ₅ : Env := σ₄.setVar "m2" (2 * m) with hσ₅
  have r₅ : Run (.assign "m2" (.add (.var "m") (.var "m"))) σ₄ σ₅ 4 :=
    (Run.assign (v := 2 * m)
      (by simp [hvar₄ "m" (by decide) (by decide), hσ₃, hσ₂, hσ₁, initEnv, two_mul])).mono
        (by simp)
  obtain ⟨σ₆, T, r₆, htgt₆, hT₆, harr₆, hinp₆, hout₆, hvar₆⟩ :=
    CC.readLoop_run (a := "tgt") (lim := "m2") (by decide) (by decide) (σ := σ₅)
      (g := fun _ => 0) (k := 2 * m) (ys := zs) (rest := [k])
      (by rw [hσ₅, arrs_setVar, harr₄ "tgt" (by decide)]
          simp [hσ₃, hσ₂, hσ₁, initEnv, vcExt, replicate_eq_arrOf])
      (by simp [hσ₅]) hzs (by simp [hσ₅, hinp₄])
  have hT : ∀ j < 2 * m, T j = target (n :: m :: rest) j := fun j hj => by
    rw [hT₆ j hj, hzd j hj]
  -- the budget
  set σ₇ : Env := { σ₆.setVar "bud" k with inp := [] } with hσ₇
  have r₇ : Run (.read "bud") σ₆ σ₇ 1 := Run.read hinp₆
  -- what the search starts from
  have hm2₇ : σ₇.vars "m2" = 2 * m := by
    have h6 := hvar₆ "m2" (by decide) (by decide)
    simp [hσ₇, h6, hσ₅]
  have hbud₇ : σ₇.vars "bud" = k := by simp [hσ₇]
  have hzero : ∀ y : String, y ≠ "i" → y ≠ "t" → y ≠ "m2" → y ≠ "bud" → y ≠ "len" →
      y ≠ "n" → y ≠ "m" → σ₇.vars y = 0 := by
    intro y h1 h2 h3 h4 h5 h6 h7
    have e6 := hvar₆ y h1 h2
    have e4 := hvar₄ y h1 h2
    simp [hσ₇, h4, e6, hσ₅, h3, e4, hσ₃, hσ₂, hσ₁, initEnv, h5, h6, h7]
  have hmode₇ : σ₇.vars "mode" = 0 := hzero "mode" (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hans₇ : σ₇.vars "ans" = 0 := hzero "ans" (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have htop₇ : σ₇.vars "top" = 0 := hzero "top" (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have harr₇ : ∀ b : String, σ₇.arrs b = σ₆.arrs b := by intro b; simp [hσ₇]
  have hoff₇ : σ₇.arrs "off" = arrOf (n + 1) O := by
    rw [harr₇, harr₆ "off" (by decide), hσ₅, arrs_setVar, hoff₄]
  have htgt₇ : σ₇.arrs "tgt" = arrOf (2 * m) T := by rw [harr₇, htgt₆]
  have hmark₇ : σ₇.arrs "mark" = arrOf n (fun _ => 0) := by
    rw [harr₇, harr₆ "mark" (by decide), hσ₅, arrs_setVar, harr₄ "mark" (by decide)]
    simp [hσ₃, hσ₂, hσ₁, initEnv, vcExt, replicate_eq_arrOf]
  have hstkA : ∀ a : String, a ≠ "off" → a ≠ "tgt" → a ≠ "mark" →
      σ₇.arrs a = arrOf k (fun _ => 0) := by
    intro a h1 h2 h3
    rw [harr₇, harr₆ a h2, hσ₅, arrs_setVar, harr₄ a h1]
    simp [hσ₃, hσ₂, hσ₁, initEnv, vcExt, h1, h2, h3, replicate_eq_arrOf]
  have hout₇ : σ₇.out = [] := by
    simp [hσ₇, hout₆, hσ₅, hout₄, hσ₃, hσ₂, hσ₁, initEnv]
  have hRep : Rep n m k O T (⟨[], 0, k, 0⟩ : Config n) σ₇ := by
    refine ⟨hm2₇, hoff₇, htgt₇, hmode₇, hbud₇, hans₇, htop₇,
      ⟨fun _ => 0, hmark₇, ?_⟩, fun _ => 0, fun _ => 0, fun _ => 0,
      hstkA "stkU" (by decide) (by decide) (by decide),
      hstkA "stkV" (by decide) (by decide) (by decide),
      hstkA "stkP" (by decide) (by decide) (by decide), ?_⟩
    · intro w hw; simp
    · intro i hi; simp at hi
  -- the search
  obtain ⟨C', τ', K, r₈, hRep', hInv', hmode', hinp', hout', hpay⟩ :=
    searchLoop_run hg hmg hO hT hRep (inv_init G k)
  have hK8 : K ≤ 816 * (2 ^ k * (5 + n + 2 * m)) + 4 := by
    refine hpay.trans ?_
    have ha : 100 * m + 50 * n + 104 ≤ 204 * (5 + n + 2 * m) := by omega
    have hb : pot (⟨[], 0, k, 0⟩ : Config n) ≤ 4 * 2 ^ k := pot_init_le k 0
    calc (100 * m + 50 * n + 104) * pot (⟨[], 0, k, 0⟩ : Config n) + 4
        ≤ 204 * (5 + n + 2 * m) * (4 * 2 ^ k) + 4 :=
          Nat.add_le_add_right (Nat.mul_le_mul ha hb) 4
      _ = 816 * (2 ^ k * (5 + n + 2 * m)) + 4 := by ring
  -- the answer, written out
  have hansv : τ'.vars "ans" = C'.ans := hRep'.2.2.2.2.2.1
  have r₉ : Run (.write (.var "ans")) τ' { τ' with out := τ'.out ++ [C'.ans] } 2 :=
    (Run.write (e := .var "ans") (v := C'.ans) (by simp [hansv])).mono (by simp)
  have hansC : C'.ans = if G.vertexCoverNum ≤ (k : ℕ∞) then 1 else 0 :=
    ans_eq hInv' hmode'
  have s₈ := Run.seq (r₈.mono hK8) r₉
  have s₇ := Run.seq r₇ s₈
  have s₆ := Run.seq r₆ s₇
  have s₅ := Run.seq r₅ s₆
  have s₄ := Run.seq r₄ s₅
  have s₃ := Run.seq r₃ s₄
  have s₂ := Run.seq r₂ s₃
  refine ⟨_, 900 * 2 ^ k * ((n :: m :: rest ++ [k]).length + 1),
    (Run.seq r₁ s₂).mono ?_, ?_, le_rfl⟩
  · have hlen2 : (n :: m :: rest ++ [k]).length + 1 = 5 + n + 2 * m := by
      simp; omega
    rw [hlen2, Nat.mul_assoc]
    have hQ : 5 + n + 2 * m ≤ 2 ^ k * (5 + n + 2 * m) :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)
    generalize 2 ^ k * (5 + n + 2 * m) = Q at hQ ⊢
    omega
  · simp [hout', hout₇, hansC]

/--
---
conclusion: Lax11.VertexCover.exists_fptTime_program_vertexCover
---
Vertex cover is fixed-parameter tractable with the parameter dependence
written into the bound: `vcProgram` decides, on every graph in
compressed sparse row form followed by the parameter `k`, whether the
graph has a vertex cover of at most `k` vertices, within
`33300 * 2 ^ k * (|x| + 1)` machine steps.

# Proof strategy

The witness is the compiled driver `vcProgram`. Its IMP+ source
`vcCom` reads the encoding into the two arrays of the components driver
and the budget into a scalar, then runs the textbook bounded search
tree as a single loop on a mode scalar: descend scans for an edge with
neither endpoint marked and either answers `1`, gives up on the branch,
or pushes a frame and marks one endpoint; backtrack either answers `0`,
flips the top frame to its second endpoint, or pops it. `vcCom_run` is
that run, end to end.

Correctness is the invariant `Inv`, which splits the answer between the
active marking and the frames the search still owes: in descend mode
`Ok ∅ k` holds exactly if the current marking extends to a cover within
the remaining budget or some stored alternative does, in backtrack mode
exactly if some stored alternative does. Six transitions preserve it,
and `ans_eq` reads the concept's answer off the terminal state through
`ok_empty_iff`, the one place where mathlib's `vertexCoverNum` is
touched.

The cost is one amortized argument. The potential of a configuration is
`fPot b = 4·2 ^ b − 3` for the active subtree plus a stored child and
two units of slack per unflipped frame, and every one of the six
transitions strictly decreases it, so the whole tree is paid for by a
single application of the loop rule rather than by a recursion. The
scan inside a descend step is itself flat — one pointer over the target
array and one owner pointer, amortized over slots and owners together —
so a turn of the outer loop costs at most `100m + 50n + 100`. The
factor `2 ^ k` enters exactly once, as the potential of the initial
configuration: `pot ⟨[], 0, k, 0⟩ = 4·2 ^ k − 2`.

`computesInTime_of_run` discharges the compiler, the layout invariant
and the machine in one step, charging `layout.const = 37` machine steps
per unit of IMP+ cost — six arrays, so one index computation is eight
instructions. The array extents are chosen per input, as that lemma
allows: `vcExt n m k` declares `off ↦ n+1`, `tgt ↦ 2m`, `mark ↦ n` and
the three stack arrays `↦ k`, which is exactly the depth the budget
permits.

# What the program is allowed to help itself to

*The budget is a scalar, not a field of the frames.* Both children of a
branch run at one budget less than their parent, so the budget is a
function of the stack depth alone — `bud + top = k` is part of the
invariant — and a push decrements it while a pop restores it. Nothing
is reconstructed on backtracking that was not written down, because
there is nothing to reconstruct.

*The mark array is never initialized.* Fresh memory is zero and `0` is
the marker for "unmarked", so the driver skips the clearing pass that
the components driver needs for its labels. This is not a saving hidden
from the bound: the bound is `2 ^ k` times linear and a clearing pass
is linear, so the pass would have been free. It is omitted because it
is unnecessary, not because it is expensive.

# Attribution

The opening result of parameterized complexity, by the textbook bounded
search tree — Downey and Fellows. The base 2 is the point of the
statement: no reduction rules are applied, and nothing here competes
with the refined analyses that beat it.
-/
theorem exists_fptTime_program_vertexCover :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ),
      ComputesInTime p {x | EncodesInstance x n G k}
        (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
        (fun x => c * 2 ^ k * (x.length + 1)) := by
  refine ⟨vcProgram, 33300, fun n G k => computesInTime_of_run vcCom_ok ?_⟩
  intro x hx
  obtain ⟨σ', K, hrun, hout, hK⟩ := vcCom_run hx rfl
  refine ⟨vcExt n (edgeCount x) k, σ', K, hrun, ?_, ?_⟩
  · rw [hout]
    by_cases h : G.vertexCoverNum ≤ (k : ℕ∞) <;> simp [h]
  · rw [const_eq]
    calc 37 * K ≤ 37 * (900 * 2 ^ k * (x.length + 1)) := Nat.mul_le_mul_left 37 hK
      _ = 33300 * 2 ^ k * (x.length + 1) := by ring

end Lax11Proofs.VCMain
