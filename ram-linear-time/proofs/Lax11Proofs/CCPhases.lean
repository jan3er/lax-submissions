import Lax11Proofs.CC
import Lax13Proofs.Lib.Fill

/-!
The three straight phases of the driver: reading the input word into an
array, clearing the label array, and writing the labels out. They are
proved here, away from the search, because they say nothing about graphs
— a read loop copies a prefix of the tape into an array whatever the
numbers mean — and because together they fix the shape every phase lemma
of this development has: what the phase does to *its* array, what it
costs, and under which bound it stays.

All three *are* the same loop, `i := 0; while i < m do …`, and none of
them owns it. `Spec.forRangeZero` is that loop — the counter, the cost,
and the reading of the failed condition — and `Lib.Fill` is what two of
the three then do to their array, one cell per turn; `initLab` is a
single application of `Fill.loop_spec` and has no proof of its own at
all. What is left of a phase is its body, and `run_vcg` walks all three
of those, tape operations included.

What a phase leaves alone is not stated: which names a command may touch
is syntactic, and `Lax13Proofs.Frame` decides it, so a caller recovers a
frame condition from the run the conclusion already carries at the price
of one `by decide`. `readLoop`'s input tape is the exception — it is
consumed, so what is left of it is a conclusion. And the value bound `B`
costs each phase one hypothesis and no invariant clause: all it produces
is a counter inside its array, a number just read, or one already there.
-/

namespace Lax11Proofs.CC

open Lax13.Ram Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning
open Lax13Proofs.Reasoning.Lib

/-! ### Reading a block of the tape into an array -/

/-- What `readLoop` may store into, and what it may assign to. Its limit
`lim` is not among the latter, which is why the caller may pass a scalar
it wants to keep; a frame obligation is then `by decide` for a literal
name and `by simp [h]` for a bound one. -/
@[simp] theorem warrs_readLoop (a lim : String) : (readLoop a lim).warrs = [a] := by
  simp [readLoop, Com.warrs]

@[simp] theorem wvars_readLoop (a lim : String) :
    (readLoop a lim).wvars = ["i", "t", "i"] := by
  simp [readLoop, Com.wvars]

/-- The invariant of `readLoop`: `i` numbers have been moved from the
tape into the array, and what is left of the tape starts at `i`. Its
array half is the kit's fill, at the `i`-th number of the block. -/
def ReadInv (a lim : String) (k : ℕ) (ys rest : List ℕ) (τ : Env) : Prop :=
  τ.vars lim = k ∧ τ.inp = ys.drop (τ.vars "i") ++ rest ∧
  Fill.Below a "i" k (fun i => ys.getD i 0) τ

/-- Reading `k` numbers off the tape into the array `a`, at a cost of
`12` per number. The array must already have length `k`; the numbers
read are the first `k` of the tape. The loop counts up to `k` and moves
numbers it has just read, so it stays below the bound as soon as the
count and those numbers do. -/
theorem readLoop_run {B : ℕ} {a lim : String} (hi : lim ≠ "i") (ht : lim ≠ "t")
    {σ : Env} {g : ℕ → ℕ} {k : ℕ} {ys rest : List ℕ}
    (harr : σ.arrs a = arrOf k g) (hlim : σ.vars lim = k)
    (hys : ys.length = k) (hinp : σ.inp = ys ++ rest)
    (hkB : k < B) (hyB : ∀ v ∈ ys, v < B) :
    ∃ (σ' : Env) (g' : ℕ → ℕ), Run B (readLoop a lim) σ σ' (12 * k + 6) ∧
      σ'.arrs a = arrOf k g' ∧ (∀ i < k, g' i = ys.getD i 0) ∧ σ'.inp = rest := by
  have hbody : Spec B (fun τ => ReadInv a lim k ys rest τ ∧ τ.vars "i" < k)
      (.seq (.read "t") (Fill.put a "i" (.var "t")))
      (fun τ τ' => ReadInv a lim k ys rest τ' ∧ τ'.vars "i" = τ.vars "i" + 1) 8 := by
    rintro τ ⟨⟨hl, hinp', hbel⟩, hlt⟩
    have hylen : τ.vars "i" < ys.length := by omega
    have hhead : τ.inp = ys.getD (τ.vars "i") 0 :: (ys.drop (τ.vars "i" + 1) ++ rest) := by
      rw [hinp', List.drop_eq_getElem_cons hylen, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hylen]; rfl
    have hv : τ.inp.headD 0 = ys.getD (τ.vars "i") 0 := by rw [hhead]; rfl
    have hvB : τ.inp.headD 0 < B := by
      rw [hv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hylen]
      exact hyB _ (List.getElem_mem hylen)
    have hlen : τ.vars "i" < (τ.arrs a).length := by rw [hbel.length]; omega
    run_vcg
    · refine ⟨⟨by simp [hi, ht, hl], by simp [hhead], ?_⟩, by simp⟩
      exact (hbel.step hlt hv).of_eq (by simp) (by simp)
    · simpa using hvB
  obtain ⟨σ', hrun, ⟨-, hinp', hbel⟩, hik⟩ :=
    (Spec.forRangeZero "i" lim (ReadInv a lim k ys rest) k 8 hkB
      (fun _ h => h.2.2.le) (fun _ h => h.1) hbody).run (σ := σ)
      ⟨by simp [hi, hlim], by simp [hinp], Fill.below_zero (g := g) (by simp [harr]) (by simp)⟩
  obtain ⟨g', harr', hg'⟩ := hbel.done hik
  exact ⟨σ', g', hrun, harr', hg', by
    rw [hik] at hinp'; rw [hinp', List.drop_eq_nil_of_le (by omega)]; rfl⟩

/-! ### Clearing the label array -/

/-- Marking every vertex unvisited, at a cost of `11` per vertex. This
is the kit's array fill and nothing else: the cell function is the
constant marker `n`, which with a counter below it is all the phase
produces. -/
theorem initLab_run {B : ℕ} {σ : Env} {g : ℕ → ℕ} {n : ℕ}
    (harr : σ.arrs "lab" = arrOf n g) (hn : σ.vars "n" = n) (hnB : n < B) :
    ∃ (σ' : Env) (g' : ℕ → ℕ), Run B initLab σ σ' (11 * n + 6) ∧
      σ'.arrs "lab" = arrOf n g' ∧ (∀ i < n, g' i = n) := by
  obtain ⟨σ', hrun, ⟨g', harr', hg'⟩, -⟩ :=
    (Fill.loop_spec B n "lab" "i" "n" (.var "n") (fun _ => n) (by decide) hnB
      (fun _ _ hm _ => by rw [← hm]; exact evalB_var (by omega))).run ⟨⟨g, harr⟩, hn⟩
  exact ⟨σ', g', hrun, harr', hg'⟩

/-! ### Writing the labels out -/

/-- The invariant of `writeLoop`: the output tape has grown by the labels
below the counter. It is stated against the tape `o` the phase started
with rather than against a whole initial environment, so that nothing but
what the loop computes is carried around it. -/
def WriteInv (n : ℕ) (g : ℕ → ℕ) (o : List ℕ) (τ : Env) : Prop :=
  τ.vars "i" ≤ n ∧ τ.vars "n" = n ∧ τ.arrs "lab" = arrOf n g ∧
  τ.out = o ++ (List.range (τ.vars "i")).map g

/-- Writing the `n` labels to the output tape, at a cost of `11` per
vertex. What is written is what the array holds, so the bound on the
array is the bound the phase needs. -/
theorem writeLoop_run {B : ℕ} {σ : Env} {g : ℕ → ℕ} {n : ℕ}
    (harr : σ.arrs "lab" = arrOf n g) (hn : σ.vars "n" = n) (hnB : n < B)
    (hgB : ∀ i < n, g i < B) :
    ∃ σ', Run B writeLoop σ σ' (11 * n + 6) ∧
      σ'.out = σ.out ++ (List.range n).map g := by
  have hbody : Spec B (fun τ => WriteInv n g σ.out τ ∧ τ.vars "i" < n)
      (.seq (.write (.get "lab" (.var "i")))
        (.assign "i" (.add (.var "i") (.lit 1))))
      (fun τ τ' => WriteInv n g σ.out τ' ∧ τ'.vars "i" = τ.vars "i" + 1) 7 := by
    rintro τ ⟨⟨hle, hnn, hlab, hout⟩, hlt⟩
    have hcell : (τ.arrs "lab")[τ.vars "i"]?.getD 0 = g (τ.vars "i") := by
      rw [← List.getD_eq_getElem?_getD, hlab, getD_arrOf g hlt]
    have hlen : τ.vars "i" < (τ.arrs "lab").length := by rw [hlab, length_arrOf]; omega
    have hvB : (τ.arrs "lab")[τ.vars "i"]?.getD 0 < B := by rw [hcell]; exact hgB _ hlt
    have hvB' : (τ.arrs "lab").getD (τ.vars "i") 0 < B := by rwa [List.getD_eq_getElem?_getD]
    run_vcg
    exact ⟨⟨by simp; omega, by simp [hnn], by simp [hlab],
      by simp [hout, List.range_succ, hcell]⟩, by simp⟩
  obtain ⟨σ', hrun, ⟨-, -, -, hout⟩, hik⟩ :=
    (Spec.forRangeZero "i" "n" (WriteInv n g σ.out) n 7 hnB (fun _ h => h.1)
      (fun _ h => h.2.1) hbody).run (σ := σ)
      ⟨by simp, by simp [hn], by simp [harr], by simp⟩
  rw [hik] at hout
  exact ⟨σ', hrun, hout⟩

end Lax11Proofs.CC
