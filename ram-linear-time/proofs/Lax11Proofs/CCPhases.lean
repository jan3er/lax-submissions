import Lax11Proofs.CC
import Lax13Proofs.Spec

/-!
The three straight phases of the driver: reading the input word into an
array, clearing the label array, and writing the labels out. They are
proved here, away from the search, because they say nothing about graphs
— a read loop copies a prefix of the tape into an array whatever the
numbers mean — and because together they fix the shape every phase lemma
of this development has: what the phase does to *its* array, what it
costs, and under which bound it stays.

All three *are* the same loop, `i := 0; while i < m do …`, so all three
are one application of `countUp_run` below to a specification of their
body. No variant, no cost arithmetic and no reading of the failed
condition appears here; `Spec.forRange` owns them.

What a phase leaves alone is not stated either. Which names a command may
touch is syntactic, and `Lax13Proofs.Frame` decides it, so a caller
recovers a frame condition from the run the conclusion already carries at
the price of one `by decide`. `readLoop`'s input tape is the exception —
it is consumed, so what is left of it is a conclusion.

The value bound `B` costs each of the three one hypothesis and no
invariant clause: everything a phase produces is a counter below the
extent of its array, a number it just read, or a number already in the
array, so the bounds the caller supplies on those are all the bounded
semantics asks for.
-/

namespace Lax11Proofs.CC

open Lax13.Ram Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning

/-- Extending a pointwise array invariant by the cell just written: two
of the three loops below fill an array, and this is what one turn does
to "the cells under the counter hold what they should". -/
theorem below_succ {i v : ℕ} {f F : ℕ → ℕ} (hv : v = F i) (hf : ∀ j < i, f j = F j)
    (j : ℕ) (hj : j < i + 1) : (if j = i then v else f j) = F j := by
  by_cases hje : j = i
  · simp [hje, hv]
  · simp only [if_neg hje]; exact hf j (by omega)

/-- **The shape of all three phases**: zero the counter `i`, then run it
up to what the scalar `m` holds, one step per turn. `Spec.forRange`
covers the loop; what is added here is the initialisation and the four
bounds the rule asks of an invariant, which for a counter phase are
always the same two facts — the counter never passes `N`, and `m` holds
`N` throughout. A body costing `Kb` therefore costs the phase
`(Kb + 4) · N + 6`. -/
theorem countUp_run {B : ℕ} {c : Com} {N Kb : ℕ} (m : String) (σ : Env) (I : Env → Prop)
    (hxN : ∀ τ, I τ → τ.vars "i" ≤ N) (hm : ∀ τ, I τ → τ.vars m = N) (hNB : N < B)
    (hbody : Spec B (fun τ => I τ ∧ τ.vars "i" < N) c
      (fun τ τ' => I τ' ∧ τ'.vars "i" = τ.vars "i" + 1) Kb)
    (hI : I (σ.setVar "i" 0)) :
    ∃ σ', Run B (.seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var m)) c)) σ σ'
        ((Kb + 4) * N + 6) ∧ I σ' ∧ σ'.vars "i" = N := by
  obtain ⟨σ', hrun, hI', hik⟩ :=
    (Spec.forRange (K := (Kb + 4) * N + 4) (x := "i") (m := m) I N Kb
      (fun _ hτ => lt_of_le_of_lt (hxN _ hτ) hNB) (fun _ hτ => hm _ hτ ▸ hNB) hm hxN hbody
      (fun _ h => h) (fun _ _ => Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) 4)).run hI
  exact ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun).mono (by simp; omega), hI', hik⟩

/-! ### Reading a block of the tape into an array -/

/-- What `readLoop` may store into, and what it may assign to. Its limit
`lim` is not among the latter, which is why the caller may pass a scalar
it wants to keep; and with these two a frame obligation is `by decide`
for a literal name and `by simp [h]` for a bound one. -/
@[simp] theorem warrs_readLoop (a lim : String) : (readLoop a lim).warrs = [a] := by
  simp [readLoop, Com.warrs]

@[simp] theorem wvars_readLoop (a lim : String) :
    (readLoop a lim).wvars = ["i", "t", "i"] := by
  simp [readLoop, Com.wvars]

/-- The invariant of `readLoop`: `i` numbers have been moved from the
tape into the array. -/
def ReadInv (a lim : String) (k : ℕ) (ys rest : List ℕ) (τ : Env) : Prop :=
  τ.vars "i" ≤ k ∧ τ.vars lim = k ∧
  τ.inp = ys.drop (τ.vars "i") ++ rest ∧
  (∃ g, τ.arrs a = arrOf k g ∧ ∀ i < τ.vars "i", g i = ys.getD i 0)

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
      (.seq (.read "t") (.seq (.store a (.var "i") (.var "t"))
        (.assign "i" (.add (.var "i") (.lit 1)))))
      (fun τ τ' => ReadInv a lim k ys rest τ' ∧ τ'.vars "i" = τ.vars "i" + 1) 8 := by
    rintro τ ⟨⟨hle, hl, hinp', f, hf, hfv⟩, hlt⟩
    have hylen : τ.vars "i" < ys.length := by omega
    have hdrop : ys.drop (τ.vars "i") = ys[τ.vars "i"]! :: ys.drop (τ.vars "i" + 1) := by
      rw [List.getElem!_eq_getElem?_getD, List.drop_eq_getElem_cons (by omega)]
      simp [List.getElem?_eq_getElem hylen]
    have hvB : ys[τ.vars "i"]?.getD 0 < B := by
      rw [List.getElem?_eq_getElem hylen]
      exact hyB _ (List.getElem_mem hylen)
    exact ⟨_, (Run.seq (Run.read (by rw [hinp', hdrop]; rfl))
      (Run.seq (Run.store (idx := τ.vars "i") (v := ys[τ.vars "i"]!)
          (by simp; omega) (by simp; omega) (by simp [hf]; omega))
        (Run.assign (v := τ.vars "i" + 1) (by simp; omega)))).mono (by simp),
      ⟨by simp; omega, by simp [hi, ht, hl], by simp,
        fun j => if j = τ.vars "i" then ys[τ.vars "i"]! else f j,
        by simp [hf, set_arrOf],
        fun j hj => below_succ (by simp [List.getElem!_eq_getElem?_getD,
          List.getD_eq_getElem?_getD]) hfv j (by simpa using hj)⟩, by simp⟩
  obtain ⟨σ', hrun, ⟨-, -, hinp', g', hg', hgv⟩, hik⟩ :=
    countUp_run lim σ (ReadInv a lim k ys rest) (fun _ h => h.1) (fun _ h => h.2.1) hkB hbody
      ⟨by simp, by simp [hi, hlim], by simp [hinp], g, by simp [harr], by simp⟩
  rw [hik] at hinp' hgv
  exact ⟨σ', g', hrun, hg', hgv, by rw [hinp', List.drop_eq_nil_of_le (by omega)]; rfl⟩

/-! ### Clearing the label array -/

/-- The invariant of `initLab`: the cells below the counter hold the
marker. -/
def InitInv (n : ℕ) (τ : Env) : Prop :=
  τ.vars "i" ≤ n ∧ τ.vars "n" = n ∧
  (∃ g, τ.arrs "lab" = arrOf n g ∧ ∀ i < τ.vars "i", g i = n)

/-- Marking every vertex unvisited, at a cost of `11` per vertex. The
only number the phase produces is the marker `n` and a counter below
it. -/
theorem initLab_run {B : ℕ} {σ : Env} {g : ℕ → ℕ} {n : ℕ}
    (harr : σ.arrs "lab" = arrOf n g) (hn : σ.vars "n" = n) (hnB : n < B) :
    ∃ (σ' : Env) (g' : ℕ → ℕ), Run B initLab σ σ' (11 * n + 6) ∧
      σ'.arrs "lab" = arrOf n g' ∧ (∀ i < n, g' i = n) := by
  have hbody : Spec B (fun τ => InitInv n τ ∧ τ.vars "i" < n)
      (.seq (.store "lab" (.var "i") (.var "n"))
        (.assign "i" (.add (.var "i") (.lit 1))))
      (fun τ τ' => InitInv n τ' ∧ τ'.vars "i" = τ.vars "i" + 1) 7 := by
    rintro τ ⟨⟨hle, hnn, f, hf, hfv⟩, hlt⟩
    exact ⟨_, (Run.seq (Run.store (idx := τ.vars "i") (v := n)
          (by simp; omega) (by simp [hnn]; omega) (by simp [hf]; omega))
        (Run.assign (v := τ.vars "i" + 1) (by simp; omega))).mono (by simp),
      ⟨by simp; omega, by simp [hnn],
        fun j => if j = τ.vars "i" then n else f j, by simp [hf, set_arrOf],
        fun j hj => below_succ rfl hfv j (by simpa using hj)⟩, by simp⟩
  obtain ⟨σ', hrun, ⟨-, -, g', hg', hgv⟩, hik⟩ :=
    countUp_run "n" σ (InitInv n) (fun _ h => h.1) (fun _ h => h.2.1) hnB hbody
      ⟨by simp, by simp [hn], g, by simp [harr], by simp⟩
  rw [hik] at hgv
  exact ⟨σ', g', hrun, hg', hgv⟩

/-! ### Writing the labels out -/

/-- The invariant of `writeLoop`: the output tape has grown by the labels
below the counter. It is stated against the tape `o` the phase started
with rather than against a whole initial environment, so that — as for
the other two — nothing but what the loop computes is carried around
it. -/
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
    exact ⟨_, (Run.seq (Run.write (v := g (τ.vars "i"))
          (by simp [hlab, getElem?_arrOf _ hlt]; exact ⟨by omega, hgB _ hlt⟩))
        (Run.assign (v := τ.vars "i" + 1) (by simp; omega))).mono (by simp),
      ⟨by simp; omega, by simp [hnn], by simp [hlab], by simp [hout, List.range_succ]⟩, by simp⟩
  obtain ⟨σ', hrun, ⟨-, -, -, hout⟩, hik⟩ :=
    countUp_run "n" σ (WriteInv n g σ.out) (fun _ h => h.1) (fun _ h => h.2.1) hnB hbody
      ⟨by simp, by simp [hn], by simp [harr], by simp⟩
  rw [hik] at hout
  exact ⟨σ', hrun, hout⟩

end Lax11Proofs.CC
