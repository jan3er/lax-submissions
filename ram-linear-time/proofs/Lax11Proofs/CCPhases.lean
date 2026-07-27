import Lax11Proofs.CC

/-!
The three straight phases of the driver: reading the input word into an
array, clearing the label array, and writing the labels out.

Each is one loop and one application of `Run.while_count`. They are
proved here, away from the search, because they say nothing about
graphs — a read loop copies a prefix of the tape into an array whatever
the numbers mean — and because together they fix the shape every phase
lemma of this development has: what the phase does to *its* array, that
it leaves the other arrays and the untouched scalars alone, and what it
costs.

The frame conditions are the tedious part and there is no way around
them: IMP+ has no notion of a variable being local, so a lemma about a
loop has to say which names it may have changed. They are cheap to
state and cheap to use, which is what matters.
-/

namespace Lax11Proofs.CC

open Lax11.Ram Lax11Proofs.Imp Lax11Proofs.Compile Lax11Proofs.Reasoning

/-! ### Reading a block of the tape into an array -/

/-- The invariant of `readLoop`: `i` numbers have been moved from the
tape into the array, and nothing else has changed. -/
def ReadInv (a lim : String) (σ : Env) (k : ℕ) (ys rest : List ℕ) (τ : Env) : Prop :=
  τ.vars "i" ≤ k ∧ τ.vars lim = k ∧
  τ.inp = ys.drop (τ.vars "i") ++ rest ∧
  (∃ g, τ.arrs a = arrOf k g ∧ ∀ i < τ.vars "i", g i = ys.getD i 0) ∧
  (∀ b, b ≠ a → τ.arrs b = σ.arrs b) ∧ τ.out = σ.out ∧
  (∀ y, y ≠ "i" → y ≠ "t" → τ.vars y = σ.vars y)

/-- Reading `k` numbers off the tape into the array `a`, at a cost of
`12` per number. The array must already have length `k`; the numbers
read are the first `k` of the tape. -/
theorem readLoop_run {a lim : String} (hi : lim ≠ "i") (ht : lim ≠ "t")
    {σ : Env} {g : ℕ → ℕ} {k : ℕ} {ys rest : List ℕ}
    (harr : σ.arrs a = arrOf k g) (hlim : σ.vars lim = k)
    (hys : ys.length = k) (hinp : σ.inp = ys ++ rest) :
    ∃ (σ' : Env) (g' : ℕ → ℕ), Run (readLoop a lim) σ σ' (12 * k + 6) ∧
      σ'.arrs a = arrOf k g' ∧ (∀ i < k, g' i = ys.getD i 0) ∧
      (∀ b, b ≠ a → σ'.arrs b = σ.arrs b) ∧ σ'.inp = rest ∧ σ'.out = σ.out ∧
      (∀ y, y ≠ "i" → y ≠ "t" → σ'.vars y = σ.vars y) := by
  have hstep : ∀ τ : Env, ReadInv a lim σ k ys rest τ →
      (Cond.lt (.var "i") (.var lim)).eval τ = some true →
      ∃ τ', Run (.seq (.read "t")
        (.seq (.store a (.var "i") (.var "t"))
          (.assign "i" (.add (.var "i") (.lit 1))))) τ τ' 8 ∧
        ReadInv a lim σ k ys rest τ' ∧ (k - τ'.vars "i") < (k - τ.vars "i") := by
    rintro τ ⟨hle, hl, hinp', ⟨f, hf, hfv⟩, hb, hout, hy⟩ hcond
    have hlt : τ.vars "i" < k := by simp [hl] at hcond; omega
    have hdrop : ys.drop (τ.vars "i") = ys[τ.vars "i"]! :: ys.drop (τ.vars "i" + 1) := by
      rw [List.getElem!_eq_getElem?_getD]
      rw [List.drop_eq_getElem_cons (by omega)]
      simp [List.getElem?_eq_getElem (show τ.vars "i" < ys.length by omega)]
    refine ⟨_, (Run.seq (Run.read (by rw [hinp', hdrop]; rfl))
      (Run.seq (Run.store (idx := τ.vars "i") (v := ys[τ.vars "i"]!)
          (by simp) (by simp) (by simp [hf]; omega))
        (Run.assign (v := τ.vars "i" + 1) (by simp)))).mono (by simp),
      ⟨by simp; omega, by simp [hi, ht, hl], by simp, ?_, ?_, by simp [hout], ?_⟩, by simp; omega⟩
    · refine ⟨fun j => if j = τ.vars "i" then ys[τ.vars "i"]! else f j, by simp [hf, set_arrOf], ?_⟩
      intro j hj
      simp at hj
      by_cases hje : j = τ.vars "i"
      · subst hje
        simp [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      · simp only [if_neg hje]
        exact hfv j (by omega)
    · intro b hbne
      simp [hbne, hb b hbne]
    · intro y hy1 hy2
      simp [hy1, hy2, hy y hy1 hy2]
  obtain ⟨σ', hrun, ⟨hle', hl', hinp'', ⟨g', hg', hgv⟩, hb', hout', hy'⟩, hfalse⟩ :=
    Run.while_count (b := Cond.lt (.var "i") (.var lim))
      (ReadInv a lim σ k ys rest) (fun τ => k - τ.vars "i") 8
      (fun τ _ => ⟨_, rfl⟩) hstep
      (σ := σ.setVar "i" 0)
      ⟨by simp, by simp [hi, hlim], by simp [hinp], ⟨g, by simp [harr], by simp⟩,
        by simp, by simp, by intro y hy1 _; simp [hy1]⟩
  have hik : σ'.vars "i" = k := by simp [hl'] at hfalse; omega
  rw [hik] at hinp'' hgv
  refine ⟨σ', g', (Run.seq (Run.assign (v := 0) rfl) hrun).mono (by simp; omega),
    hg', hgv, fun b hbne => by simp [hb' b hbne], ?_, by simp [hout'], ?_⟩
  · rw [hinp'', List.drop_eq_nil_of_le (by omega)]; rfl
  · intro y hy1 hy2; simp [hy' y hy1 hy2]

/-! ### Clearing the label array -/

/-- The invariant of `initLab`. -/
def InitInv (σ : Env) (n : ℕ) (τ : Env) : Prop :=
  τ.vars "i" ≤ n ∧ τ.vars "n" = n ∧
  (∃ g, τ.arrs "lab" = arrOf n g ∧ ∀ i < τ.vars "i", g i = n) ∧
  (∀ b, b ≠ "lab" → τ.arrs b = σ.arrs b) ∧ τ.out = σ.out ∧ τ.inp = σ.inp ∧
  (∀ y, y ≠ "i" → τ.vars y = σ.vars y)

/-- Marking every vertex unvisited, at a cost of `11` per vertex. -/
theorem initLab_run {σ : Env} {g : ℕ → ℕ} {n : ℕ}
    (harr : σ.arrs "lab" = arrOf n g) (hn : σ.vars "n" = n) :
    ∃ (σ' : Env) (g' : ℕ → ℕ), Run initLab σ σ' (11 * n + 6) ∧
      σ'.arrs "lab" = arrOf n g' ∧ (∀ i < n, g' i = n) ∧
      (∀ b, b ≠ "lab" → σ'.arrs b = σ.arrs b) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
      (∀ y, y ≠ "i" → σ'.vars y = σ.vars y) := by
  have hstep : ∀ τ : Env, InitInv σ n τ →
      (Cond.lt (.var "i") (.var "n")).eval τ = some true →
      ∃ τ', Run (.seq (.store "lab" (.var "i") (.var "n"))
        (.assign "i" (.add (.var "i") (.lit 1)))) τ τ' 7 ∧
        InitInv σ n τ' ∧ (n - τ'.vars "i") < (n - τ.vars "i") := by
    rintro τ ⟨hle, hnn, ⟨f, hf, hfv⟩, hb, hout, hinp, hy⟩ hcond
    have hlt : τ.vars "i" < n := by simp [hnn] at hcond; omega
    refine ⟨_, (Run.seq (Run.store (idx := τ.vars "i") (v := n)
          (by simp) (by simp [hnn]) (by simp [hf]; omega))
        (Run.assign (v := τ.vars "i" + 1) (by simp))).mono (by simp),
      ⟨by simp; omega, by simp [hnn], ?_, ?_, by simp [hout], by simp [hinp], ?_⟩, by simp; omega⟩
    · refine ⟨fun j => if j = τ.vars "i" then n else f j, by simp [hf, set_arrOf], ?_⟩
      intro j hj
      simp at hj
      by_cases hje : j = τ.vars "i"
      · simp [hje]
      · simp only [if_neg hje]; exact hfv j (by omega)
    · intro b hbne; simp [hbne, hb b hbne]
    · intro y hy1; simp [hy1, hy y hy1]
  obtain ⟨σ', hrun, ⟨hle', hnn', ⟨g', hg', hgv⟩, hb', hout', hinp', hy'⟩, hfalse⟩ :=
    Run.while_count (b := Cond.lt (.var "i") (.var "n"))
      (InitInv σ n) (fun τ => n - τ.vars "i") 7
      (fun τ _ => ⟨_, rfl⟩) hstep
      (σ := σ.setVar "i" 0)
      ⟨by simp, by simp [hn], ⟨g, by simp [harr], by simp⟩, by simp, by simp, by simp,
        by intro y hy1; simp [hy1]⟩
  have hik : σ'.vars "i" = n := by simp [hnn'] at hfalse; omega
  rw [hik] at hgv
  exact ⟨σ', g', (Run.seq (Run.assign (v := 0) rfl) hrun).mono (by simp; omega),
    hg', hgv, fun b hbne => by simp [hb' b hbne], by simp [hinp'], by simp [hout'],
    fun y hy1 => by simp [hy' y hy1]⟩

/-! ### Writing the labels out -/

/-- The invariant of `writeLoop`. -/
def WriteInv (σ : Env) (n : ℕ) (g : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "i" ≤ n ∧ τ.vars "n" = n ∧ τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧
  τ.out = σ.out ++ (List.range (τ.vars "i")).map g ∧
  (∀ y, y ≠ "i" → τ.vars y = σ.vars y)

/-- Writing the `n` labels to the output tape, at a cost of `11` per
vertex. -/
theorem writeLoop_run {σ : Env} {g : ℕ → ℕ} {n : ℕ}
    (harr : σ.arrs "lab" = arrOf n g) (hn : σ.vars "n" = n) :
    ∃ σ', Run writeLoop σ σ' (11 * n + 6) ∧
      σ'.out = σ.out ++ (List.range n).map g := by
  have hstep : ∀ τ : Env, WriteInv σ n g τ →
      (Cond.lt (.var "i") (.var "n")).eval τ = some true →
      ∃ τ', Run (.seq (.write (.get "lab" (.var "i")))
        (.assign "i" (.add (.var "i") (.lit 1)))) τ τ' 7 ∧
        WriteInv σ n g τ' ∧ (n - τ'.vars "i") < (n - τ.vars "i") := by
    rintro τ ⟨hle, hnn, ha, hinp, hout, hy⟩ hcond
    have hlt : τ.vars "i" < n := by simp [hnn] at hcond; omega
    refine ⟨_, (Run.seq (Run.write (v := g (τ.vars "i"))
          (by simp [ha, harr, getElem?_arrOf _ hlt]))
        (Run.assign (v := τ.vars "i" + 1) (by simp))).mono (by simp),
      ⟨by simp; omega, by simp [hnn], by simp [ha], by simp [hinp], ?_, ?_⟩, by simp; omega⟩
    · simp [hout, List.range_succ]
    · intro y hy1; simp [hy1, hy y hy1]
  obtain ⟨σ', hrun, ⟨hle', hnn', ha', hinp', hout', hy'⟩, hfalse⟩ :=
    Run.while_count (b := Cond.lt (.var "i") (.var "n"))
      (WriteInv σ n g) (fun τ => n - τ.vars "i") 7
      (fun τ _ => ⟨_, rfl⟩) hstep
      (σ := σ.setVar "i" 0)
      ⟨by simp, by simp [hn], by simp, by simp, by simp, by intro y hy1; simp [hy1]⟩
  have hik : σ'.vars "i" = n := by simp [hnn'] at hfalse; omega
  rw [hik] at hout'
  exact ⟨σ', (Run.seq (Run.assign (v := 0) rfl) hrun).mono (by simp; omega), hout'⟩

end Lax11Proofs.CC
