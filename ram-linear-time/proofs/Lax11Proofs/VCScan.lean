import Lax11Proofs.VC

/-!
The scan lemma: one pass over the target array either finds an
uncovered edge or certifies that the marking touches every slot.

The loop is flat — each turn advances either the slot pointer `j` or
the block owner `u` — so its cost is not constant per slot and the
potential form of the loop rule is what bounds it: `50·(2m − j) +
50·(n − u)` pays for both kinds of turn at once, the same amortization
the components driver used for its search.

The conclusion is a dichotomy on the flag. Found means *an* uncovered
adjacent pair, not the least one — the invariant downstream never asks
which. Not found means every slot of every block has a marked endpoint,
which is exactly what `isVertexCover_of_slots` consumes. The owner is
correct because offsets are nondecreasing, so a slot has a unique
owner; that uniqueness is the only graph fact the loop itself needs.

The value bound costs the scan four hypotheses and no invariant
clause: everything it produces is a vertex number, a slot number, an
offset or a mark, and the caller's bounds on those are all the bounded
semantics asks for.
-/

namespace Lax11Proofs.VC

open Lax13.Ram Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax11Proofs.CC

variable {g : List ℕ} {n m B : ℕ} {G : SimpleGraph (Fin n)} {O T MK : ℕ → ℕ}

/-- The invariant of the scan loop: the owner's block has reached `j`,
and the flag dichotomy — nothing uncovered below `j`, or a recorded
uncovered pair. -/
def ScanInv (g : List ℕ) (n m : ℕ) (MK : ℕ → ℕ) (σ : Env) (τ : Env) : Prop :=
  τ.vars "m2" = 2 * m ∧ τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out ∧
  (∀ y, y ≠ "j" → y ≠ "u" → y ≠ "w" → y ≠ "found" → y ≠ "eu" → y ≠ "ev" →
    τ.vars y = σ.vars y) ∧
  τ.vars "u" ≤ n ∧ offset g (τ.vars "u") ≤ τ.vars "j" ∧ τ.vars "j" ≤ 2 * m ∧
  ((τ.vars "found" = 0 ∧
      ∀ o p, o < n → offset g o ≤ p → p < offset g (o + 1) → p < τ.vars "j" →
        MK o ≠ 0 ∨ MK (target g p) ≠ 0) ∨
   (τ.vars "found" = 1 ∧
      ∃ j₀, τ.vars "eu" < n ∧ offset g (τ.vars "eu") ≤ j₀ ∧
        j₀ < offset g (τ.vars "eu" + 1) ∧ target g j₀ = τ.vars "ev" ∧
        MK (τ.vars "eu") = 0 ∧ MK (τ.vars "ev") = 0))

/-- The potential of the scan: fifty per slot not yet passed, fifty per
owner not yet advanced past. -/
def ScanPot (m n : ℕ) (τ : Env) : ℕ :=
  50 * (2 * m - τ.vars "j") + 50 * (n - τ.vars "u")

/-- **The scan.** Started on represented arrays, `scan` terminates
within `100m + 50n + 10` steps having either recorded an uncovered
adjacent pair in `eu`, `ev` or certified the marking against every
slot. Everything but its six working scalars is untouched, and every
value it produces stays below `B`. -/
theorem scan_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ j < 2 * m, T j = target g j)
    (h1B : 1 < B) (hnB : n < B) (hmB : 2 * m < B) (hMKB : ∀ i < n, MK i < B)
    {σ : Env} (hm2 : σ.vars "m2" = 2 * m)
    (hoff : σ.arrs "off" = arrOf (n + 1) O) (htgt : σ.arrs "tgt" = arrOf (2 * m) T)
    (hmark : σ.arrs "mark" = arrOf n MK) :
    ∃ σ', Run B scan σ σ' (100 * m + 50 * n + 10) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
      (∀ y, y ≠ "j" → y ≠ "u" → y ≠ "w" → y ≠ "found" → y ≠ "eu" → y ≠ "ev" →
        σ'.vars y = σ.vars y) ∧
      ((σ'.vars "found" = 0 ∧
          ∀ o p, o < n → offset g o ≤ p → p < offset g (o + 1) →
            MK o ≠ 0 ∨ MK (target g p) ≠ 0) ∨
       (σ'.vars "found" = 1 ∧ σ'.vars "eu" < n ∧ σ'.vars "ev" < n ∧
          Adjn G (σ'.vars "eu") (σ'.vars "ev") ∧
          MK (σ'.vars "eu") = 0 ∧ MK (σ'.vars "ev") = 0)) := by
  -- the offsets and the targets are words, which is all the loop reads
  have hOB : ∀ i ≤ n, O i < B := by
    intro i hi
    have h1 := hO i hi
    have h2 := offset_le hg hi
    rw [hm] at h2
    omega
  have hTB : ∀ j < 2 * m, T j < B := by
    intro j hj
    have h1 := hT j hj
    have h2 : target g j < n := hg.target_lt _ (by rw [hm]; exact hj)
    omega
  have hstep : ∀ τ, ScanInv g n m MK σ τ →
      (Cond.lt (.var "j") (.var "m2")).evalB B τ = some true →
      ∃ τ' K, Run B scanBody τ τ' K ∧ ScanInv g n m MK σ τ' ∧
        1 + (Cond.lt (Expr.var "j") (Expr.var "m2")).size + K + ScanPot m n τ' ≤
          ScanPot m n τ := by
    rintro τ ⟨hm2', harrs, hinp', hout', hfr, hun, houj, hj2m, hdich⟩ hcond
    have hjlt : τ.vars "j" < 2 * m := by simp [hm2'] at hcond; omega
    have hult : τ.vars "u" < n := by
      rcases Nat.lt_or_ge (τ.vars "u") n with h | h
      · exact h
      · exfalso
        have hue : τ.vars "u" = n := by omega
        rw [hue, hg.offset_last, hm] at houj
        omega
    have hOu1 : O (τ.vars "u" + 1) = offset g (τ.vars "u" + 1) := hO _ (by omega)
    have hOu1B : O (τ.vars "u" + 1) < B := hOB _ (by omega)
    have hTjB : T (τ.vars "j") < B := hTB _ hjlt
    rcases Nat.lt_or_ge (τ.vars "j") (offset g (τ.vars "u" + 1)) with hslot | hadv
    · -- `j` is inside the owner's block: examine the slot
      have hc1 : (Cond.lt (.var "j")
          (.get "off" (.add (.var "u") (.lit 1)))).evalB B τ = some true := by
        simp [harrs, hoff, getElem?_arrOf O (show τ.vars "u" + 1 < n + 1 by omega),
          hOu1, hslot]
        omega
      have hwlt : target g (τ.vars "j") < n := by
        refine hg.target_lt _ ?_
        rw [hm]
        exact hjlt
      have hTj : T (τ.vars "j") = target g (τ.vars "j") := hT _ hjlt
      have r_w : Run B (.assign "w" (.get "tgt" (.var "j"))) τ
          (τ.setVar "w" (T (τ.vars "j"))) 3 :=
        (Run.assign (by
          simp [harrs, htgt, getElem?_arrOf T hjlt]; omega)).mono (by simp)
      by_cases hMKu : MK (τ.vars "u") = 0
      · have hc2 : (Cond.eq (.get "mark" (.var "u")) (.lit 0)).evalB B
            (τ.setVar "w" (T (τ.vars "j"))) = some true := by
          simp [harrs, hmark, getElem?_arrOf MK hult, hMKu]
          omega
        by_cases hMKw : MK (target g (τ.vars "j")) = 0
        · -- an uncovered edge: record it and force the exit
          set τ' : Env := ((((τ.setVar "w" (T (τ.vars "j"))).setVar "eu"
              (τ.vars "u")).setVar "ev" (T (τ.vars "j"))).setVar "found" 1).setVar
              "j" (2 * m) with hτ'
          have hc3 : (Cond.eq (.get "mark" (.var "w")) (.lit 0)).evalB B
              (τ.setVar "w" (T (τ.vars "j"))) = some true := by
            simp [harrs, hmark, hTj, getElem?_arrOf MK hwlt, hMKw]
            omega
          refine ⟨τ', _, Run.ite_true hc1 (Run.seq r_w (Run.ite_true hc2
            (Run.ite_true hc3 (Run.seq (Run.assign (v := τ.vars "u") (by simp; omega))
              (Run.seq (Run.assign (v := T (τ.vars "j")) (by simp; omega))
                (Run.seq (Run.assign (v := 1) (by simp; omega))
                  (Run.assign (v := 2 * m) (by simp [hm2']; omega)))))))), ?_, ?_⟩
          · refine ⟨by simp [hτ', hm2'], by simp [hτ', harrs], by simp [hτ', hinp'],
              by simp [hτ', hout'], ?_, by simp [hτ']; omega, ?_, by simp [hτ'], ?_⟩
            · intro y h1 h2 h3 h4 h5 h6
              simp [hτ', h1, h3, h4, h5, h6]
              exact hfr y h1 h2 h3 h4 h5 h6
            · have : offset g (τ.vars "u") ≤ 2 * m := by
                have := offset_le hg (show τ.vars "u" ≤ n by omega)
                rwa [hm] at this
              simpa [hτ'] using this
            · refine Or.inr ⟨by simp [hτ'], τ.vars "j", by simp [hτ', hult],
                by simpa [hτ'] using houj, by simpa [hτ'] using hslot,
                by simp [hτ', hTj], by simp [hτ', hMKu], ?_⟩
              simp [hτ', hTj]
              exact hMKw
          · simp only [ScanPot, hτ', vars_setVar, size_condLt, size_var]
            simp
            omega
        · -- the target is marked: the slot is covered, advance `j`
          set τ' : Env := (τ.setVar "w" (T (τ.vars "j"))).setVar "j"
              (τ.vars "j" + 1) with hτ'
          have hc3 : (Cond.eq (.get "mark" (.var "w")) (.lit 0)).evalB B
              (τ.setVar "w" (T (τ.vars "j"))) = some false := by
            simp [harrs, hmark, hTj, getElem?_arrOf MK hwlt]
            exact ⟨⟨by omega, hMKB _ hwlt⟩, by omega, hMKw⟩
          refine ⟨τ', _, Run.ite_true hc1 (Run.seq r_w (Run.ite_true hc2
            (Run.ite_false hc3 (Run.assign (v := τ.vars "j" + 1)
              (by simp; omega))))), ?_, ?_⟩
          · refine ⟨by simp [hτ', hm2'], by simp [hτ', harrs], by simp [hτ', hinp'],
              by simp [hτ', hout'], ?_, by simp [hτ']; omega,
              by simp [hτ']; omega, by simp [hτ']; omega, ?_⟩
            · intro y h1 h2 h3 h4 h5 h6
              simp [hτ', h1, h3]
              exact hfr y h1 h2 h3 h4 h5 h6
            · rcases hdich with ⟨hf0, hcov⟩ | ⟨hf1, hwit⟩
              · refine Or.inl ⟨by simp [hτ', hf0], ?_⟩
                intro o p ho h1 h2 h3
                simp [hτ'] at h3
                rcases Nat.lt_or_ge p (τ.vars "j") with hp | hp
                · exact hcov o p ho h1 h2 hp
                · have hpj : p = τ.vars "j" := by omega
                  subst hpj
                  have ho' : o = τ.vars "u" := by
                    rcases lt_trichotomy o (τ.vars "u") with hlt | heq | hgt
                    · exfalso
                      have := offset_mono' hg (show o + 1 ≤ τ.vars "u" by omega)
                        (show τ.vars "u" ≤ n by omega)
                      omega
                    · exact heq
                    · exfalso
                      have := offset_mono' hg (show τ.vars "u" + 1 ≤ o by omega)
                        (show o ≤ n by omega)
                      omega
                  subst ho'
                  exact Or.inr hMKw
              · exact Or.inr ⟨by simp [hτ', hf1], by simpa [hτ'] using hwit⟩
          · simp only [ScanPot, hτ', vars_setVar, size_condLt, size_var]
            simp
            omega
      · -- the owner is marked: the slot is covered, advance `j`
        set τ' : Env := (τ.setVar "w" (T (τ.vars "j"))).setVar "j"
            (τ.vars "j" + 1) with hτ'
        have hc2 : (Cond.eq (.get "mark" (.var "u")) (.lit 0)).evalB B
            (τ.setVar "w" (T (τ.vars "j"))) = some false := by
          simp [harrs, hmark, getElem?_arrOf MK hult]
          exact ⟨⟨by omega, hMKB _ hult⟩, by omega, hMKu⟩
        refine ⟨τ', _, Run.ite_true hc1 (Run.seq r_w (Run.ite_false hc2
          (Run.assign (v := τ.vars "j" + 1) (by simp; omega)))), ?_, ?_⟩
        · refine ⟨by simp [hτ', hm2'], by simp [hτ', harrs], by simp [hτ', hinp'],
            by simp [hτ', hout'], ?_, by simp [hτ']; omega,
            by simp [hτ']; omega, by simp [hτ']; omega, ?_⟩
          · intro y h1 h2 h3 h4 h5 h6
            simp [hτ', h1, h3]
            exact hfr y h1 h2 h3 h4 h5 h6
          · rcases hdich with ⟨hf0, hcov⟩ | ⟨hf1, hwit⟩
            · refine Or.inl ⟨by simp [hτ', hf0], ?_⟩
              intro o p ho h1 h2 h3
              simp [hτ'] at h3
              rcases Nat.lt_or_ge p (τ.vars "j") with hp | hp
              · exact hcov o p ho h1 h2 hp
              · have hpj : p = τ.vars "j" := by omega
                subst hpj
                have ho' : o = τ.vars "u" := by
                  rcases lt_trichotomy o (τ.vars "u") with hlt | heq | hgt
                  · exfalso
                    have := offset_mono' hg (show o + 1 ≤ τ.vars "u" by omega)
                      (show τ.vars "u" ≤ n by omega)
                    omega
                  · exact heq
                  · exfalso
                    have := offset_mono' hg (show τ.vars "u" + 1 ≤ o by omega)
                      (show o ≤ n by omega)
                    omega
                subst ho'
                exact Or.inl hMKu
            · exact Or.inr ⟨by simp [hτ', hf1], by simpa [hτ'] using hwit⟩
        · simp only [ScanPot, hτ', vars_setVar, size_condLt, size_var]
          simp
          omega
    · -- the owner's block is exhausted: advance the owner
      have hc1 : (Cond.lt (.var "j")
          (.get "off" (.add (.var "u") (.lit 1)))).evalB B τ = some false := by
        simp [harrs, hoff, getElem?_arrOf O (show τ.vars "u" + 1 < n + 1 by omega),
          hOu1]
        omega
      refine ⟨τ.setVar "u" (τ.vars "u" + 1), _,
        Run.ite_false hc1 (Run.assign (v := τ.vars "u" + 1) (by simp; omega)), ?_, ?_⟩
      · refine ⟨by simp [hm2'], by simp [harrs], by simp [hinp'], by simp [hout'],
          ?_, by simp; omega, by simpa using hadv, by simpa using hj2m, ?_⟩
        · intro y h1 h2 h3 h4 h5 h6
          simp [h2]
          exact hfr y h1 h2 h3 h4 h5 h6
        · rcases hdich with ⟨hf0, hcov⟩ | ⟨hf1, hwit⟩
          · exact Or.inl ⟨by simp [hf0], by simpa using hcov⟩
          · exact Or.inr ⟨by simp [hf1], by simpa using hwit⟩
      · simp only [ScanPot, vars_setVar, size_condLt, size_var]
        simp
        omega
  set σ₀ : Env := ((σ.setVar "j" 0).setVar "u" 0).setVar "found" 0 with hσ₀
  have hI₀ : ScanInv g n m MK σ σ₀ := by
    refine ⟨by simp [hσ₀, hm2], by simp [hσ₀], by simp [hσ₀], by simp [hσ₀], ?_,
      by simp [hσ₀], by simp [hσ₀, hg.offset_zero], by simp [hσ₀], ?_⟩
    · intro y h1 h2 h3 h4 h5 h6
      simp [hσ₀, h1, h2, h4]
    · exact Or.inl ⟨by simp [hσ₀], by intro o p _ _ _ h3; simp [hσ₀] at h3⟩
  obtain ⟨τ', K, hrun, ⟨hm2', harrs', hinp'', hout'', hfr', hun', houj', hj2m', hdich'⟩,
      hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := Cond.lt (.var "j") (.var "m2")) (c := scanBody)
      (ScanInv g n m MK σ) (ScanPot m n)
      (fun τ hτ => by
        obtain ⟨hm2', -, -, -, -, -, -, hj2m, -⟩ := hτ
        exact evalB_condLt_vars (by omega) (by omega)) hstep hI₀
  have hj' : τ'.vars "j" = 2 * m := by
    simp [hm2'] at hfalse
    omega
  have hKle : K ≤ 100 * m + 50 * n + 4 := by
    have hΦ₀ : ScanPot m n σ₀ = 100 * m + 50 * n := by
      simp [ScanPot, hσ₀]
      omega
    simp only [size_condLt, size_var] at hpay
    omega
  refine ⟨τ', ((Run.seq (Run.assign (v := 0) (by simp; omega))
    (Run.seq (Run.assign (v := 0) (by simp; omega))
      (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun))).mono (by simp; omega)),
    harrs', hinp'', hout'', hfr', ?_⟩
  · rcases hdich' with ⟨hf0, hcov⟩ | ⟨hf1, j₀, heu, h1, h2, h3, h4, h5⟩
    · refine Or.inl ⟨hf0, ?_⟩
      intro o p ho hp1 hp2
      refine hcov o p ho hp1 hp2 ?_
      have := offset_le hg (show o + 1 ≤ n by omega)
      rw [hm] at this
      omega
    · refine Or.inr ⟨hf1, heu, ?_, ?_, h4, h5⟩
      · rw [← h3]
        exact target_lt' hg heu h2
      · have := adjn_of_slot hg heu h1 h2
        rwa [h3] at this

end Lax11Proofs.VC
