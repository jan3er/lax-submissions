import Lax15Proofs.Phases

/-!
The body of the outer loop, run.

One turn of the search is a dispatch on the mode, and under it the eight
transitions of `Config.lean`. The descend body runs the scan of
`Phases.lean` and then answers, gives up on the branch, or pushes a
frame; the backtrack body answers, flips the top frame to its second
branch — which is where the row scan runs — or pops it, which is where
the unwind loop runs.

Every case has the same four obligations and meets them the same way.
The `Run` is built by hand out of the rules of the kit and the loop
lemma of the phase it contains. The representation is reassembled: the
scalars that moved are read off the new configuration, and the arrays
that moved — `mark`, `trail`, the four stacks — are given explicitly,
in the bottom-up order the stack arrays are stored in and the
bottom-first order the trail is. The invariant and the potential drop
come from exactly one `step_*` lemma, applied to semantic facts: never
to a condition on slots, always to `Ok`, `resDeg` and `ResEdges`
statements that the scan's verdict and the transport lemmas of
`Residual.lean` have already produced. And the cost is bounded by one
loose numeral times `n + 2m + 1`, which is the shape the assembly wants.

The value bound is four hypotheses. Beyond the encoding's `n` and `2m`,
the run holds budgets (at most `k`), stack and trail heights (at most
`n`, and `n + 1` is written once), and modes; so `2 < B`, `n + 1 < B`,
`2m < B` and `k + 1 < B` is the whole of it, and the `fib (k + 2)` of
the running time is nowhere among the numbers held.
-/

namespace Lax15Proofs.VC

open Lax13.Ram Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax11Proofs.CC

variable {g : List ℕ} {n m k B : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}

/-! ### Reading the stack arrays

The stack arrays are bottom-up and the pure stack is top-first, so the
top frame sits at index `fs.length` and a push leaves every lower index
alone. -/

/-- The top frame, at the top index of the bottom-up order. -/
theorem getElem_reverse_top (f : Frame n) (fs : List (Frame n)) :
    (f :: fs).reverse[fs.length]'(by simp) = f := by
  simp

/-- A lower frame, past a push, in the bottom-up order. -/
theorem getElem_reverse_lt (f : Frame n) {fs : List (Frame n)} {i : ℕ}
    (hi : i < fs.length) :
    (f :: fs).reverse[i]'(by simp; omega) = fs.reverse[i]'(by simpa using hi) := by
  simp only [List.reverse_cons]
  rw [List.getElem_append_left (by simpa using hi)]

/-! ### Transporting the representation -/

/-- A transition that leaves the stack alone transports the
representation: the arrays and the two heights are untouched, and the
mode, budget and answer are read off the new configuration. This is the
whole of `Rep` for the four leaf transitions. -/
theorem Rep.of_frames_eq {C : Config n} {τ τ' : Env} {mode bud ans : ℕ}
    (h : Rep n m O T C τ) (harrs : τ'.arrs = τ.arrs)
    (hm2 : τ'.vars "m2" = τ.vars "m2") (htop : τ'.vars "top" = τ.vars "top")
    (htt : τ'.vars "tt" = τ.vars "tt") (hmode : τ'.vars "mode" = mode)
    (hbud : τ'.vars "bud" = bud) (hans : τ'.vars "ans" = ans) :
    Rep n m O T ⟨C.frames, mode, bud, ans⟩ τ' := by
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, h9, h10, h11⟩ := h
  exact ⟨by rw [hm2, h1], by rw [harrs, h2], by rw [harrs, h3], hmode, hbud, hans,
    by rw [htop]; exact h7, by rw [htt]; exact h8, by rw [harrs]; exact h9,
    by rw [harrs]; exact h10, by rw [harrs]; exact h11⟩

/-- The residual owners are vertices, so the scan's count is one of the
numbers the machine may hold. -/
theorem card_resOwners_le {M : Finset (Fin n)} {J : ℕ} :
    (ResOwners g M J).card ≤ n := by
  simpa using Finset.card_le_univ (ResOwners g M J)

/-! ### The descend body

The scan runs, and then one of four things happens. If it found no
vertex to branch on, the residual graph is a matching, its count is
exact, and the count against the budget decides the answer — yes at the
leaf, or a dead branch. If it found one, the budget decides whether the
branch is taken or the marking is already stuck. -/

/-- **Descend.** From a represented state in mode `0`, the descend body
reaches a represented state whose configuration still satisfies the
invariant and whose potential has dropped. -/
theorem descendBody_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ p < 2 * m, T p = target g p)
    (h2B : 2 < B) (hnB : n + 1 < B) (hmB : 2 * m < B) (hkB : k + 1 < B)
    {C : Config n} {τ : Env} (hRep : Rep n m O T C τ) (hJ : J G k C)
    (hmode : C.mode = 0) :
    ∃ (C' : Config n) (τ' : Env) (K : ℕ), Run B descendBody τ τ' K ∧
      Rep n m O T C' τ' ∧ J G k C' ∧ pot C' + 1 ≤ pot C ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out ∧ K ≤ 500 * (n + 2 * m + 1) := by
  obtain ⟨σ, K₀, hrun₀, hRep₀, harrs₀, hinp₀, hout₀, hro, hverdict, hK₀⟩ :=
    descendScan_run hg hm hO hT (by omega) (by omega) hmB hRep
  have hbudk : C.bud + (trail C.frames).length = k := hJ.2.2.1 hmode
  have hbud : σ.vars "bud" = C.bud := hRep₀.bud
  have hans : σ.vars "ans" = C.ans := hRep₀.ans
  have htop : σ.vars "top" = C.frames.length := hRep₀.top
  have htt : σ.vars "tt" = (trail C.frames).length := hRep₀.tt
  have hfrn : C.frames.length ≤ n := hJ.frames_length_le
  have httn : (trail C.frames).length ≤ n := hJ.trail_length_le
  rcases hverdict with ⟨hf0, hthin⟩ | ⟨hf1, v, hvval, hvM, hvd⟩
  · -- **No branching vertex.** The residual graph is a matching, so the
    -- capped count is the number of residual edges exactly.
    have hdeg := (thinBlocks_iff hg).1 hthin
    have hroE : σ.vars "ro" = (ResEdges G (marked C.frames)).card := by
      rw [hro]
      exact le_antisymm (card_resOwners_le_card_resEdges hg)
        (card_resEdges_le_card_resOwners hg hdeg)
    have hroB : σ.vars "ro" < B := by
      have := card_resOwners_le (g := g) (M := marked C.frames) (J := 2 * edgeCount g)
      omega
    by_cases hle : σ.vars "ro" ≤ C.bud
    · -- **T1, the matching yes.**
      obtain ⟨hJ', hpot'⟩ := step_yes hJ hmode (ok_of_card_resEdges_le (b := C.bud)
        (by omega))
      refine ⟨⟨C.frames, 2, C.bud, 1⟩, (σ.setVar "ans" 1).setVar "mode" 2,
        500 * (n + 2 * m + 1), ?_,
        hRep₀.of_frames_eq (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp [hbud]) (by simp),
        hJ', hpot', by simp [hinp₀], by simp [hout₀], le_rfl⟩
      refine (Run.seq hrun₀ (Run.ite_true (by simp [hf0]; omega)
        (Run.ite_true (by simp [hbud]; omega)
          (Run.seq (Run.assign (v := 1) (by simp; omega))
            (Run.assign (v := 2) (by simp; omega)))))).mono ?_
      simp only [size_condEq, size_condLt, size_var, size_lit, size_add]
      omega
    · -- **T2, the matching no.**
      obtain ⟨hJ', hpot'⟩ := step_no hJ hmode hdeg (by omega)
      refine ⟨⟨C.frames, 1, C.bud, C.ans⟩, σ.setVar "mode" 1, 500 * (n + 2 * m + 1), ?_,
        hRep₀.of_frames_eq (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp [hbud]) (by simp [hans]),
        hJ', hpot', by simp [hinp₀], by simp [hout₀], le_rfl⟩
      refine (Run.seq hrun₀ (Run.ite_true (by simp [hf0]; omega)
        (Run.ite_false (by simp [hbud]; omega)
          (Run.assign (v := 1) (by simp; omega))))).mono ?_
      simp only [size_condEq, size_condLt, size_var, size_lit, size_add]
      omega
  · -- **A branching vertex.** It has two residual neighbours.
    have hvB : (v : ℕ) < n := v.2
    by_cases hb0 : C.bud = 0
    · -- **T3, the budget no.** A residual neighbour of `v` is an
      -- uncovered edge, and there is nothing left to buy it with.
      obtain ⟨w, hw⟩ : (ResNbhd G (marked C.frames) v).Nonempty :=
        Finset.card_pos.1 (by rw [← resDeg_eq_card]; omega)
      obtain ⟨hadj, hwM⟩ := mem_resNbhd.1 hw
      obtain ⟨hJ', hpot'⟩ := step_stuck hJ hmode hb0 hadj hvM hwM
      refine ⟨⟨C.frames, 1, C.bud, C.ans⟩, σ.setVar "mode" 1, 500 * (n + 2 * m + 1), ?_,
        hRep₀.of_frames_eq (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp [hbud]) (by simp [hans]),
        hJ', hpot', by simp [hinp₀], by simp [hout₀], le_rfl⟩
      refine (Run.seq hrun₀ (Run.ite_false (by simp [hf1]; omega)
        (Run.ite_true (by simp [hbud, hb0]; omega)
          (Run.assign (v := 1) (by simp; omega))))).mono ?_
      simp only [size_condEq, size_var, size_lit]
      omega
    · -- **T4, the push.** The branch that takes `v` becomes the active
      -- one; the branch that takes its residual neighbourhood is stored
      -- in the new frame.
      obtain ⟨MK, hmark, hMK⟩ := hRep₀.mark
      obtain ⟨TR, htrail, hTR⟩ := hRep₀.trail
      obtain ⟨SV, SB, ST, SP, hstkV, hstkB, hstkT, hstkP, hstk⟩ := hRep₀.stk
      obtain ⟨hJ', hpot'⟩ := step_push hJ hmode (by omega) hvM hvd
      set L := C.frames.length with hL
      set TT := (trail C.frames).length with hTT
      set V := (v : ℕ) with hV
      have hvσ : σ.vars "v" = V := hvval.symm
      refine ⟨⟨⟨v, C.bud, false, [v]⟩ :: C.frames, 0, C.bud - 1, C.ans⟩,
        ((((((((σ.setArr "stkV" L V).setArr "stkB" L C.bud).setArr "stkT" L TT).setArr
          "stkP" L 0).setVar "top" (L + 1)).setArr "mark" V 1).setArr "trail" TT
          V).setVar "tt" (TT + 1)).setVar "bud" (C.bud - 1),
        500 * (n + 2 * m + 1), ?_, ?_, hJ', hpot', by simp [hinp₀], by simp [hout₀],
        le_rfl⟩
      · refine (Run.seq hrun₀ (Run.ite_false (by simp [hf1]; omega)
          (Run.ite_false (by simp [hbud, hb0]; omega)
            (Run.seq (Run.store (idx := L) (v := V) (by simp [htop]; omega)
                (by simp [hvσ]; omega) (by simpa [hstkV] using (show L < n + 1 by omega)))
              (Run.seq (Run.store (idx := L) (v := C.bud) (by simp [htop]; omega)
                  (by simp [hbud]; omega)
                  (by simpa [hstkB] using (show L < n + 1 by omega)))
                (Run.seq (Run.store (idx := L) (v := TT) (by simp [htop]; omega)
                    (by simp [htt]; omega)
                    (by simpa [hstkT] using (show L < n + 1 by omega)))
                  (Run.seq (Run.store (idx := L) (v := 0) (by simp [htop]; omega)
                      (by simp; omega)
                      (by simpa [hstkP] using (show L < n + 1 by omega)))
                    (Run.seq (Run.assign (v := L + 1) (by simp [htop]; omega))
                      (Run.seq (Run.store (idx := V) (v := 1) (by simp [hvσ]; omega)
                          (by simp; omega) (by simpa [hmark] using hvB))
                        (Run.seq (Run.store (idx := TT) (v := V)
                            (by simp [htt]; omega) (by simp [hvσ]; omega)
                            (by simpa [htrail] using (show TT < n + 1 by omega)))
                          (Run.seq (Run.assign (v := TT + 1) (by simp [htt]; omega))
                            (Run.assign (v := C.bud - 1)
                              (by simp [hbud]; omega))))))))))))).mono ?_
        simp only [size_condEq, size_var, size_lit, size_add, size_sub]
        omega
      · refine ⟨by simp [hRep₀.m2], by simp [hRep₀.off], by simp [hRep₀.tgt],
          by simp [hRep₀.mode, hmode], by simp, by simp [hans], by simp [hL],
          by simp; omega,
          ⟨fun w => if w = V then 1 else MK w, by simp [hmark, set_arrOf], ?_⟩,
          ⟨fun i => if i = TT then V else TR i, by simp [htrail, set_arrOf], ?_⟩,
          fun i => if i = L then V else SV i, fun i => if i = L then C.bud else SB i,
          fun i => if i = L then TT else ST i, fun i => if i = L then 0 else SP i,
          by simp [hstkV, set_arrOf], by simp [hstkB, set_arrOf],
          by simp [hstkT, set_arrOf], by simp [hstkP, set_arrOf], ?_⟩
        · have h := indicator_set_one (M := marked C.frames) hMK hvB
          simpa [marked_cons, toFinset_singleton_union] using h
        · intro i hi
          have hlenv : (trailVals C.frames).length = TT := length_trailVals _
          simp only [trail_cons, List.length_append, List.length_cons,
            List.length_nil] at hi
          simp only [trailVals_cons, List.map_cons, List.map_nil]
          by_cases hiTT : i = TT
          · subst hiTT
            rw [if_pos rfl, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (by omega)]
            simp [hlenv, hV]
          · have hilt : i < TT := by omega
            rw [if_neg hiTT, hTR i hilt, List.getD_eq_getElem?_getD,
              List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
        · intro i hi
          simp only [List.length_cons] at hi
          rcases Nat.lt_or_ge i L with hlt | hge
          · obtain ⟨h1, h2, h3, h4⟩ := hstk i hlt
            refine ⟨?_, ?_, ?_, ?_⟩ <;>
              simp only [if_neg (show ¬ i = L by omega), getElem_reverse_lt _ hlt,
                base_cons (le_of_lt hlt)]
            exacts [h1, h2, h3, h4]
          · have hiL : i = L := by omega
            subst hiL
            refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hL, hTT, hV]

/-! ### The backtrack body

The stack decides. An empty one is the end of the search; otherwise the
top frame is read out and either flipped to its second branch — the row
scan marks the whole residual neighbourhood, and the comparison against
the frame's own budget says whether that branch is worth descending
into — or popped, the unwind loop taking its marks back off. -/

/-- **Backtrack.** From a represented state in mode `1`, the backtrack
body reaches a represented state whose configuration still satisfies the
invariant and whose potential has dropped. -/
theorem backtrackBody_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ p < 2 * m, T p = target g p)
    (h2B : 2 < B) (hnB : n + 1 < B) (hmB : 2 * m < B) (hkB : k + 1 < B)
    {C : Config n} {τ : Env} (hRep : Rep n m O T C τ) (hJ : J G k C)
    (hmode : C.mode = 1) :
    ∃ (C' : Config n) (τ' : Env) (K : ℕ), Run B backtrackBody τ τ' K ∧
      Rep n m O T C' τ' ∧ J G k C' ∧ pot C' + 1 ≤ pot C ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out ∧ K ≤ 500 * (n + 2 * m + 1) := by
  obtain ⟨MK, hmark, hMK⟩ := hRep.mark
  obtain ⟨TR, htrail, hTR⟩ := hRep.trail
  obtain ⟨SVa, SBa, STa, SPa, hstkV, hstkB, hstkT, hstkP, hstk⟩ := hRep.stk
  have hm2 := hRep.m2
  have hoff := hRep.off
  have htgt := hRep.tgt
  have hmd := hRep.mode
  have hbudC := hRep.bud
  have hans := hRep.ans
  have htop := hRep.top
  have htt := hRep.tt
  have hheal := hJ.healthy
  have hfrn : C.frames.length ≤ n := hJ.frames_length_le
  rcases hfrs : C.frames with _ | ⟨f, fs⟩
  · -- **T5, the exhaustion.** No frame is left, so no alternative is.
    rw [hfrs] at htop
    obtain ⟨hJ', hpot'⟩ := step_exhausted hJ hmode hfrs
    refine ⟨⟨C.frames, 2, C.bud, 0⟩, (τ.setVar "ans" 0).setVar "mode" 2,
      500 * (n + 2 * m + 1), ?_,
      hRep.of_frames_eq (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp [hbudC]) (by simp), hJ', hpot', by simp, by simp, le_rfl⟩
    refine (Run.ite_true (by simp [htop]; omega)
      (Run.seq (Run.assign (v := 0) (by simp; omega))
        (Run.assign (v := 2) (by simp; omega)))).mono ?_
    simp only [size_condEq, size_var, size_lit]
    omega
  · rw [hfrs] at hMK hTR hstk htop htt hheal hfrn
    have hvnot : f.v ∉ marked fs := hheal.1
    have hnd0 : f.S.Nodup := hheal.2.2.1
    have hbk : f.b + (trail fs).length = k := hheal.2.2.2.1
    have hhfs : Healthy G k fs := hheal.tail
    have hvn : ((f.v : ℕ)) < n := f.v.2
    have hbn : f.b ≤ k := by omega
    have htbn : (trail fs).length ≤ n := hhfs.trail_length_le
    have hfsn : fs.length + 1 ≤ n := by simpa using hfrn
    have hcard : (marked fs).card = (trail fs).length := hhfs.card_marked
    obtain ⟨hSV, hSB, hST, hSP⟩ := hstk fs.length (by simp)
    rw [getElem_reverse_top] at hSV hSB hSP
    rw [base_top] at hST
    have htop' : τ.vars "top" = fs.length + 1 := by simpa using htop
    have htt' : τ.vars "tt" = (trail fs).length + f.S.length := by
      rw [htt]; simp only [trail_cons, List.length_append]; omega
    have htrn : (trail fs).length + f.S.length ≤ n := by
      have := hheal.trail_length_le
      simp only [trail_cons, List.length_append] at this; omega
    -- the top frame, read out of the stack arrays
    set σ₁ : Env := τ.setVar "sp" fs.length with hσ₁
    set σ₂ : Env := σ₁.setVar "pv" ((f.v : ℕ)) with hσ₂
    set σ₃ : Env := σ₂.setVar "pb" f.b with hσ₃
    set σ₄ : Env := σ₃.setVar "tb" ((trail fs).length) with hσ₄
    have harrs₄ : ∀ a, σ₄.arrs a = τ.arrs a := by
      intro a; simp only [hσ₄, hσ₃, hσ₂, hσ₁, arrs_setVar]
    have hv₄ : ∀ y, y ≠ "sp" → y ≠ "pv" → y ≠ "pb" → y ≠ "tb" → σ₄.vars y = τ.vars y := by
      intro y h1 h2 h3 h4
      simp only [hσ₄, hσ₃, hσ₂, hσ₁, vars_setVar, if_neg h1, if_neg h2, if_neg h3,
        if_neg h4]
    have hsp₄ : σ₄.vars "sp" = fs.length := by simp [hσ₄, hσ₃, hσ₂, hσ₁]
    have hpv₄ : σ₄.vars "pv" = (f.v : ℕ) := by simp [hσ₄, hσ₃, hσ₂]
    have hpb₄ : σ₄.vars "pb" = f.b := by simp [hσ₄, hσ₃]
    have htb₄ : σ₄.vars "tb" = (trail fs).length := by simp [hσ₄]
    have r₁ : Run B (.assign "sp" (.sub (.var "top") (.lit 1))) τ σ₁ 4 :=
      (Run.assign (v := fs.length) (by simp [htop']; omega)).mono (by simp)
    have r₂ : Run B (.assign "pv" (.get "stkV" (.var "sp"))) σ₁ σ₂ 4 :=
      (Run.assign (v := (f.v : ℕ)) (evalB_get (k := fs.length) (by simp [hσ₁]; omega)
        (by rw [hσ₁, arrs_setVar, hstkV, getElem?_arrOf SVa (by omega), hSV])
        (by omega))).mono (by simp)
    have r₃ : Run B (.assign "pb" (.get "stkB" (.var "sp"))) σ₂ σ₃ 4 :=
      (Run.assign (v := f.b) (evalB_get (k := fs.length) (by simp [hσ₂, hσ₁]; omega)
        (by rw [hσ₂, hσ₁, arrs_setVar, arrs_setVar, hstkB, getElem?_arrOf SBa (by omega),
            hSB])
        (by omega))).mono (by simp)
    have r₄ : Run B (.assign "tb" (.get "stkT" (.var "sp"))) σ₃ σ₄ 4 :=
      (Run.assign (v := (trail fs).length)
        (evalB_get (k := fs.length) (by simp [hσ₃, hσ₂, hσ₁]; omega)
        (by rw [hσ₃, hσ₂, hσ₁, arrs_setVar, arrs_setVar, arrs_setVar, hstkT,
            getElem?_arrOf STa (by omega), hST])
        (by omega))).mono (by simp)
    have htopf : (Cond.eq (Expr.var "top") (.lit 0)).evalB B τ = some false := by
      simp [htop']; omega
    cases hph : f.phase
    · -- **The flip.** The frame's vertex comes off the cover and its
      -- whole residual neighbourhood goes on.
      have hSf : f.S = [f.v] := hheal.2.2.2.2.1 hph
      have hphtest : (Cond.eq (Expr.get "stkP" (.var "sp")) (.lit 0)).evalB B σ₄
          = some true := by
        refine evalB_condEq (m := 0) (n := 0) ?_ (by simp; omega)
        refine evalB_get (k := fs.length) (by simp [hsp₄]; omega) ?_ (by omega)
        rw [harrs₄, hstkP, getElem?_arrOf SPa (by omega), hSP, hph]
        rfl
      set σ₅ : Env := σ₄.setArr "mark" ((f.v : ℕ)) 0 with hσ₅
      set σ₆ : Env := σ₅.setVar "tt" ((trail fs).length) with hσ₆
      set σ₇ : Env := σ₆.setVar "bud" f.b with hσ₇
      set σ₈ : Env := σ₇.setVar "j" (offset g ((f.v : ℕ))) with hσ₈
      set σ₉ : Env := σ₈.setVar "jend" (offset g ((f.v : ℕ) + 1)) with hσ₉
      obtain ⟨MK₀, hmark₅, hMK₅⟩ :
          ∃ MK₀, σ₅.arrs "mark" = arrOf n MK₀ ∧ Indicator (marked fs) MK₀ := by
        refine ⟨fun x => if x = (f.v : ℕ) then 0 else MK x, ?_, ?_⟩
        · rw [hσ₅, arrs_setArr, if_pos rfl, harrs₄, hmark, set_arrOf]
        · have h := indicator_set_zero (M := marked (f :: fs)) hMK hvn
          have he : (marked (f :: fs)).erase (⟨(f.v : ℕ), hvn⟩ : Fin n) = marked fs := by
            have hfv : (⟨(f.v : ℕ), hvn⟩ : Fin n) = f.v := rfl
            rw [hfv, marked_cons, hSf, toFinset_singleton_union,
              Finset.erase_insert hvnot]
          rwa [he] at h
      have harrs₅ : ∀ a, a ≠ "mark" → σ₅.arrs a = τ.arrs a := by
        intro a ha
        rw [hσ₅, arrs_setArr, if_neg ha, harrs₄]
      have harrs₉ : ∀ a, a ≠ "mark" → σ₉.arrs a = τ.arrs a := by
        intro a ha
        simp only [hσ₉, hσ₈, hσ₇, hσ₆, arrs_setVar]
        exact harrs₅ a ha
      have hmark₉ : σ₉.arrs "mark" = arrOf n MK₀ := by
        simp only [hσ₉, hσ₈, hσ₇, hσ₆, arrs_setVar]; exact hmark₅
      have hoff₇ : σ₇.arrs "off" = arrOf (n + 1) O := by
        simp only [hσ₇, hσ₆, arrs_setVar]
        rw [harrs₅ "off" (by decide), hoff]
      have hoff₈ : σ₈.arrs "off" = arrOf (n + 1) O := by
        simp only [hσ₈, arrs_setVar]; exact hoff₇
      have hoffv : offset g ((f.v : ℕ)) ≤ 2 * m := by
        have := offset_le hg (show (f.v : ℕ) ≤ n by omega); omega
      have hoffv1 : offset g ((f.v : ℕ) + 1) ≤ 2 * m := by
        have := offset_le hg (show (f.v : ℕ) + 1 ≤ n by omega); omega
      have r₅ : Run B (.store "mark" (.var "pv") (.lit 0)) σ₄ σ₅ 3 :=
        (Run.store (idx := (f.v : ℕ)) (v := 0) (by simp [hpv₄]; omega) (by simp; omega)
          (by rw [harrs₄, hmark, length_arrOf]; exact hvn)).mono (by simp)
      have r₆ : Run B (.assign "tt" (.var "tb")) σ₅ σ₆ 2 :=
        (Run.assign (v := (trail fs).length)
          (by simp [hσ₅, htb₄]; omega)).mono (by simp)
      have r₇ : Run B (.assign "bud" (.var "pb")) σ₆ σ₇ 2 :=
        (Run.assign (v := f.b)
          (by simp [hσ₆, hσ₅, hpb₄]; omega)).mono (by simp)
      have hpv₇ : σ₇.vars "pv" = (f.v : ℕ) := by
        simp only [hσ₇, hσ₆, vars_setVar, hσ₅, vars_setArr,
          if_neg (show ("pv" : String) ≠ "bud" by decide),
          if_neg (show ("pv" : String) ≠ "tt" by decide)]
        exact hpv₄
      have hpv₈ : σ₈.vars "pv" = (f.v : ℕ) := by
        simp only [hσ₈, vars_setVar, if_neg (show ("pv" : String) ≠ "j" by decide)]
        exact hpv₇
      have r₈ : Run B (.assign "j" (.get "off" (.var "pv"))) σ₇ σ₈ 3 :=
        (Run.assign (v := offset g ((f.v : ℕ)))
          (evalB_get (k := (f.v : ℕ)) (by simp [hpv₇]; omega)
            (by rw [hoff₇, getElem?_arrOf O (by omega), hO _ (by omega)])
            (by omega))).mono (by simp)
      have r₉ : Run B (.assign "jend" (.get "off" (.add (.var "pv") (.lit 1)))) σ₈ σ₉ 5 :=
        (Run.assign (v := offset g ((f.v : ℕ) + 1))
          (evalB_get (k := (f.v : ℕ) + 1) (by simp [hpv₈]; omega)
            (by rw [hoff₈, getElem?_arrOf O (by omega), hO _ (by omega)])
            (by omega))).mono (by simp)
      -- the row scan
      obtain ⟨τ₁, l, MK', TR', K₁, hrow, hlnd, hlfin, htt₁, hmark₁, hMK₁, htrail₁,
        hTRlo, hTRhi, harrs₁, hvars₁, hinp₁, hout₁, hK₁⟩ :=
        rowLoop_run (M := marked fs) (v := f.v) (MK := MK₀) (TR := TR)
          (tb := (trail fs).length) (τ := σ₉) hg hm hT (by omega) (by omega) hmB hcard
          hmark₉ hMK₅ (by rw [harrs₉ "trail" (by decide), htrail])
          (by rw [harrs₉ "tgt" (by decide), htgt])
          (by simp [hσ₉, hσ₈]) (by simp [hσ₉]) (by simp [hσ₉, hσ₈, hσ₇, hσ₆])
      have hlen : l.length = resDeg G (marked fs) f.v := by
        rw [resDeg_eq_card, ← hlfin, List.toFinset_card_of_nodup hlnd]
      have hln : (trail fs).length + l.length ≤ n := by
        have := length_add_card_le (M := marked fs) hlnd
          (fun w hw => (mem_resNbhd.1 (by rw [← hlfin]; exact List.mem_toFinset.2 hw)).2)
        omega
      have hv₁ : ∀ y, y ≠ "j" → y ≠ "w" → y ≠ "tt" → τ₁.vars y = σ₉.vars y := hvars₁
      have hv₉ : ∀ y, y ≠ "sp" → y ≠ "pv" → y ≠ "pb" → y ≠ "tb" → y ≠ "jend" →
          y ≠ "j" → y ≠ "bud" → y ≠ "tt" → σ₉.vars y = τ.vars y := by
        intro y h1 h2 h3 h4 h5 h6 h7 h8
        simp only [hσ₉, hσ₈, hσ₇, hσ₆, vars_setVar, hσ₅, vars_setArr, if_neg h5,
          if_neg h6, if_neg h7, if_neg h8]
        exact hv₄ y h1 h2 h3 h4
      have hsp₁ : τ₁.vars "sp" = fs.length := by
        rw [hv₁ "sp" (by decide) (by decide) (by decide)]
        simp only [hσ₉, hσ₈, hσ₇, hσ₆, vars_setVar, hσ₅, vars_setArr,
          if_neg (show ("sp" : String) ≠ "jend" by decide),
          if_neg (show ("sp" : String) ≠ "j" by decide),
          if_neg (show ("sp" : String) ≠ "bud" by decide),
          if_neg (show ("sp" : String) ≠ "tt" by decide)]
        exact hsp₄
      have htb₁ : τ₁.vars "tb" = (trail fs).length := by
        rw [hv₁ "tb" (by decide) (by decide) (by decide)]
        simp only [hσ₉, hσ₈, hσ₇, hσ₆, vars_setVar, hσ₅, vars_setArr,
          if_neg (show ("tb" : String) ≠ "jend" by decide),
          if_neg (show ("tb" : String) ≠ "j" by decide),
          if_neg (show ("tb" : String) ≠ "bud" by decide),
          if_neg (show ("tb" : String) ≠ "tt" by decide)]
        exact htb₄
      have hbud₁ : τ₁.vars "bud" = f.b := by
        rw [hv₁ "bud" (by decide) (by decide) (by decide)]
        simp [hσ₉, hσ₈, hσ₇]
      have hstkP₁ : τ₁.arrs "stkP" = arrOf (n + 1) SPa := by
        rw [harrs₁ "stkP" (by decide) (by decide), harrs₉ "stkP" (by decide), hstkP]
      set σ₁₀ : Env := τ₁.setArr "stkP" fs.length 1 with hσ₁₀
      set σ₁₁ : Env := σ₁₀.setVar "d" l.length with hσ₁₁
      obtain ⟨SP', hstkP₁₁, hSPtop, hSPlt⟩ :
          ∃ SP', σ₁₁.arrs "stkP" = arrOf (n + 1) SP' ∧ SP' fs.length = 1 ∧
            ∀ i, i ≠ fs.length → SP' i = SPa i := by
        refine ⟨fun i => if i = fs.length then 1 else SPa i, ?_, by simp, ?_⟩
        · rw [hσ₁₁, arrs_setVar, hσ₁₀, arrs_setArr, if_pos rfl, hstkP₁, set_arrOf]
        · intro i hi; simp [hi]
      have r₁₀ : Run B (.store "stkP" (.var "sp") (.lit 1)) τ₁ σ₁₀ 3 :=
        (Run.store (idx := fs.length) (v := 1) (by simp [hsp₁]; omega) (by simp; omega)
          (by rw [hstkP₁, length_arrOf]; omega)).mono (by simp)
      have r₁₁ : Run B (.assign "d" (.sub (.var "tt") (.var "tb"))) σ₁₀ σ₁₁ 4 :=
        (Run.assign (v := l.length)
          (by simp [hσ₁₀, htt₁, htb₁]; omega)).mono (by simp)
      have hbud₁₁ : σ₁₁.vars "bud" = f.b := by
        simp only [hσ₁₁, vars_setVar, if_neg (show ("bud" : String) ≠ "d" by decide),
          hσ₁₀, vars_setArr]
        exact hbud₁
      have hd₁₁ : σ₁₁.vars "d" = l.length := by simp [hσ₁₁]
      have htt₁₁ : σ₁₁.vars "tt" = (trail fs).length + l.length := by
        simp only [hσ₁₁, vars_setVar, if_neg (show ("tt" : String) ≠ "d" by decide),
          hσ₁₀, vars_setArr]
        exact htt₁
      have hkeep : ∀ y, y ≠ "sp" → y ≠ "pv" → y ≠ "pb" → y ≠ "tb" → y ≠ "jend" →
          y ≠ "j" → y ≠ "bud" → y ≠ "tt" → y ≠ "w" → y ≠ "d" →
          σ₁₁.vars y = τ.vars y := by
        intro y h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
        simp only [hσ₁₁, vars_setVar, if_neg h10, hσ₁₀, vars_setArr]
        rw [hv₁ y h6 h9 h8]
        exact hv₉ y h1 h2 h3 h4 h5 h6 h7 h8
      have hmark₁₁ : σ₁₁.arrs "mark" = arrOf n MK' := by
        rw [hσ₁₁, arrs_setVar, hσ₁₀, arrs_setArr,
          if_neg (show ("mark" : String) ≠ "stkP" by decide), hmark₁]
      have hMKnew : Indicator (marked (Frame.mk f.v f.b true l :: fs)) MK' := by
        rw [marked_cons, Finset.union_comm]
        exact hMK₁
      have htrail₁₁ : σ₁₁.arrs "trail" = arrOf (n + 1) TR' := by
        rw [hσ₁₁, arrs_setVar, hσ₁₀, arrs_setArr,
          if_neg (show ("trail" : String) ≠ "stkP" by decide), htrail₁]
      have hlenv : (trailVals fs).length = (trail fs).length := length_trailVals _
      have hTRnew : ∀ i < (trail (Frame.mk f.v f.b true l :: fs)).length,
          TR' i = (trailVals (Frame.mk f.v f.b true l :: fs)).getD i 0 := by
        intro i hi
        simp only [trail_cons, List.length_append] at hi
        rcases Nat.lt_or_ge i ((trail fs).length) with hlt | hge
        · rw [hTRlo i hlt, hTR i (by simp only [trail_cons, List.length_append]; omega)]
          simp only [trailVals_cons]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
        · obtain ⟨i', rfl⟩ : ∃ i', i = (trail fs).length + i' :=
            ⟨i - (trail fs).length, by omega⟩
          have hi' : i' < l.length := by omega
          simp only [trailVals_cons]
          rw [hTRhi i' hi', List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by omega), hlenv]
          simp [hi']
      have hstkarr : ∀ a, a ≠ "mark" → a ≠ "trail" → a ≠ "stkP" →
          σ₁₁.arrs a = τ.arrs a := by
        intro a h1 h2 h3
        rw [hσ₁₁, arrs_setVar, hσ₁₀, arrs_setArr, if_neg h3, harrs₁ a h1 h2,
          harrs₉ a h1]
      have hstknew : ∀ i (hi : i < (Frame.mk f.v f.b true l :: fs).length),
          SVa i = (((Frame.mk f.v f.b true l :: fs).reverse[i]'(by simpa using hi)).v : ℕ) ∧
          SBa i = ((Frame.mk f.v f.b true l :: fs).reverse[i]'(by simpa using hi)).b ∧
          STa i = base (Frame.mk f.v f.b true l :: fs) i ∧
          SP' i = if ((Frame.mk f.v f.b true l :: fs).reverse[i]'(by simpa using hi)).phase
            then 1 else 0 := by
        intro i hi
        simp only [List.length_cons] at hi
        rcases Nat.lt_or_ge i fs.length with hlt | hge
        · obtain ⟨h1, h2, h3, h4⟩ := hstk i (by simp; omega)
          rw [getElem_reverse_lt _ hlt] at h1 h2 h4
          rw [base_cons (le_of_lt hlt)] at h3
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp only [getElem_reverse_lt _ hlt, base_cons (le_of_lt hlt),
              hSPlt i (by omega)]
          exacts [h1, h2, h3, h4]
        · have hif : i = fs.length := by omega
          subst hif
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [getElem_reverse_top, base_top, hSPtop]
          exacts [hSV, hSB, hST, by simp]
      by_cases hfeas : l.length ≤ f.b
      · -- **T6, the feasible flip.**
        set σ₁₂ : Env := σ₁₁.setVar "bud" (f.b - l.length) with hσ₁₂
        set σ₁₃ : Env := σ₁₂.setVar "mode" 0 with hσ₁₃
        have hfeastest : (Cond.lt (Expr.var "d") (.add (.var "bud") (.lit 1))).evalB B σ₁₁
            = some true := by simp [hd₁₁, hbud₁₁]; omega
        have r₁₂ : Run B (.assign "bud" (.sub (.var "bud") (.var "d"))) σ₁₁ σ₁₂ 4 :=
          (Run.assign (v := f.b - l.length)
            (by simp [hd₁₁, hbud₁₁]; omega)).mono (by simp)
        have r₁₃ : Run B (.assign "mode" (.lit 0)) σ₁₂ σ₁₃ 2 :=
          (Run.assign (v := 0) (by simp; omega)).mono (by simp)
        have rflip : Run B flipFrame σ₄ σ₁₃ (K₁ + 40) := by
          rw [flipFrame_eq]
          refine (Run.seq r₅ (Run.seq r₆ (Run.seq r₇ (Run.seq r₈ (Run.seq r₉
            (Run.seq hrow (Run.seq r₁₀ (Run.seq r₁₁
              (Run.ite_true hfeastest (Run.seq r₁₂ r₁₃)))))))))).mono ?_
          simp only [size_condLt, size_var, size_lit, size_add]
          omega
        have rback : Run B backtrackBody τ σ₁₃ (K₁ + 70) := by
          refine (Run.ite_false htopf (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄
            (Run.ite_true hphtest rflip)))))).mono ?_
          simp only [size_condEq, size_var, size_lit, size_get]
          omega
        obtain ⟨hJ', hpot'⟩ := step_flip hJ hmode hfrs hph hlnd hlfin (by omega)
        refine ⟨⟨Frame.mk f.v f.b true l :: fs, 0,
            f.b - resDeg G (marked fs) f.v, C.ans⟩, σ₁₃, K₁ + 70, rback, ?_,
          hJ', hpot', ?_, ?_, by omega⟩
        · refine ⟨?_, ?_, ?_, by simp [hσ₁₃],
            by rw [hσ₁₃, vars_setVar, if_neg (show ("bud" : String) ≠ "mode" by decide),
              hσ₁₂, vars_setVar, if_pos rfl, hlen], ?_, ?_, ?_,
            ⟨MK', ?_, hMKnew⟩, ⟨TR', ?_, hTRnew⟩,
            SVa, SBa, STa, SP', ?_, ?_, ?_, ?_, hstknew⟩
          · rw [hσ₁₃, vars_setVar, if_neg (show ("m2" : String) ≠ "mode" by decide),
              hσ₁₂, vars_setVar, if_neg (show ("m2" : String) ≠ "bud" by decide),
              hkeep "m2" (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hm2
          · rw [hσ₁₃, arrs_setVar, hσ₁₂, arrs_setVar,
              hstkarr "off" (by decide) (by decide) (by decide), hoff]
          · rw [hσ₁₃, arrs_setVar, hσ₁₂, arrs_setVar,
              hstkarr "tgt" (by decide) (by decide) (by decide), htgt]
          · rw [hσ₁₃, vars_setVar, if_neg (show ("ans" : String) ≠ "mode" by decide),
              hσ₁₂, vars_setVar, if_neg (show ("ans" : String) ≠ "bud" by decide),
              hkeep "ans" (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hans
          · rw [hσ₁₃, vars_setVar, if_neg (show ("top" : String) ≠ "mode" by decide),
              hσ₁₂, vars_setVar, if_neg (show ("top" : String) ≠ "bud" by decide),
              hkeep "top" (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide), htop']
            simp
          · rw [hσ₁₃, vars_setVar, if_neg (show ("tt" : String) ≠ "mode" by decide),
              hσ₁₂, vars_setVar, if_neg (show ("tt" : String) ≠ "bud" by decide), htt₁₁]
            simp only [trail_cons, List.length_append]
            omega
          · rw [hσ₁₃, arrs_setVar, hσ₁₂, arrs_setVar, hmark₁₁]
          · rw [hσ₁₃, arrs_setVar, hσ₁₂, arrs_setVar, htrail₁₁]
          · rw [hσ₁₃, arrs_setVar, hσ₁₂, arrs_setVar,
              hstkarr "stkV" (by decide) (by decide) (by decide), hstkV]
          · rw [hσ₁₃, arrs_setVar, hσ₁₂, arrs_setVar,
              hstkarr "stkB" (by decide) (by decide) (by decide), hstkB]
          · rw [hσ₁₃, arrs_setVar, hσ₁₂, arrs_setVar,
              hstkarr "stkT" (by decide) (by decide) (by decide), hstkT]
          · rw [hσ₁₃, arrs_setVar, hσ₁₂, arrs_setVar, hstkP₁₁]
        · simp only [hσ₁₃, hσ₁₂, hσ₁₁, inp_setVar, hσ₁₀, inp_setArr]
          rw [hinp₁]
          simp only [hσ₉, hσ₈, hσ₇, hσ₆, inp_setVar, hσ₅, inp_setArr, hσ₄, hσ₃, hσ₂,
            hσ₁]
        · simp only [hσ₁₃, hσ₁₂, hσ₁₁, out_setVar, hσ₁₀, out_setArr]
          rw [hout₁]
          simp only [hσ₉, hσ₈, hσ₇, hσ₆, out_setVar, hσ₅, out_setArr, hσ₄, hσ₃, hσ₂,
            hσ₁]
      · -- **T7, the infeasible flip.**
        have hinfeastest :
            (Cond.lt (Expr.var "d") (.add (.var "bud") (.lit 1))).evalB B σ₁₁
              = some false := by simp [hd₁₁, hbud₁₁]; omega
        have rflip : Run B flipFrame σ₄ σ₁₁ (K₁ + 40) := by
          rw [flipFrame_eq]
          refine (Run.seq r₅ (Run.seq r₆ (Run.seq r₇ (Run.seq r₈ (Run.seq r₉
            (Run.seq hrow (Run.seq r₁₀ (Run.seq r₁₁
              (Run.ite_false hinfeastest Run.skip))))))))).mono ?_
          simp only [size_condLt, size_var, size_lit, size_add]
          omega
        have rback : Run B backtrackBody τ σ₁₁ (K₁ + 70) := by
          refine (Run.ite_false htopf (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄
            (Run.ite_true hphtest rflip)))))).mono ?_
          simp only [size_condEq, size_var, size_lit, size_get]
          omega
        obtain ⟨hJ', hpot'⟩ :=
          step_flip_infeasible f.b hJ hmode hfrs hph hlnd hlfin (by omega)
        refine ⟨⟨Frame.mk f.v f.b true l :: fs, 1, f.b, C.ans⟩, σ₁₁,
          K₁ + 70, rback, ?_, hJ', hpot', ?_, ?_, by omega⟩
        · refine ⟨?_, ?_, ?_, ?_, hbud₁₁, ?_, ?_, ?_,
            ⟨MK', hmark₁₁, hMKnew⟩, ⟨TR', htrail₁₁, hTRnew⟩,
            SVa, SBa, STa, SP', ?_, ?_, ?_, hstkP₁₁, hstknew⟩
          · rw [hkeep "m2" (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hm2
          · rw [hstkarr "off" (by decide) (by decide) (by decide), hoff]
          · rw [hstkarr "tgt" (by decide) (by decide) (by decide), htgt]
          · rw [hkeep "mode" (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hmd, hmode]
          · rw [hkeep "ans" (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hans
          · rw [hkeep "top" (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), htop']
            simp
          · rw [htt₁₁]
            simp only [trail_cons, List.length_append]
            omega
          · rw [hstkarr "stkV" (by decide) (by decide) (by decide), hstkV]
          · rw [hstkarr "stkB" (by decide) (by decide) (by decide), hstkB]
          · rw [hstkarr "stkT" (by decide) (by decide) (by decide), hstkT]
        · simp only [hσ₁₁, inp_setVar, hσ₁₀, inp_setArr]
          rw [hinp₁]
          simp only [hσ₉, hσ₈, hσ₇, hσ₆, inp_setVar, hσ₅, inp_setArr, hσ₄, hσ₃, hσ₂,
            hσ₁]
        · simp only [hσ₁₁, out_setVar, hσ₁₀, out_setArr]
          rw [hout₁]
          simp only [hσ₉, hσ₈, hσ₇, hσ₆, out_setVar, hσ₅, out_setArr, hσ₄, hσ₃, hσ₂,
            hσ₁]
    · -- **T8, the pop.** The frame has spent both branches; the unwind
      -- loop takes its marks back off and its budget comes back.
      have hphtest : (Cond.eq (Expr.get "stkP" (.var "sp")) (.lit 0)).evalB B σ₄
          = some false := by
        refine evalB_condEq (m := 1) (n := 0) ?_ (by simp; omega)
        refine evalB_get (k := fs.length) (by simp [hsp₄]; omega) ?_ (by omega)
        rw [harrs₄, hstkP, getElem?_arrOf SPa (by omega), hSP, hph]
        rfl
      have hlenv : (trailVals fs).length = (trail fs).length := length_trailVals _
      obtain ⟨τ₂, MK', K₂, hunw, htt₂, hmark₂, hMK₂, harrs₂, hvars₂, hinp₂, hout₂,
        hK₂⟩ :=
        unwind_run (B := B) (M := marked fs) (S := f.S) (MK := MK) (TR := TR)
          (tb := (trail fs).length) (τ := σ₄) (by omega) (by omega) hnd0
          hheal.head_disjoint (by rw [harrs₄, hmark])
          (by rw [marked_cons] at hMK; exact hMK) (by rw [harrs₄, htrail])
          (fun i hi => by
            rw [hTR _ (by simp only [trail_cons, List.length_append]; omega)]
            simp only [trailVals_cons]
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlenv]
            simp [hi])
          htb₄ (by rw [hv₄ "tt" (by decide) (by decide) (by decide) (by decide), htt'])
          htrn
      set σ₅ : Env := τ₂.setVar "bud" f.b with hσ₅
      set σ₆ : Env := σ₅.setVar "top" fs.length with hσ₆
      have hv₂ : ∀ y, y ≠ "tt" → τ₂.vars y = σ₄.vars y := hvars₂
      have hpb₂ : τ₂.vars "pb" = f.b := by rw [hv₂ "pb" (by decide), hpb₄]
      have htop₂ : τ₂.vars "top" = fs.length + 1 := by
        rw [hv₂ "top" (by decide),
          hv₄ "top" (by decide) (by decide) (by decide) (by decide), htop']
      have rb₅ : Run B (.assign "bud" (.var "pb")) τ₂ σ₅ 2 :=
        (Run.assign (v := f.b) (by simp [hpb₂]; omega)).mono (by simp)
      have rb₆ : Run B (.assign "top" (.sub (.var "top") (.lit 1))) σ₅ σ₆ 4 :=
        (Run.assign (v := fs.length) (by simp [hσ₅, htop₂]; omega)).mono (by simp)
      have rpop : Run B popFrame σ₄ σ₆ (K₂ + 10) := by
        rw [popFrame_eq]
        exact (Run.seq hunw (Run.seq rb₅ rb₆)).mono (by omega)
      have rback : Run B backtrackBody τ σ₆ (K₂ + 40) := by
        refine (Run.ite_false htopf (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄
          (Run.ite_false hphtest rpop)))))).mono ?_
        simp only [size_condEq, size_var, size_lit, size_get]
        omega
      obtain ⟨hJ', hpot'⟩ := step_pop f.b hJ hmode hfrs hph
      refine ⟨⟨fs, 1, f.b, C.ans⟩, σ₆, K₂ + 40, rback, ?_, hJ', hpot',
        ?_, ?_, by omega⟩
      · have hkeep₆ : ∀ y, y ≠ "sp" → y ≠ "pv" → y ≠ "pb" → y ≠ "tb" → y ≠ "tt" →
            y ≠ "bud" → y ≠ "top" → σ₆.vars y = τ.vars y := by
          intro y h1 h2 h3 h4 h5 h6 h7
          simp only [hσ₆, hσ₅, vars_setVar, if_neg h6, if_neg h7]
          rw [hv₂ y h5]
          exact hv₄ y h1 h2 h3 h4
        have harrs₆ : ∀ a, a ≠ "mark" → σ₆.arrs a = τ.arrs a := by
          intro a ha
          simp only [hσ₆, hσ₅, arrs_setVar]
          rw [harrs₂ a ha, harrs₄]
        refine ⟨?_, ?_, ?_, ?_, by simp [hσ₆, hσ₅], ?_, by simp [hσ₆], ?_,
          ⟨MK', ?_, hMK₂⟩, ⟨TR, ?_, ?_⟩, SVa, SBa, STa, SPa, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hkeep₆ "m2" (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]
          exact hm2
        · rw [harrs₆ "off" (by decide), hoff]
        · rw [harrs₆ "tgt" (by decide), htgt]
        · rw [hkeep₆ "mode" (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide), hmd, hmode]
        · rw [hkeep₆ "ans" (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]
          exact hans
        · rw [hσ₆, vars_setVar, if_neg (show ("tt" : String) ≠ "top" by decide), hσ₅,
            vars_setVar, if_neg (show ("tt" : String) ≠ "bud" by decide), htt₂]
        · rw [hσ₆, arrs_setVar, hσ₅, arrs_setVar, hmark₂]
        · rw [harrs₆ "trail" (by decide), htrail]
        · intro i hi
          have hi' : i < (trail fs).length := hi
          rw [hTR i (by simp only [trail_cons, List.length_append]; omega)]
          simp only [trailVals_cons]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by omega)]
        · rw [harrs₆ "stkV" (by decide), hstkV]
        · rw [harrs₆ "stkB" (by decide), hstkB]
        · rw [harrs₆ "stkT" (by decide), hstkT]
        · rw [harrs₆ "stkP" (by decide), hstkP]
        · intro i hi
          have hi' : i < fs.length := hi
          obtain ⟨h1, h2, h3, h4⟩ := hstk i (by simp; omega)
          rw [getElem_reverse_lt _ hi'] at h1 h2 h4
          rw [base_cons (le_of_lt hi')] at h3
          exact ⟨h1, h2, h3, h4⟩
      · simp only [hσ₆, hσ₅, inp_setVar]
        rw [hinp₂]
        simp only [hσ₄, hσ₃, hσ₂, hσ₁, inp_setVar]
      · simp only [hσ₆, hσ₅, out_setVar]
        rw [hout₂]
        simp only [hσ₄, hσ₃, hσ₂, hσ₁, out_setVar]

/-! ### One turn of the outer loop -/

/-- **The body.** The mode dispatches; either way the configuration
advances by one transition, the invariant survives, the potential drops
by at least one, and the cost is linear in the size of the encoding. -/
theorem outerBody_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ p < 2 * m, T p = target g p)
    (h2B : 2 < B) (hnB : n + 1 < B) (hmB : 2 * m < B) (hkB : k + 1 < B)
    {C : Config n} {τ : Env} (hRep : Rep n m O T C τ) (hJ : J G k C)
    (hmode : C.mode < 2) :
    ∃ (C' : Config n) (τ' : Env) (K : ℕ), Run B outerBody τ τ' K ∧
      Rep n m O T C' τ' ∧ J G k C' ∧ pot C' + 1 ≤ pot C ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out ∧ K ≤ 510 * (n + 2 * m + 1) := by
  have hmd : τ.vars "mode" = C.mode := hRep.mode
  by_cases h0 : C.mode = 0
  · obtain ⟨C', τ', K, hrun, hRep', hJ', hpot, hi, ho, hK⟩ :=
      descendBody_run hg hm hO hT h2B hnB hmB hkB hRep hJ h0
    refine ⟨C', τ', 1 + (Cond.eq (Expr.var "mode") (Expr.lit 0)).size + K,
      Run.ite_true (by simp [hmd, h0]; omega) hrun, hRep', hJ', hpot, hi, ho, ?_⟩
    simp only [size_condEq, size_var, size_lit]
    omega
  · have h1 : C.mode = 1 := by omega
    obtain ⟨C', τ', K, hrun, hRep', hJ', hpot, hi, ho, hK⟩ :=
      backtrackBody_run hg hm hO hT h2B hnB hmB hkB hRep hJ h1
    refine ⟨C', τ', 1 + (Cond.eq (Expr.var "mode") (Expr.lit 0)).size + K,
      Run.ite_false (by simp [hmd, h1]; omega) hrun, hRep', hJ', hpot, hi, ho, ?_⟩
    simp only [size_condEq, size_var, size_lit]
    omega

end Lax15Proofs.VC
