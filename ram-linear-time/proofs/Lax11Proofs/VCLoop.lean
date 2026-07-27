import Lax11Proofs.VCScan

/-!
The outer loop: one transition lemma for the body, then the loop rule.

`Rep` says what the arrays and scalars hold when the pure configuration
is `C`: the stack arrays list the frames bottom-up — entry `i` is frame
`i` counted from the bottom, which is `C.frames.reverse[i]`, since the
pure stack keeps its top at the head — and the mark array is the
indicator of the marked set. The invariant handed to the loop rule is
"some configuration is represented, and it satisfies `Inv`".

The loop potential must be a total function of the environment, so it
cannot read the pure configuration; `phasesOf` reads the phase list
back off the stack array — garbage off the invariant is fine, since
only invariant states are ever compared — and `potN` mirrors `pot` on
it. On represented states the two agree, which is the one lemma that
crosses between the numeric and the pure potential.

Each body case builds its `Run` by hand, hands the new configuration to
the matching preservation lemma of `VCSpec`, and pays the loop rule out
of the matching drop lemma. The descend cases contain the scan; their
cost is `≤ 100m + 50n + 96`, which is why the loop potential carries
the factor `100m + 50n + 104`.

The value bound is four hypotheses and no invariant clause. Beyond what
the scan needs, the search produces stack indices and budgets, both
below `k`, and the marks and modes, which are `0`, `1` or `2`; so `2`,
`n`, `2m` and `k` being words is the whole of it, and in particular the
`2 ^ k` of the running time is nowhere among the numbers held.
-/

namespace Lax11Proofs.VC

open Lax13.Ram Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax11Proofs.CC

variable {g : List ℕ} {n m k B : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}

/-! ### Representation -/

/-- The arrays and scalars represent the configuration `C`: the CSR
arrays hold the encoding, the mode, budget, answer and stack pointer
are the configuration's, the mark array is the indicator of the marked
set, and the stack arrays list the frames bottom-up. -/
def Rep (n m k : ℕ) (O T : ℕ → ℕ) (C : Config n) (τ : Env) : Prop :=
  τ.vars "m2" = 2 * m ∧
  τ.arrs "off" = arrOf (n + 1) O ∧ τ.arrs "tgt" = arrOf (2 * m) T ∧
  τ.vars "mode" = C.mode ∧ τ.vars "bud" = C.bud ∧ τ.vars "ans" = C.ans ∧
  τ.vars "top" = C.frames.length ∧
  (∃ MK, τ.arrs "mark" = arrOf n MK ∧
    ∀ w (hw : w < n), MK w = if (⟨w, hw⟩ : Fin n) ∈ marked C.frames then 1 else 0) ∧
  (∃ SU SV SP, τ.arrs "stkU" = arrOf k SU ∧ τ.arrs "stkV" = arrOf k SV ∧
    τ.arrs "stkP" = arrOf k SP ∧
    ∀ i (hi : i < C.frames.length),
      SU i = ((C.frames.reverse[i]'(by simpa using hi)).u : ℕ) ∧
      SV i = ((C.frames.reverse[i]'(by simpa using hi)).v : ℕ) ∧
      SP i = if (C.frames.reverse[i]'(by simpa using hi)).ph then 1 else 0)

/-- Reading the top frame out of the bottom-up array order. -/
theorem reverse_getElem_top (f : Frame n) (fs : List (Frame n)) :
    (f :: fs).reverse[fs.length]'(by simp) = f := by
  simp

/-- Reading a lower frame past a push, in the bottom-up order. -/
theorem reverse_getElem_lt (f : Frame n) {fs : List (Frame n)} {i : ℕ}
    (hi : i < fs.length) :
    (f :: fs).reverse[i]'(by simp; omega) = fs.reverse[i]'(by simpa using hi) := by
  simp only [List.reverse_cons]
  rw [List.getElem_append_left (by simpa using hi)]

/-- An indicator that is not `0` witnesses membership. -/
theorem mem_of_indicator_ne {MK : ℕ → ℕ} {fs : List (Frame n)}
    (hMK : ∀ w (hw : w < n), MK w = if (⟨w, hw⟩ : Fin n) ∈ marked fs then 1 else 0)
    {w : ℕ} (hw : w < n) (h : MK w ≠ 0) : (⟨w, hw⟩ : Fin n) ∈ marked fs := by
  by_contra hmem
  rw [hMK w hw, if_neg hmem] at h
  exact h rfl

/-- An indicator that is `0` witnesses non-membership. -/
theorem not_mem_of_indicator_eq {MK : ℕ → ℕ} {fs : List (Frame n)}
    (hMK : ∀ w (hw : w < n), MK w = if (⟨w, hw⟩ : Fin n) ∈ marked fs then 1 else 0)
    {w : ℕ} (hw : w < n) (h : MK w = 0) : (⟨w, hw⟩ : Fin n) ∉ marked fs := by
  intro hmem
  rw [hMK w hw, if_pos hmem] at h
  exact absurd h one_ne_zero

/-- The indicator array is a word array as soon as `1` is a word: its
entries are `0` and `1`. -/
theorem indicator_lt {MK : ℕ → ℕ} {fs : List (Frame n)} (h1B : 1 < B)
    (hMK : ∀ w (hw : w < n), MK w = if (⟨w, hw⟩ : Fin n) ∈ marked fs then 1 else 0)
    {w : ℕ} (hw : w < n) : MK w < B := by
  rw [hMK w hw]
  split <;> omega

/-! ### The numeric potential -/

/-- The stack potential read off the phase list alone. -/
def stackPotB : List Bool → ℕ → ℕ
  | [], _ => 0
  | ph :: phs, b => (if ph then 1 else fPot b + 2) + stackPotB phs (b + 1)

theorem stackPot_eq_stackPotB (fs : List (Frame n)) (b : ℕ) :
    stackPot fs b = stackPotB (fs.map Frame.ph) b := by
  induction fs generalizing b with
  | nil => rfl
  | cons f fs ih => simp [stackPot, stackPotB, ih]

/-- The potential as a function of what the environment holds: mode,
budget, and the phase list. -/
def potN (mode bud : ℕ) (phs : List Bool) : ℕ :=
  (if mode = 0 then fPot bud else 0) + stackPotB phs bud + (if mode = 2 then 0 else 1)

theorem pot_eq_potN (C : Config n) :
    pot C = potN C.mode C.bud (C.frames.map Frame.ph) := by
  simp [pot, potN, stackPot_eq_stackPotB]

/-- The phase list, read back off the stack array top-first. Total on
every environment; meaningful on represented ones. -/
def phasesOf (τ : Env) : List Bool :=
  (List.range (τ.vars "top")).map
    (fun i => (τ.arrs "stkP").getD (τ.vars "top" - 1 - i) 0 == 1)

/-- On a represented state the numeric phase list is the pure one. -/
theorem phasesOf_eq {C : Config n} {τ : Env} (hRep : Rep n m k O T C τ)
    (hlen : C.frames.length ≤ k) :
    phasesOf τ = C.frames.map Frame.ph := by
  obtain ⟨-, -, -, -, -, -, htop, -, SU, SV, SP, -, -, hstkP, hstk⟩ := hRep
  refine List.ext_getElem (by simp [phasesOf, htop]) fun i h₁ h₂ => ?_
  simp only [phasesOf, List.getElem_map, List.getElem_range, List.length_map,
    List.length_range] at h₁ h₂ ⊢
  rw [htop] at h₁ ⊢
  have hik : C.frames.length - 1 - i < k := by omega
  have hil : C.frames.length - 1 - i < C.frames.length := by omega
  rw [hstkP, getD_arrOf SP hik, (hstk _ hil).2.2]
  have hrev : (C.frames.reverse[C.frames.length - 1 - i]'(by simpa using hil)) =
      C.frames[i]'h₂ := by
    rw [List.getElem_reverse]
    congr 1
    omega
  rw [hrev]
  cases hph : (C.frames[i]'h₂).ph <;> simp

/-- On a represented state the numeric potential is the pure one. -/
theorem potN_eq {C : Config n} {τ : Env} (hRep : Rep n m k O T C τ)
    (hlen : C.frames.length ≤ k) :
    potN (τ.vars "mode") (τ.vars "bud") (phasesOf τ) = pot C := by
  rw [hRep.2.2.2.1, hRep.2.2.2.2.1, phasesOf_eq hRep hlen, ← pot_eq_potN]

/-! ### The body of the outer loop

Six transitions, three theorems. Descend runs the scan and then either
exits with `1`, gives up on the branch, or pushes a frame; backtrack
either exits with `0`, flips the top frame, or pops it. Each case names
the new configuration, builds its `Run` by hand, re-establishes every
clause of `Rep`, hands the configuration to the matching preservation
lemma and pays the loop rule out of the matching drop lemma. -/

/-- **Descend.** From a represented state in mode `0`, the descend body
reaches a represented state whose configuration still satisfies the
invariant and whose potential has dropped, within `100m + 50n + 96`
steps. -/
theorem descendBody_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ j < 2 * m, T j = target g j)
    (h2B : 2 < B) (hnB : n < B) (hmB : 2 * m < B) (hkB : k < B)
    {C : Config n} {τ : Env} (hRep : Rep n m k O T C τ)
    (hInv : Inv G k C) (hmode : C.mode = 0) :
    ∃ (C' : Config n) (τ' : Env) (K : ℕ),
      Run B descendBody τ τ' K ∧ Rep n m k O T C' τ' ∧ Inv G k C' ∧
      pot C' + 1 ≤ pot C ∧ K ≤ 100 * m + 50 * n + 96 ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out := by
  obtain ⟨hm2, hoff, htgt, hmd, hbud, hans, htop, ⟨MK, hmark, hMK⟩,
    SU, SV, SP, hstkU, hstkV, hstkP, hstk⟩ := hRep
  have hlen : C.bud + C.frames.length = k := hInv.2.1
  have hbudB : C.bud < B := by omega
  have hfrlB : C.frames.length < B := by omega
  have hMKB : ∀ i, i < n → MK i < B := fun i hi => indicator_lt (by omega) hMK hi
  have hpotC : pot C = pot (⟨C.frames, 0, C.bud, C.ans⟩ : Config n) := by
    simp [pot, hmode]
  obtain ⟨σ', hrun, harrs', hinp', hout', hfrm, hdich⟩ :=
    scan_run hg hm hO hT (by omega) hnB hmB hMKB hm2 hoff htgt hmark
  have hfm2 : σ'.vars "m2" = 2 * m := by
    rw [hfrm "m2" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hm2
  have hfmd : σ'.vars "mode" = C.mode := by
    rw [hfrm "mode" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hmd
  have hfbud : σ'.vars "bud" = C.bud := by
    rw [hfrm "bud" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hbud
  have hfans : σ'.vars "ans" = C.ans := by
    rw [hfrm "ans" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hans
  have hftop : σ'.vars "top" = C.frames.length := by
    rw [hfrm "top" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact htop
  have hoff' : σ'.arrs "off" = arrOf (n + 1) O := by rw [harrs']; exact hoff
  have htgt' : σ'.arrs "tgt" = arrOf (2 * m) T := by rw [harrs']; exact htgt
  have hmark' : σ'.arrs "mark" = arrOf n MK := by rw [harrs']; exact hmark
  have hstkU' : σ'.arrs "stkU" = arrOf k SU := by rw [harrs']; exact hstkU
  have hstkV' : σ'.arrs "stkV" = arrOf k SV := by rw [harrs']; exact hstkV
  have hstkP' : σ'.arrs "stkP" = arrOf k SP := by rw [harrs']; exact hstkP
  rcases hdich with ⟨hf0, hcov⟩ | ⟨hf1, heu, hev, hadj, hMKeu, hMKev⟩
  · -- **Success exit.** Every slot is covered, so the marking is a cover.
    refine ⟨⟨C.frames, 2, C.bud, 1⟩, (σ'.setVar "ans" 1).setVar "mode" 2,
      100 * m + 50 * n + 96, ?_, ?_, ?_, ?_, le_rfl, by simp [hinp'], by simp [hout']⟩
    · refine (Run.seq hrun (Run.ite_true (by simp [hf0]; omega)
        (Run.seq (Run.assign (v := 1) (by simp; omega))
          (Run.assign (v := 2) (by simp; omega))))).mono ?_
      simp
    · exact ⟨by simp [hfm2], by simp [hoff'], by simp [htgt'], by simp, by simp [hfbud],
        by simp, by simp [hftop], ⟨MK, by simp [hmark'], hMK⟩,
        SU, SV, SP, by simp [hstkU'], by simp [hstkV'], by simp [hstkP'], hstk⟩
    · refine inv_found_cover hInv hmode (isVertexCover_of_slots hg _ ?_)
      intro o p ho hp h1 h2
      rcases hcov o p ho h1 h2 with h | h
      · exact Or.inl (mem_of_indicator_ne hMK ho h)
      · exact Or.inr (mem_of_indicator_ne hMK hp h)
    · rw [hpotC]; exact pot_found _ _ _
  · obtain ⟨heu', hev', hadjuv⟩ := hadj
    by_cases hb : C.bud = 0
    · -- **Stuck.** An uncovered edge and no budget: the branch is dead.
      refine ⟨⟨C.frames, 1, C.bud, C.ans⟩, σ'.setVar "mode" 1,
        100 * m + 50 * n + 96, ?_, ?_, ?_, ?_, le_rfl, by simp [hinp'], by simp [hout']⟩
      · refine (Run.seq hrun (Run.ite_false (by simp [hf1]; omega)
          (Run.ite_true (by simp [hfbud, hb]; omega)
            (Run.assign (v := 1) (by simp; omega))))).mono ?_
        simp
      · exact ⟨by simp [hfm2], by simp [hoff'], by simp [htgt'], by simp, by simp [hfbud],
          by simp [hfans], by simp [hftop], ⟨MK, by simp [hmark'], hMK⟩,
          SU, SV, SP, by simp [hstkU'], by simp [hstkV'], by simp [hstkP'], hstk⟩
      · exact inv_stuck hInv hmode hb hadjuv (not_mem_of_indicator_eq hMK heu' hMKeu)
          (not_mem_of_indicator_eq hMK hev' hMKev)
      · rw [hpotC, hb]; exact pot_stuck _ _
    · -- **Push.** An uncovered edge with budget left: commit `eu`.
      have hbpos : 0 < C.bud := Nat.pos_of_ne_zero hb
      have hfk : C.frames.length < k := by omega
      refine ⟨⟨Frame.mk ⟨σ'.vars "eu", heu'⟩ ⟨σ'.vars "ev", hev'⟩ false :: C.frames,
          0, C.bud - 1, C.ans⟩,
        (((((σ'.setArr "stkU" C.frames.length (σ'.vars "eu")).setArr "stkV"
            C.frames.length (σ'.vars "ev")).setArr "stkP" C.frames.length 0).setArr
            "mark" (σ'.vars "eu") 1).setVar "top" (C.frames.length + 1)).setVar
            "bud" (C.bud - 1),
        100 * m + 50 * n + 96, ?_, ?_, ?_, ?_, le_rfl, by simp [hinp'], by simp [hout']⟩
      · refine (Run.seq hrun (Run.ite_false (by simp [hf1]; omega)
          (Run.ite_false (by simp [hfbud, hb]; omega)
            (Run.seq (Run.store (idx := C.frames.length) (v := σ'.vars "eu")
                (by simp [hftop]; omega) (by simp; omega) (by simpa [hstkU'] using hfk))
              (Run.seq (Run.store (idx := C.frames.length) (v := σ'.vars "ev")
                  (by simp [hftop]; omega) (by simp; omega) (by simpa [hstkV'] using hfk))
                (Run.seq (Run.store (idx := C.frames.length) (v := 0)
                    (by simp [hftop]; omega) (by simp; omega)
                    (by simpa [hstkP'] using hfk))
                  (Run.seq (Run.store (idx := σ'.vars "eu") (v := 1)
                      (by simp; omega) (by simp; omega) (by simpa [hmark'] using heu'))
                    (Run.seq (Run.assign (v := C.frames.length + 1)
                        (by simp [hftop]; omega))
                      (Run.assign (v := C.bud - 1)
                        (by simp [hfbud]; omega)))))))))).mono ?_
        simp
      · refine ⟨by simp [hfm2], by simp [hoff'], by simp [htgt'],
          by simp [hfmd, hmode], by simp, by simp [hfans], by simp,
          ⟨fun w => if w = σ'.vars "eu" then 1 else MK w,
            by simp [hmark', set_arrOf], ?_⟩,
          fun i => if i = C.frames.length then σ'.vars "eu" else SU i,
          fun i => if i = C.frames.length then σ'.vars "ev" else SV i,
          fun i => if i = C.frames.length then 0 else SP i,
          by simp [hstkU', set_arrOf], by simp [hstkV', set_arrOf],
          by simp [hstkP', set_arrOf], ?_⟩
        · intro w hw
          simp only [marked_cons, chosen_false, Finset.mem_insert]
          by_cases hweu : w = σ'.vars "eu"
          · subst hweu
            simp
          · have hne : ¬ ((⟨w, hw⟩ : Fin n) = ⟨σ'.vars "eu", heu'⟩) := by
              simp only [Fin.mk.injEq]; exact hweu
            simp only [if_neg hweu, hne, false_or]
            exact hMK w hw
        · intro i hi
          simp only [List.length_cons] at hi
          rcases Nat.lt_or_ge i C.frames.length with hlt | hge
          · obtain ⟨h1, h2, h3⟩ := hstk i hlt
            refine ⟨?_, ?_, ?_⟩ <;>
              simp only [if_neg (show ¬ i = C.frames.length by omega),
                reverse_getElem_lt _ hlt]
            exacts [h1, h2, h3]
          · have hif : i = C.frames.length := by omega
            subst hif
            refine ⟨?_, ?_, ?_⟩ <;> simp
      · exact inv_push hInv hmode hbpos hadjuv (not_mem_of_indicator_eq hMK heu' hMKeu)
          (not_mem_of_indicator_eq hMK hev' hMKev)
      · rw [hpotC]; exact pot_push hbpos _ _ _ _

/-- **Backtrack.** From a represented state in mode `1`, the backtrack
body reaches a represented state whose configuration still satisfies the
invariant and whose potential has dropped, in constant time. -/
theorem backtrackBody_run (h2B : 2 < B) (hnB : n < B) (hkB : k < B)
    {C : Config n} {τ : Env} (hRep : Rep n m k O T C τ)
    (hInv : Inv G k C) (hmode : C.mode = 1) :
    ∃ (C' : Config n) (τ' : Env) (K : ℕ),
      Run B backtrackBody τ τ' K ∧ Rep n m k O T C' τ' ∧ Inv G k C' ∧
      pot C' + 1 ≤ pot C ∧ K ≤ 96 ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out := by
  obtain ⟨hm2, hoff, htgt, hmd, hbud, hans, htop, ⟨MK, hmark, hMK⟩,
    SU, SV, SP, hstkU, hstkV, hstkP, hstk⟩ := hRep
  have hlen : C.bud + C.frames.length = k := hInv.2.1
  have hheal : Healthy C.frames := hInv.2.2.1
  have hbudB : C.bud < B := by omega
  have hfrlB : C.frames.length < B := by omega
  have hpotC : pot C = pot (⟨C.frames, 1, C.bud, C.ans⟩ : Config n) := by
    simp [pot, hmode]
  rcases hfrs : C.frames with _ | ⟨f, fs⟩
  · -- **Failure exit.** The stack is empty and no alternative is left.
    rw [hfrs] at htop
    refine ⟨⟨C.frames, 2, C.bud, 0⟩, (τ.setVar "ans" 0).setVar "mode" 2, 96,
      ?_, ?_, ?_, ?_, le_rfl, by simp, by simp⟩
    · refine (Run.ite_true (by simp [htop]; omega)
        (Run.seq (Run.assign (v := 0) (by simp; omega))
          (Run.assign (v := 2) (by simp; omega)))).mono ?_
      simp
    · exact ⟨by simp [hm2], by simp [hoff], by simp [htgt], by simp, by simp [hbud],
        by simp, by simp [htop, hfrs], ⟨MK, by simp [hmark], hMK⟩,
        SU, SV, SP, by simp [hstkU], by simp [hstkV], by simp [hstkP], hstk⟩
    · exact inv_fail hInv hmode hfrs
    · rw [hpotC]; exact pot_fail _ _ _
  · rw [hfrs] at hMK htop hlen hheal
    simp only [hfrs] at hstk
    obtain ⟨u, v, ph⟩ := f
    have hfl : fs.length < k := by simp at hlen; omega
    have huB : (u : ℕ) < B := by have := u.isLt; omega
    have hvB : (v : ℕ) < B := by have := v.isLt; omega
    have htop' : τ.vars "top" = fs.length + 1 := by simpa using htop
    obtain ⟨hSU, hSV, hSP⟩ := hstk fs.length (by simp)
    rw [reverse_getElem_top] at hSU hSV hSP
    have hcpu : (Expr.get "stkU" (.sub (.var "top") (.lit 1))).evalB B τ
        = some (u : ℕ) := by
      simp [htop', hstkU, getElem?_arrOf SU hfl, hSU]
      omega
    have hcpv : (Expr.get "stkV" (.sub (.var "top") (.lit 1))).evalB B
        (τ.setVar "pu" (u : ℕ)) = some (v : ℕ) := by
      simp [htop', hstkV, getElem?_arrOf SV hfl, hSV]
      omega
    have htopf : (Cond.eq (Expr.var "top") (.lit 0)).evalB B τ = some false := by
      simp [htop']
      omega
    cases ph
    · -- **Flip.** The top frame's stored branch becomes the active one.
      refine ⟨⟨Frame.mk u v true :: fs, 0, C.bud, C.ans⟩,
        (((((τ.setVar "pu" (u : ℕ)).setVar "pv" (v : ℕ)).setArr "mark" (u : ℕ) 0).setArr
          "mark" (v : ℕ) 1).setArr "stkP" fs.length 1).setVar "mode" 0,
        96, ?_, ?_, ?_, ?_, le_rfl, by simp, by simp⟩
      · refine (Run.ite_false htopf (Run.seq (Run.assign (v := (u : ℕ)) hcpu)
          (Run.seq (Run.assign (v := (v : ℕ)) hcpv)
            (Run.ite_true (by
                simp [htop', hstkP, getElem?_arrOf SP hfl, hSP]; omega)
              (Run.seq (Run.store (idx := (u : ℕ)) (v := 0) (by simp; omega)
                  (by simp; omega) (by simp [hmark]))
                (Run.seq (Run.store (idx := (v : ℕ)) (v := 1) (by simp; omega)
                    (by simp; omega) (by simp [hmark]))
                  (Run.seq (Run.store (idx := fs.length) (v := 1)
                      (by simp [htop']; omega) (by simp; omega)
                      (by simpa [hstkP] using hfl))
                    (Run.assign (v := 0) (by simp; omega))))))))).mono ?_
        simp
      · refine ⟨by simp [hm2], by simp [hoff], by simp [htgt], by simp, by simp [hbud],
          by simp [hans], by simp [htop'], ⟨fun w => if w = (v : ℕ) then 1 else
            if w = (u : ℕ) then 0 else MK w, by simp [hmark, set_arrOf], ?_⟩,
          SU, SV, fun i => if i = fs.length then 1 else SP i,
          by simp [hstkU], by simp [hstkV], by simp [hstkP, set_arrOf], ?_⟩
        · intro w hw
          dsimp only
          simp only [mem_marked_flip hheal ⟨w, hw⟩]
          by_cases hwv : w = (v : ℕ)
          · subst hwv
            simp [Fin.ext_iff]
          · have h1 : ¬ ((⟨w, hw⟩ : Fin n) = v) := by
              simp only [Fin.ext_iff]; exact hwv
            by_cases hwu : w = (u : ℕ)
            · subst hwu
              simp [Fin.ext_iff, hwv]
            · have h2 : (⟨w, hw⟩ : Fin n) ≠ u := by
                simp only [ne_eq, Fin.ext_iff]; exact hwu
              simp only [if_neg hwv, if_neg hwu]
              rw [hMK w hw]
              simp [h1, h2]
        · intro i hi
          simp only [List.length_cons] at hi
          rcases Nat.lt_or_ge i fs.length with hlt | hge
          · obtain ⟨h1, h2, h3⟩ := hstk i (by simp; omega)
            rw [reverse_getElem_lt _ hlt] at h1 h2 h3
            refine ⟨?_, ?_, ?_⟩ <;>
              simp only [if_neg (show ¬ i = fs.length by omega), reverse_getElem_lt _ hlt]
            exacts [h1, h2, h3]
          · have hif : i = fs.length := by omega
            subst hif
            refine ⟨?_, ?_, ?_⟩ <;> simp [hSU, hSV]
      · exact inv_flip hInv hmode hfrs
      · rw [hpotC, hfrs]; exact pot_flip _ _ _
    · -- **Pop.** The top frame is exhausted: its mark and its unit come back.
      refine ⟨⟨fs, 1, C.bud + 1, C.ans⟩,
        ((((τ.setVar "pu" (u : ℕ)).setVar "pv" (v : ℕ)).setArr "mark" (v : ℕ) 0).setVar
          "bud" (C.bud + 1)).setVar "top" fs.length,
        96, ?_, ?_, ?_, ?_, le_rfl, by simp, by simp⟩
      · refine (Run.ite_false htopf (Run.seq (Run.assign (v := (u : ℕ)) hcpu)
          (Run.seq (Run.assign (v := (v : ℕ)) hcpv)
            (Run.ite_false (by
                simp [htop', hstkP, getElem?_arrOf SP hfl, hSP]; omega)
              (Run.seq (Run.store (idx := (v : ℕ)) (v := 0) (by simp; omega)
                  (by simp; omega) (by simp [hmark]))
                (Run.seq (Run.assign (v := C.bud + 1) (by simp [hbud]; omega))
                  (Run.assign (v := fs.length) (by simp [htop']; omega)))))))).mono ?_
        simp
      · refine ⟨by simp [hm2], by simp [hoff], by simp [htgt], by simp [hmd, hmode],
          by simp, by simp [hans], by simp,
          ⟨fun w => if w = (v : ℕ) then 0 else MK w, by simp [hmark, set_arrOf], ?_⟩,
          SU, SV, SP, by simp [hstkU], by simp [hstkV], by simp [hstkP], ?_⟩
        · intro w hw
          dsimp only
          simp only [mem_marked_pop hheal ⟨w, hw⟩]
          by_cases hwv : w = (v : ℕ)
          · subst hwv
            simp
          · have h1 : (⟨w, hw⟩ : Fin n) ≠ v := by
              simp only [ne_eq, Fin.ext_iff]; exact hwv
            simp only [if_neg hwv]
            rw [hMK w hw]
            simp [h1]
        · intro i hi
          have hi' : i < fs.length := hi
          obtain ⟨h1, h2, h3⟩ := hstk i (by simp; omega)
          rw [reverse_getElem_lt _ hi'] at h1 h2 h3
          exact ⟨h1, h2, h3⟩
      · exact inv_pop hInv hmode hfrs
      · rw [hpotC, hfrs]; exact pot_pop _ _ _

/-- **One turn of the outer loop.** The mode dispatches; either way the
invariant survives, the potential drops, and the cost is bounded by the
descend case. -/
theorem outerBody_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ j < 2 * m, T j = target g j)
    (h2B : 2 < B) (hnB : n < B) (hmB : 2 * m < B) (hkB : k < B)
    {C : Config n} {τ : Env} (hRep : Rep n m k O T C τ)
    (hInv : Inv G k C) (hmode : C.mode < 2) :
    ∃ (C' : Config n) (τ' : Env) (K : ℕ),
      Run B outerBody τ τ' K ∧ Rep n m k O T C' τ' ∧ Inv G k C' ∧
      pot C' + 1 ≤ pot C ∧ K ≤ 100 * m + 50 * n + 100 ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out := by
  have hmd : τ.vars "mode" = C.mode := hRep.2.2.2.1
  by_cases h0 : C.mode = 0
  · obtain ⟨C', τ', K, hrun, hRep', hInv', hpot, hK, hi, ho⟩ :=
      descendBody_run hg hm hO hT h2B hnB hmB hkB hRep hInv h0
    refine ⟨C', τ', 1 + (Cond.eq (Expr.var "mode") (Expr.lit 0)).size + K,
      Run.ite_true (by simp [hmd, h0]; omega) hrun, hRep', hInv', hpot, ?_, hi, ho⟩
    simp only [size_condEq, size_var, size_lit]
    omega
  · have h1 : C.mode = 1 := by omega
    obtain ⟨C', τ', K, hrun, hRep', hInv', hpot, hK, hi, ho⟩ :=
      backtrackBody_run h2B hnB hkB hRep hInv h1
    refine ⟨C', τ', 1 + (Cond.eq (Expr.var "mode") (Expr.lit 0)).size + K,
      Run.ite_false (by simp [hmd, h1]; omega) hrun, hRep', hInv', hpot, ?_, hi, ho⟩
    simp only [size_condEq, size_var, size_lit]
    omega

/-! ### The loop

One application of `Run.while_pot`. The invariant is "some
configuration is represented and satisfies `Inv`, and the tapes are
untouched"; the potential is the numeric one, scaled by the cost of a
turn. Each turn pays `1 + 3` for the test and at most `100m + 50n +
100` for the body, and buys one unit of `pot`, so the factor `100m +
50n + 104` covers it. -/

/-- **The search loop.** From a represented state satisfying the
invariant, the outer loop reaches a represented, invariant state in
mode `2`, in at most `(100m + 50n + 104) · pot C₀ + 4` steps. -/
theorem searchLoop_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ j < 2 * m, T j = target g j)
    (h2B : 2 < B) (hnB : n < B) (hmB : 2 * m < B) (hkB : k < B)
    {C₀ : Config n} {σ : Env} (hRep : Rep n m k O T C₀ σ) (hInv : Inv G k C₀) :
    ∃ (C' : Config n) (τ' : Env) (K : ℕ),
      Run B (.while (.lt (.var "mode") (.lit 2)) outerBody) σ τ' K ∧
      Rep n m k O T C' τ' ∧ Inv G k C' ∧ C'.mode = 2 ∧
      τ'.inp = σ.inp ∧ τ'.out = σ.out ∧
      K ≤ (100 * m + 50 * n + 104) * pot C₀ + 4 := by
  -- the test always evaluates: the mode is at most `2`, and `2` is a word
  have hdef : ∀ τ : Env,
      (∃ C, Rep n m k O T C τ ∧ Inv G k C ∧ τ.inp = σ.inp ∧ τ.out = σ.out) →
      ∃ v, (Cond.lt (.var "mode") (.lit 2)).evalB B τ = some v := by
    rintro τ ⟨C, hRepC, hInvC, -, -⟩
    have hmd : τ.vars "mode" = C.mode := hRepC.2.2.2.1
    have := hInvC.1
    exact evalB_condLt_var_lit (by omega) (by omega)
  -- a turn: the body runs, the invariant survives, the potential pays
  have hstep : ∀ τ : Env,
      (∃ C, Rep n m k O T C τ ∧ Inv G k C ∧ τ.inp = σ.inp ∧ τ.out = σ.out) →
      (Cond.lt (.var "mode") (.lit 2)).evalB B τ = some true →
      ∃ τ'' K, Run B outerBody τ τ'' K ∧
        (∃ C, Rep n m k O T C τ'' ∧ Inv G k C ∧ τ''.inp = σ.inp ∧ τ''.out = σ.out) ∧
        1 + (Cond.lt (Expr.var "mode") (Expr.lit 2)).size + K +
            (100 * m + 50 * n + 104) *
              potN (τ''.vars "mode") (τ''.vars "bud") (phasesOf τ'') ≤
          (100 * m + 50 * n + 104) *
            potN (τ.vars "mode") (τ.vars "bud") (phasesOf τ) := by
    rintro τ ⟨C, hRepC, hInvC, hinp, hout⟩ hc
    have hc' := Cond.eval_of_evalB hc
    have hlen : C.bud + C.frames.length = k := hInvC.2.1
    have hmd : τ.vars "mode" = C.mode := hRepC.2.2.2.1
    have hmode : C.mode < 2 := by
      simp only [Cond.eval, Expr.eval, Option.bind_some, Option.map_some,
        Option.some.injEq, decide_eq_true_eq, hmd] at hc'
      exact hc'
    obtain ⟨C', τ'', K, hrunb, hRep', hInv', hpot, hK, hi, ho⟩ :=
      outerBody_run hg hm hO hT h2B hnB hmB hkB hRepC hInvC hmode
    refine ⟨τ'', K, hrunb, ⟨C', hRep', hInv', by rw [hi, hinp], by rw [ho, hout]⟩, ?_⟩
    have hlen' : C'.bud + C'.frames.length = k := hInv'.2.1
    have e1 := potN_eq hRep' (show C'.frames.length ≤ k by omega)
    have e2 := potN_eq hRepC (show C.frames.length ≤ k by omega)
    have hmul : (100 * m + 50 * n + 104) * (pot C' + 1) ≤
        (100 * m + 50 * n + 104) * pot C := Nat.mul_le_mul_left _ hpot
    rw [Nat.mul_succ] at hmul
    rw [e1, e2]
    simp only [size_condLt, size_var, size_lit]
    omega
  obtain ⟨τ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_pot (B := B) (b := Cond.lt (.var "mode") (.lit 2)) (c := outerBody)
      (fun τ => ∃ C, Rep n m k O T C τ ∧ Inv G k C ∧ τ.inp = σ.inp ∧ τ.out = σ.out)
      (fun τ => (100 * m + 50 * n + 104) *
        potN (τ.vars "mode") (τ.vars "bud") (phasesOf τ))
      hdef hstep ⟨C₀, hRep, hInv, rfl, rfl⟩
  -- exit: the test is false and `Inv` caps the mode, so the mode is `2`
  obtain ⟨C', hRep', hInv', hinp', hout'⟩ := hI'
  have hfalse' := Cond.eval_of_evalB hfalse
  have hmd' : τ'.vars "mode" = C'.mode := hRep'.2.2.2.1
  have hmode' : C'.mode = 2 := by
    simp only [Cond.eval, Expr.eval, Option.bind_some, Option.map_some,
      Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt, hmd'] at hfalse'
    have := hInv'.1
    omega
  have hlen₀ : C₀.frames.length ≤ k := by have := hInv.2.1; omega
  have hΦ₀ := potN_eq hRep hlen₀
  refine ⟨C', τ', K, hrun, hRep', hInv', hmode', hinp', hout', ?_⟩
  simp only [size_condLt, size_var, size_lit, hΦ₀] at hpay
  omega

end Lax11Proofs.VC
