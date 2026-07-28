import Lax15Proofs.Config
import Lax15Proofs.Program

/-!
The inner loops, run.

`Rep` says what the arrays and the scalars hold when the pure
configuration is `C`. Three orientation decisions are fixed here and
every later proof mirrors them.

* The **trail array** grows upwards: the bottom frame's marks first,
  then the frame above it, and so on, each frame's marks in the order it
  made them. The pure `trail` of `Config.lean` is *top*-first, so the
  array holds `trailArr fs = trail fs.reverse`, the orientation in which
  a push is an append at the end and a pop a truncation. Its entries are
  vertex numbers, so the tie is stated against `trailVals`, the same
  list of `ℕ`.
* The **stack arrays** are bottom-up, as in the `2^k` driver: entry `i`
  is the frame `i` levels above the bottom, which is
  `C.frames.reverse[i]`. Frame `i`'s stored trail base is `base C.frames
  i`, the length of everything the frames below it marked.
* The **mark array** is the indicator of `marked C.frames`, over the
  extent `n`; `Indicator` names that tie once, because the two scans and
  the unwind loop each move it.

The three loop lemmas below are the three `while`s the body of the
outer loop contains. The descend scan is stated at the level of `Rep` —
it changes no array and no scalar the configuration is read out of, so
the configuration it represents is literally unchanged. The flip's row
scan and the pop's unwind loop are stated at the level of the arrays,
as `VCScan` states its scan: they run in the middle of a body, from a
state that represents no configuration at all — the marks are already
those of the frames below, while the frame itself is still on the
stack — so `Rep` is not available to them, and the caller reassembles
it. Their conclusions are shaped for `step_flip`, `step_flip_infeasible`
and `step_pop`, which ask for a nodup list with the right `toFinset` and
nothing more.

The costs are all of the form `numeral · (n + 2m + 1)`, which is the
shape the assembly wants: the length of the input word bounds `n + 2m`.
-/

namespace Lax15Proofs.VC

open Lax13.Ram Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax11Proofs.CC

variable {g : List ℕ} {n m k B : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
  {M : Finset (Fin n)}

/-! ### The trail, as the machine holds it -/

/-- The trail in array order: the frames bottom-first, each frame's
marks in the order it made them. The pure `trail` is top-first, so this
is the trail of the reversed stack — the orientation in which a push
appends and a pop truncates. -/
def trailArr (fs : List (Frame n)) : List (Fin n) := trail fs.reverse

/-- The trail array as the machine holds it: vertex numbers. -/
def trailVals (fs : List (Frame n)) : List ℕ := (trailArr fs).map Fin.val

@[simp] theorem trailArr_nil : trailArr ([] : List (Frame n)) = [] := rfl

@[simp] theorem trailArr_cons (f : Frame n) (fs : List (Frame n)) :
    trailArr (f :: fs) = trailArr fs ++ f.S := by
  simp [trailArr, trail]

@[simp] theorem length_trailArr (fs : List (Frame n)) :
    (trailArr fs).length = (trail fs).length := by
  induction fs with
  | nil => simp
  | cons f fs ih => simp [ih]; omega

@[simp] theorem toFinset_trailArr (fs : List (Frame n)) :
    (trailArr fs).toFinset = marked fs := by
  induction fs with
  | nil => simp
  | cons f fs ih => simp [ih, Finset.union_comm]

@[simp] theorem trailVals_nil : trailVals ([] : List (Frame n)) = [] := rfl

@[simp] theorem trailVals_cons (f : Frame n) (fs : List (Frame n)) :
    trailVals (f :: fs) = trailVals fs ++ f.S.map Fin.val := by
  simp [trailVals]

@[simp] theorem length_trailVals (fs : List (Frame n)) :
    (trailVals fs).length = (trail fs).length := by
  simp [trailVals]

/-- The trail array has no repetitions, in array order too. -/
theorem Healthy.trailArr_nodup {fs : List (Frame n)} (h : Healthy G k fs) :
    (trailArr fs).Nodup := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    rw [trailArr_cons, List.nodup_append]
    refine ⟨ih h.tail, h.2.2.1, fun x hx y hy hxy => ?_⟩
    exact Finset.disjoint_left.1 h.head_disjoint (List.mem_toFinset.2 hy)
      (by rw [← toFinset_trailArr]; exact List.mem_toFinset.2 (hxy ▸ hx))

/-- The trail height a frame found when it was pushed: the length of
everything the frames below it marked. Frames are numbered from the
bottom, as the stack arrays number them. -/
def base (fs : List (Frame n)) (i : ℕ) : ℕ := (trail (fs.drop (fs.length - i))).length

/-- The top frame's base is the trail below it. -/
@[simp] theorem base_top (f : Frame n) (fs : List (Frame n)) :
    base (f :: fs) fs.length = (trail fs).length := by
  simp [base]

/-- A push does not disturb the bases of the frames below. -/
theorem base_cons {f : Frame n} {fs : List (Frame n)} {i : ℕ} (hi : i ≤ fs.length) :
    base (f :: fs) i = base fs i := by
  simp only [base, List.length_cons]
  congr 2
  rw [show fs.length + 1 - i = (fs.length - i) + 1 by omega, List.drop_succ_cons]

/-! ### The arrays -/

/-- The mark array holds the indicator of a set of vertices. -/
def Indicator (M : Finset (Fin n)) (MK : ℕ → ℕ) : Prop :=
  ∀ w (hw : w < n), MK w = if (⟨w, hw⟩ : Fin n) ∈ M then 1 else 0

/-- An indicator that is not `0` witnesses membership. -/
theorem mem_of_indicator_ne {MK : ℕ → ℕ} (hMK : Indicator M MK) {w : ℕ} (hw : w < n)
    (h : MK w ≠ 0) : (⟨w, hw⟩ : Fin n) ∈ M := by
  by_contra hmem
  rw [hMK w hw, if_neg hmem] at h
  exact h rfl

/-- An indicator that is `0` witnesses non-membership. -/
theorem not_mem_of_indicator_eq {MK : ℕ → ℕ} (hMK : Indicator M MK) {w : ℕ} (hw : w < n)
    (h : MK w = 0) : (⟨w, hw⟩ : Fin n) ∉ M := by
  intro hmem
  rw [hMK w hw, if_pos hmem] at h
  exact absurd h one_ne_zero

/-- The indicator array is a word array as soon as `1` is a word. -/
theorem indicator_lt {MK : ℕ → ℕ} (h1B : 1 < B) (hMK : Indicator M MK) {w : ℕ}
    (hw : w < n) : MK w < B := by
  rw [hMK w hw]
  split <;> omega

/-- The indicator, read against the marking of the machine. -/
theorem indicator_zero_iff {MK : ℕ → ℕ} (hMK : Indicator M MK) {w : ℕ} (hw : w < n) :
    MK w = 0 ↔ w ∉ markedVals M := by
  rw [hMK w hw, mem_markedVals_iff hw]
  split <;> simp_all

/-- Setting one cell of an indicator array to `1` is inserting one
vertex into the set it indicates. -/
theorem indicator_set_one {MK : ℕ → ℕ} (hMK : Indicator M MK) {w : ℕ} (hw : w < n) :
    Indicator (insert (⟨w, hw⟩ : Fin n) M) (fun x => if x = w then 1 else MK x) := by
  intro x hx
  by_cases hxw : x = w
  · subst hxw
    simp
  · simp only [if_neg hxw, hMK x hx, Finset.mem_insert]
    have : ¬ ((⟨x, hx⟩ : Fin n) = ⟨w, hw⟩) := by simp only [Fin.mk.injEq]; exact hxw
    simp [this]

/-- Setting one cell of an indicator array to `0` is erasing one vertex
from the set it indicates. -/
theorem indicator_set_zero {MK : ℕ → ℕ} (hMK : Indicator M MK) {w : ℕ} (hw : w < n) :
    Indicator (M.erase (⟨w, hw⟩ : Fin n)) (fun x => if x = w then 0 else MK x) := by
  intro x hx
  by_cases hxw : x = w
  · subst hxw
    simp
  · simp only [if_neg hxw, hMK x hx, Finset.mem_erase]
    have : ¬ ((⟨x, hx⟩ : Fin n) = ⟨w, hw⟩) := by simp only [Fin.mk.injEq]; exact hxw
    simp [this]

/-! ### Representation -/

/-- The arrays and the scalars represent the configuration `C`: the CSR
arrays hold the encoding, the mode, budget, answer, stack height and
trail height are the configuration's, the mark array indicates the
marking, the trail array holds the trail bottom-first, and the four
stack arrays list the frames bottom-up with their vertex, stored
budget, trail base and phase. -/
def Rep (n m : ℕ) (O T : ℕ → ℕ) (C : Config n) (τ : Env) : Prop :=
  τ.vars "m2" = 2 * m ∧
  τ.arrs "off" = arrOf (n + 1) O ∧ τ.arrs "tgt" = arrOf (2 * m) T ∧
  τ.vars "mode" = C.mode ∧ τ.vars "bud" = C.bud ∧ τ.vars "ans" = C.ans ∧
  τ.vars "top" = C.frames.length ∧ τ.vars "tt" = (trail C.frames).length ∧
  (∃ MK, τ.arrs "mark" = arrOf n MK ∧ Indicator (marked C.frames) MK) ∧
  (∃ TR, τ.arrs "trail" = arrOf (n + 1) TR ∧
    ∀ i < (trail C.frames).length, TR i = (trailVals C.frames).getD i 0) ∧
  (∃ SV SB ST SP, τ.arrs "stkV" = arrOf (n + 1) SV ∧ τ.arrs "stkB" = arrOf (n + 1) SB ∧
    τ.arrs "stkT" = arrOf (n + 1) ST ∧ τ.arrs "stkP" = arrOf (n + 1) SP ∧
    ∀ i (hi : i < C.frames.length),
      SV i = ((C.frames.reverse[i]'(by simpa using hi)).v : ℕ) ∧
      SB i = (C.frames.reverse[i]'(by simpa using hi)).b ∧
      ST i = base C.frames i ∧
      SP i = if (C.frames.reverse[i]'(by simpa using hi)).phase then 1 else 0)

variable {C : Config n} {τ : Env}

theorem Rep.m2 (h : Rep n m O T C τ) : τ.vars "m2" = 2 * m := h.1
theorem Rep.off (h : Rep n m O T C τ) : τ.arrs "off" = arrOf (n + 1) O := h.2.1
theorem Rep.tgt (h : Rep n m O T C τ) : τ.arrs "tgt" = arrOf (2 * m) T := h.2.2.1
theorem Rep.mode (h : Rep n m O T C τ) : τ.vars "mode" = C.mode := h.2.2.2.1
theorem Rep.bud (h : Rep n m O T C τ) : τ.vars "bud" = C.bud := h.2.2.2.2.1
theorem Rep.ans (h : Rep n m O T C τ) : τ.vars "ans" = C.ans := h.2.2.2.2.2.1
theorem Rep.top (h : Rep n m O T C τ) : τ.vars "top" = C.frames.length := h.2.2.2.2.2.2.1
theorem Rep.tt (h : Rep n m O T C τ) : τ.vars "tt" = (trail C.frames).length :=
  h.2.2.2.2.2.2.2.1

theorem Rep.mark (h : Rep n m O T C τ) :
    ∃ MK, τ.arrs "mark" = arrOf n MK ∧ Indicator (marked C.frames) MK :=
  h.2.2.2.2.2.2.2.2.1

theorem Rep.trail (h : Rep n m O T C τ) :
    ∃ TR, τ.arrs "trail" = arrOf (n + 1) TR ∧
      ∀ i < (trail C.frames).length, TR i = (trailVals C.frames).getD i 0 :=
  h.2.2.2.2.2.2.2.2.2.1

theorem Rep.stk (h : Rep n m O T C τ) :
    ∃ SV SB ST SP, τ.arrs "stkV" = arrOf (n + 1) SV ∧ τ.arrs "stkB" = arrOf (n + 1) SB ∧
      τ.arrs "stkT" = arrOf (n + 1) ST ∧ τ.arrs "stkP" = arrOf (n + 1) SP ∧
      ∀ i (hi : i < C.frames.length),
        SV i = ((C.frames.reverse[i]'(by simpa using hi)).v : ℕ) ∧
        SB i = (C.frames.reverse[i]'(by simpa using hi)).b ∧
        ST i = base C.frames i ∧
        SP i = if (C.frames.reverse[i]'(by simpa using hi)).phase then 1 else 0 :=
  h.2.2.2.2.2.2.2.2.2.2

/-- Representation is a statement about six scalars and eight arrays,
so a phase that leaves those alone transports it. This is what makes
the descend scan a `Rep`-level lemma: it moves nine working scalars and
no array. -/
theorem Rep.of_vars_eq {τ' : Env} (h : Rep n m O T C τ) (harrs : τ'.arrs = τ.arrs)
    (hm2 : τ'.vars "m2" = τ.vars "m2") (hmode : τ'.vars "mode" = τ.vars "mode")
    (hbud : τ'.vars "bud" = τ.vars "bud") (hans : τ'.vars "ans" = τ.vars "ans")
    (htop : τ'.vars "top" = τ.vars "top") (htt : τ'.vars "tt" = τ.vars "tt") :
    Rep n m O T C τ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨by rw [hm2, h1], by rw [harrs, h2], by rw [harrs, h3], by rw [hmode, h4],
    by rw [hbud, h5], by rw [hans, h6], by rw [htop, h7], by rw [htt, h8],
    by rw [harrs]; exact h9, by rw [harrs]; exact h10, by rw [harrs]; exact h11⟩

/-! ### Reading a loop condition -/

/-- The loop condition of every loop here compares two scalars; this is
what its truth value says. -/
theorem lt_of_condLt_true {x y : String} {ρ : Env}
    (h : (Cond.lt (.var x) (.var y)).evalB B ρ = some true) : ρ.vars x < ρ.vars y := by
  simp only [evalB_condLt_iff, evalB_var_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

/-- And this is what its falsity says. -/
theorem le_of_condLt_false {x y : String} {ρ : Env}
    (h : (Cond.lt (.var x) (.var y)).evalB B ρ = some false) : ρ.vars y ≤ ρ.vars x := by
  simp only [evalB_condLt_iff, evalB_var_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  have := hr.symm
  simp only [decide_eq_false_iff_not, not_lt] at this
  exact this

/-! ### The pop's unwind loop

The loop that takes the top frame's marks back off. It runs from a
state whose mark array indicates `S ∪ M` — the frame's own marks
together with everything below it — and whose trail array holds `S` at
`[tb, tb + |S|)`, and it leaves the mark array indicating `M` alone and
the trail height back at `tb`. The trail array itself is not cleared:
nothing ever reads above the height. -/

/-- The unwind loop of `popFrame`, on its own. -/
def unwindLoop : Com :=
  .while (.lt (.var "tb") (.var "tt"))
    (.seq (.assign "tt" (.sub (.var "tt") (.lit 1)))
      (.store "mark" (.get "trail" (.var "tt")) (.lit 0)))

theorem popFrame_eq :
    popFrame = .seq unwindLoop
      (.seq (.assign "bud" (.var "pb")) (.assign "top" (.sub (.var "top") (.lit 1)))) := rfl

/-- The invariant of the unwind loop: `i` of the frame's marks are still
on, the mark array indicates them together with what is below, and
nothing but the mark array and the trail height has moved. -/
def UnwindInv {n : ℕ} (tb : ℕ) (M : Finset (Fin n)) (S : List (Fin n)) (σ τ : Env) : Prop :=
  (∀ y, y ≠ "tt" → τ.vars y = σ.vars y) ∧ (∀ a, a ≠ "mark" → τ.arrs a = σ.arrs a) ∧
    τ.inp = σ.inp ∧ τ.out = σ.out ∧
    ∃ i, i ≤ S.length ∧ τ.vars "tt" = tb + i ∧
      ∃ MK, τ.arrs "mark" = arrOf n MK ∧ Indicator ((S.take i).toFinset ∪ M) MK

/-- Taking the last of `i + 1` marks off the set they indicate. The
frame marked a nodup list disjoint from what is below it, so the vertex
erased is in neither of the two parts that stay. -/
theorem take_succ_erase {S : List (Fin n)} (hnd : S.Nodup) (hdisj : Disjoint S.toFinset M)
    {i : ℕ} (hi : i < S.length) :
    (((S.take (i + 1)).toFinset ∪ M).erase (S[i]'hi)) = (S.take i).toFinset ∪ M := by
  have hsplit : S.take (i + 1) = S.take i ++ [S[i]'hi] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]
    rfl
  have hnotin : (S[i]'hi) ∉ (S.take i) := by
    intro hmem
    have hnd' : (S.take (i + 1)).Nodup := hnd.sublist (List.take_sublist _ _)
    rw [hsplit, List.nodup_append] at hnd'
    exact hnd'.2.2 _ hmem _ (by simp) rfl
  have hnotM : (S[i]'hi) ∉ M :=
    Finset.disjoint_left.1 hdisj (List.mem_toFinset.2 (List.getElem_mem hi))
  have hins : (S.take (i + 1)).toFinset = insert (S[i]'hi) ((S.take i).toFinset) := by
    ext x
    simp only [hsplit, List.toFinset_append, Finset.mem_union, Finset.mem_insert,
      List.mem_toFinset, List.mem_singleton]
    tauto
  rw [hins, Finset.insert_union, Finset.erase_insert]
  simp only [Finset.mem_union, List.mem_toFinset]
  rintro (hx | hx)
  · exact hnotin hx
  · exact hnotM hx

/-- **The unwind loop.** From a state whose marks are the frame's
together with what is below it, and whose trail holds the frame's marks
above `tb`, the loop returns the marks to what is below and the trail
height to `tb`, in time linear in the number of vertices. -/
theorem unwind_run (h1B : 1 < B) (hnB : n < B) {S : List (Fin n)} {MK TR : ℕ → ℕ}
    {tb : ℕ} {τ : Env} (hnd : S.Nodup) (hdisj : Disjoint S.toFinset M)
    (hmark : τ.arrs "mark" = arrOf n MK) (hMK : Indicator (S.toFinset ∪ M) MK)
    (htrail : τ.arrs "trail" = arrOf (n + 1) TR)
    (hTR : ∀ i (hi : i < S.length), TR (tb + i) = ((S[i]'hi : Fin n) : ℕ))
    (htb : τ.vars "tb" = tb) (htt : τ.vars "tt" = tb + S.length)
    (hbnd : tb + S.length ≤ n) :
    ∃ (τ' : Env) (MK' : ℕ → ℕ) (K : ℕ), Run B unwindLoop τ τ' K ∧
      τ'.vars "tt" = tb ∧ τ'.arrs "mark" = arrOf n MK' ∧ Indicator M MK' ∧
      (∀ a, a ≠ "mark" → τ'.arrs a = τ.arrs a) ∧ (∀ y, y ≠ "tt" → τ'.vars y = τ.vars y) ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out ∧ K ≤ 50 * (n + 1) := by
  have hstep : ∀ ρ, UnwindInv tb M S τ ρ →
      (Cond.lt (.var "tb") (.var "tt")).evalB B ρ = some true →
      ∃ ρ' K, Run B (.seq (.assign "tt" (.sub (.var "tt") (.lit 1)))
          (.store "mark" (.get "trail" (.var "tt")) (.lit 0))) ρ ρ' K ∧
        UnwindInv tb M S τ ρ' ∧
        1 + (Cond.lt (Expr.var "tb") (Expr.var "tt")).size + K +
          30 * (ρ'.vars "tt" - tb) ≤ 30 * (ρ.vars "tt" - tb) := by
    rintro ρ ⟨hfr, harr, hinp, hout, i, hile, htti, MKi, hmarki, hMKi⟩ hcond
    have htbρ : ρ.vars "tb" = tb := by rw [hfr "tb" (by decide), htb]
    have hlt : tb < ρ.vars "tt" := by
      have := lt_of_condLt_true hcond
      omega
    have hipos : 0 < i := by omega
    set j := i - 1 with hj
    have hjlt : j < S.length := by omega
    have htrρ : ρ.arrs "trail" = arrOf (n + 1) TR := by rw [harr "trail" (by decide), htrail]
    set ρ₁ : Env := ρ.setVar "tt" (tb + j) with hρ₁
    have hSj : ((S[j]'hjlt : Fin n) : ℕ) < n := (S[j]'hjlt).2
    have r₁ : Run B (.assign "tt" (.sub (.var "tt") (.lit 1))) ρ ρ₁ 4 :=
      (Run.assign (v := tb + j) (by simp [htti]; omega)).mono (by simp)
    have hidx : (Expr.get "trail" (.var "tt")).evalB B ρ₁ = some ((S[j]'hjlt : Fin n) : ℕ) := by
      refine evalB_get (k := tb + j) (by simp [hρ₁]; omega) ?_ (by omega)
      rw [hρ₁, arrs_setVar, htrρ, getElem?_arrOf TR (by omega), hTR j hjlt]
    have r₂ : Run B (.store "mark" (.get "trail" (.var "tt")) (.lit 0)) ρ₁
        (ρ₁.setArr "mark" ((S[j]'hjlt : Fin n) : ℕ) 0) 4 :=
      (Run.store hidx (by simp; omega)
        (by rw [hρ₁, arrs_setVar, hmarki, length_arrOf]; exact hSj)).mono (by simp)
    refine ⟨_, _, Run.seq r₁ r₂, ⟨?_, ?_, by simp [hρ₁, hinp], by simp [hρ₁, hout],
      j, by omega, by simp [hρ₁], ?_⟩, ?_⟩
    · intro y hy
      simp only [vars_setArr, hρ₁, vars_setVar, if_neg hy]
      exact hfr y hy
    · intro a ha
      simp only [arrs_setArr, hρ₁, arrs_setVar, if_neg ha]
      exact harr a ha
    · refine ⟨fun x => if x = ((S[j]'hjlt : Fin n) : ℕ) then 0 else MKi x, ?_, ?_⟩
      · rw [arrs_setArr, if_pos rfl, hρ₁, arrs_setVar, hmarki, set_arrOf]
      · have hit : i = j + 1 := by omega
        rw [← take_succ_erase hnd hdisj hjlt]
        have := indicator_set_zero (M := (S.take i).toFinset ∪ M) hMKi hSj
        simpa [hit] using this
    · simp only [size_condLt, size_var]
      simp [hρ₁]
      omega
  obtain ⟨τ', K, hrun, ⟨hfr', harr', hinp', hout', i', hile', htti', MK', hmark', hMK'⟩,
      hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := Cond.lt (.var "tb") (.var "tt"))
      (c := .seq (.assign "tt" (.sub (.var "tt") (.lit 1)))
        (.store "mark" (.get "trail" (.var "tt")) (.lit 0)))
      (UnwindInv tb M S τ) (fun ρ => 30 * (ρ.vars "tt" - tb))
      (fun ρ hρ => by
        obtain ⟨hfr, -, -, -, i, hile, htti, -⟩ := hρ
        refine evalB_condLt_vars ?_ (by omega)
        rw [hfr "tb" (by decide), htb]; omega)
      hstep ⟨fun y _ => rfl, fun a _ => rfl, rfl, rfl, S.length, le_rfl, htt,
        MK, hmark, by simpa using hMK⟩
  have htb' : τ'.vars "tb" = tb := by rw [hfr' "tb" (by decide), htb]
  have hi0 : i' = 0 := by
    have := le_of_condLt_false hfalse
    omega
  subst hi0
  refine ⟨τ', MK', K, hrun, by simpa using htti', hmark', by simpa using hMK',
    harr', hfr', hinp', hout', ?_⟩
  simp only [size_condLt, size_var, htt] at hpay ⊢
  omega

/-! ### The flip's row scan

The loop that marks the whole residual neighbourhood of the top frame's
vertex. It runs over the block of that vertex, marking every target it
has not already marked and pushing it on the trail, so what it appends
is the residual neighbourhood listed once each, in the order the
encoding names it first. A block may name a neighbour twice; the mark
test is what makes the trail segment nodup and its length the residual
degree.

The conclusion hands out that list, its `toFinset` and its length,
which is everything `step_flip` and `step_flip_infeasible` ask of it —
they quantify over any nodup list with the right `toFinset`. -/

/-- The row scan of `flipFrame`, on its own. -/
def rowLoop : Com := .while (.lt (.var "j") (.var "jend")) rowStep

theorem flipFrame_eq :
    flipFrame = .seq (.store "mark" (.var "pv") (.lit 0))
      (.seq (.assign "tt" (.var "tb"))
        (.seq (.assign "bud" (.var "pb"))
          (.seq (.assign "j" (.get "off" (.var "pv")))
            (.seq (.assign "jend" (.get "off" (.add (.var "pv") (.lit 1))))
              (.seq rowLoop
                (.seq (.store "stkP" (.var "sp") (.lit 1))
                  (.seq (.assign "d" (.sub (.var "tt") (.var "tb")))
                    (.ite (.lt (.var "d") (.add (.var "bud") (.lit 1)))
                      (.seq (.assign "bud" (.sub (.var "bud") (.var "d")))
                        (.assign "mode" (.lit 0)))
                      .skip)))))))) := rfl

/-- The invariant of the row scan: the slots below `j` of the block have
contributed the list `l` — their unmarked targets, first occurrence
first — the marks are what was below together with `l`, and the trail
holds `l` above `tb`. -/
def RowInv (g : List ℕ) {n : ℕ} (v : Fin n) (M : Finset (Fin n)) (tb : ℕ) (TR : ℕ → ℕ)
    (σ τ : Env) : Prop :=
  (∀ y, y ≠ "j" → y ≠ "w" → y ≠ "tt" → τ.vars y = σ.vars y) ∧
  (∀ a, a ≠ "mark" → a ≠ "trail" → τ.arrs a = σ.arrs a) ∧
  τ.inp = σ.inp ∧ τ.out = σ.out ∧
  offset g (v : ℕ) ≤ τ.vars "j" ∧ τ.vars "j" ≤ offset g ((v : ℕ) + 1) ∧
  ∃ l : List (Fin n), l.Nodup ∧
    (∀ w : Fin n, w ∈ l ↔ (w ∉ M ∧ ∃ p, offset g (v : ℕ) ≤ p ∧ p < τ.vars "j" ∧
      target g p = (w : ℕ))) ∧
    τ.vars "tt" = tb + l.length ∧
    (∃ MK, τ.arrs "mark" = arrOf n MK ∧ Indicator (M ∪ l.toFinset) MK) ∧
    (∃ TR', τ.arrs "trail" = arrOf (n + 1) TR' ∧ (∀ i < tb, TR' i = TR i) ∧
      ∀ i (hi : i < l.length), TR' (tb + i) = ((l[i]'hi : Fin n) : ℕ))

/-- The trail never outgrows the vertex set: what is on it below `tb`
and what the scan has added are disjoint sets of vertices. -/
theorem length_add_card_le {l : List (Fin n)} (hnd : l.Nodup)
    (hdisj : ∀ w ∈ l, w ∉ M) : M.card + l.length ≤ n := by
  have hd : Disjoint M l.toFinset :=
    Finset.disjoint_right.2 fun x hx => hdisj x (List.mem_toFinset.1 hx)
  have hcard : (M ∪ l.toFinset).card = M.card + l.length := by
    rw [Finset.card_union_of_disjoint hd, List.toFinset_card_of_nodup hnd]
  rw [← hcard]
  simpa using Finset.card_le_univ (M ∪ l.toFinset)

/-- **The row scan.** From a state whose marks are those of the frames
below, positioned at the start of the block of `v`, the loop marks
exactly the residual neighbourhood of `v`, records it on the trail in
first-occurrence order, and raises the trail height by its size. -/
theorem rowLoop_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hT : ∀ j < 2 * m, T j = target g j)
    (h1B : 1 < B) (hnB : n < B) (hmB : 2 * m < B) {v : Fin n} {MK TR : ℕ → ℕ}
    {tb : ℕ} {τ : Env} (hcard : M.card = tb)
    (hmark : τ.arrs "mark" = arrOf n MK) (hMK : Indicator M MK)
    (htrail : τ.arrs "trail" = arrOf (n + 1) TR)
    (htgt : τ.arrs "tgt" = arrOf (2 * m) T)
    (hj : τ.vars "j" = offset g (v : ℕ)) (hjend : τ.vars "jend" = offset g ((v : ℕ) + 1))
    (htt : τ.vars "tt" = tb) :
    ∃ (τ' : Env) (l : List (Fin n)) (MK' TR' : ℕ → ℕ) (K : ℕ), Run B rowLoop τ τ' K ∧
      l.Nodup ∧ l.toFinset = ResNbhd G M v ∧ τ'.vars "tt" = tb + l.length ∧
      τ'.arrs "mark" = arrOf n MK' ∧ Indicator (M ∪ l.toFinset) MK' ∧
      τ'.arrs "trail" = arrOf (n + 1) TR' ∧ (∀ i < tb, TR' i = TR i) ∧
      (∀ i (hi : i < l.length), TR' (tb + i) = ((l[i]'hi : Fin n) : ℕ)) ∧
      (∀ a, a ≠ "mark" → a ≠ "trail" → τ'.arrs a = τ.arrs a) ∧
      (∀ y, y ≠ "j" → y ≠ "w" → y ≠ "tt" → τ'.vars y = τ.vars y) ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out ∧ K ≤ 50 * (n + 2 * m + 1) := by
  have hend : offset g ((v : ℕ) + 1) ≤ 2 * m := by
    have := offset_le hg (show (v : ℕ) + 1 ≤ n from v.2)
    omega
  have hstep : ∀ ρ, RowInv g v M tb TR τ ρ →
      (Cond.lt (.var "j") (.var "jend")).evalB B ρ = some true →
      ∃ ρ' K, Run B rowStep ρ ρ' K ∧ RowInv g v M tb TR τ ρ' ∧
        1 + (Cond.lt (Expr.var "j") (Expr.var "jend")).size + K +
          40 * (offset g ((v : ℕ) + 1) - ρ'.vars "j") ≤
            40 * (offset g ((v : ℕ) + 1) - ρ.vars "j") := by
    rintro ρ ⟨hfr, harr, hinp, hout, hlo, hhi, l, hnd, hmem, htt', ⟨MKl, hmarkl, hMKl⟩,
      ⟨TRl, htraill, hTRlo, hTRhi⟩⟩ hcond
    have hjendρ : ρ.vars "jend" = offset g ((v : ℕ) + 1) := by
      rw [hfr "jend" (by decide) (by decide) (by decide), hjend]
    have hjlt : ρ.vars "j" < offset g ((v : ℕ) + 1) := by
      have := lt_of_condLt_true hcond
      omega
    have hj2m : ρ.vars "j" < 2 * m := by omega
    have htgtρ : ρ.arrs "tgt" = arrOf (2 * m) T := by
      rw [harr "tgt" (by decide) (by decide), htgt]
    have hwn : target g (ρ.vars "j") < n := target_lt' hg v.2 hjlt
    obtain ⟨w, hwval⟩ : ∃ w : Fin n, (w : ℕ) = target g (ρ.vars "j") := ⟨⟨_, hwn⟩, rfl⟩
    have hwlt : (w : ℕ) < n := w.2
    have hTj : T (ρ.vars "j") = (w : ℕ) := by rw [hwval]; exact hT _ hj2m
    set ρ₁ : Env := ρ.setVar "w" (w : ℕ) with hρ₁
    have hmarkl₁ : ρ₁.arrs "mark" = arrOf n MKl := by rw [hρ₁, arrs_setVar, hmarkl]
    have htraill₁ : ρ₁.arrs "trail" = arrOf (n + 1) TRl := by rw [hρ₁, arrs_setVar, htraill]
    have htt₁ : ρ₁.vars "tt" = tb + l.length := by rw [hρ₁]; simpa using htt'
    have r₁ : Run B (.assign "w" (.get "tgt" (.var "j"))) ρ ρ₁ 3 :=
      (Run.assign (v := (w : ℕ)) (evalB_get (k := ρ.vars "j") (evalB_var (by omega))
        (by rw [htgtρ, getElem?_arrOf T hj2m, hTj]) (by omega))).mono (by simp)
    have hdisjl : ∀ x ∈ l, x ∉ M := fun x hx => ((hmem x).1 hx).1
    have hbnd : tb + l.length ≤ n := by rw [← hcard]; exact length_add_card_le hnd hdisjl
    by_cases hMKw : MKl (w : ℕ) = 0
    · -- an unmarked target: it joins the cover and the trail
      have hwnot : w ∉ M ∪ l.toFinset := by
        have := not_mem_of_indicator_eq hMKl hwlt hMKw
        simpa using this
      have hwl : w ∉ l := fun hx => hwnot (Finset.mem_union_right _ (List.mem_toFinset.2 hx))
      have hwM : w ∉ M := fun hx => hwnot (Finset.mem_union_left _ hx)
      have hndapp : (l ++ [w]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hnd, by simp, ?_⟩
        intro a ha b hb hab
        simp only [List.mem_singleton] at hb
        rw [hb] at hab
        subst hab
        exact hwl ha
      have hbnd' : tb + l.length + 1 ≤ n := by
        have := length_add_card_le (M := M) (l := l ++ [w]) hndapp (by
          intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hdisjl x hx
          · exact hwM)
        rw [← hcard]
        simpa using this
      have hc : (Cond.eq (.get "mark" (.var "w")) (.lit 0)).evalB B ρ₁ = some true := by
        refine (evalB_condEq (m := MKl (w : ℕ)) (n := 0)
          (evalB_get (k := (w : ℕ)) (by simp [hρ₁]; omega)
            (by rw [hmarkl₁, getElem?_arrOf MKl hwlt]) (by omega))
          (evalB_lit (by omega))).trans ?_
        simp [hMKw]
      set ρ₂ : Env := ((ρ₁.setArr "mark" (w : ℕ) 1).setArr "trail" (tb + l.length)
        (w : ℕ)).setVar "tt" (tb + l.length + 1) with hρ₂
      have r₂ : Run B (.seq (.store "mark" (.var "w") (.lit 1))
          (.seq (.store "trail" (.var "tt") (.var "w"))
            (.assign "tt" (.add (.var "tt") (.lit 1))))) ρ₁ ρ₂ 10 :=
        (Run.seq (Run.store (idx := (w : ℕ)) (v := 1) (by simp [hρ₁]; omega)
            (by simp; omega) (by rw [hmarkl₁, length_arrOf]; exact hwlt))
          (Run.seq (Run.store (idx := tb + l.length) (v := (w : ℕ))
              (by simp [htt₁]; omega) (by simp [hρ₁]; omega)
              (by rw [arrs_setArr, if_neg (by decide), htraill₁, length_arrOf]; omega))
            (Run.assign (v := tb + l.length + 1) (by simp [htt₁]; omega)))).mono (by simp)
      set ρ₃ : Env := ρ₂.setVar "j" (ρ.vars "j" + 1) with hρ₃
      have hvj : ρ₃.vars "j" = ρ.vars "j" + 1 := by simp [hρ₃]
      have hvtt : ρ₃.vars "tt" = tb + (l ++ [w]).length := by simp [hρ₃, hρ₂]; omega
      refine ⟨ρ₃, 30, (Run.seq r₁ (Run.seq (Run.ite_true hc r₂)
          (Run.assign (v := ρ.vars "j" + 1) (by simp [hρ₂, hρ₁]; omega)))).mono (by simp),
        ?_, ?_⟩
      · refine ⟨?_, ?_, by simp [hρ₃, hρ₂, hρ₁, hinp], by simp [hρ₃, hρ₂, hρ₁, hout],
          by omega, by omega, l ++ [w], hndapp, ?_, hvtt, ⟨?_, ?_, ?_⟩, ?_⟩
        · intro y h1 h2 h3
          rw [show ρ₃.vars y = ρ.vars y by simp [hρ₃, hρ₂, hρ₁, h1, h2, h3]]
          exact hfr y h1 h2 h3
        · intro a h1 h2
          rw [show ρ₃.arrs a = ρ.arrs a by simp [hρ₃, hρ₂, hρ₁, h1, h2]]
          exact harr a h1 h2
        · intro x
          rw [hvj]
          simp only [List.mem_append, List.mem_singleton]
          constructor
          · rintro (hx | rfl)
            · obtain ⟨hx1, p, hp1, hp2, hp3⟩ := (hmem x).1 hx
              exact ⟨hx1, p, hp1, by omega, hp3⟩
            · exact ⟨hwM, ρ.vars "j", hlo, by omega, hwval.symm⟩
          · rintro ⟨hx1, p, hp1, hp2, hp3⟩
            rcases Nat.lt_or_ge p (ρ.vars "j") with hp | hp
            · exact Or.inl ((hmem x).2 ⟨hx1, p, hp1, hp, hp3⟩)
            · have hpe : p = ρ.vars "j" := by omega
              subst hpe
              exact Or.inr (Fin.ext (by rw [hwval, hp3]))
        · exact fun x => if x = (w : ℕ) then 1 else MKl x
        · show ρ₃.arrs "mark" = _
          rw [show ρ₃.arrs "mark" = (arrOf n MKl).set (w : ℕ) 1 by
            simp [hρ₃, hρ₂, hmarkl₁], set_arrOf]
        · have hins : (l ++ [w]).toFinset = insert w l.toFinset := by
            ext x
            simp only [List.mem_toFinset, List.mem_append, List.mem_singleton,
              Finset.mem_insert]
            tauto
          rw [hins, Finset.union_insert]
          simpa using indicator_set_one (M := M ∪ l.toFinset) hMKl hwlt
        · refine ⟨fun x => if x = tb + l.length then (w : ℕ) else TRl x, ?_, ?_, ?_⟩
          · rw [show ρ₃.arrs "trail" = (arrOf (n + 1) TRl).set (tb + l.length) (w : ℕ) by
              simp [hρ₃, hρ₂, htraill₁], set_arrOf]
          · intro i hi
            show (if i = tb + l.length then (w : ℕ) else TRl i) = TR i
            rw [if_neg (by omega)]
            exact hTRlo i hi
          · intro i hi
            simp only [List.length_append, List.length_cons, List.length_nil] at hi
            rcases Nat.lt_or_ge i l.length with hil | hil
            · show (if tb + i = tb + l.length then (w : ℕ) else TRl (tb + i)) = _
              rw [if_neg (by omega), hTRhi i hil]
              congr 1
              exact (List.getElem_append_left hil).symm
            · have hie : i = l.length := by omega
              subst hie
              show (if tb + l.length = tb + l.length then (w : ℕ) else TRl (tb + l.length)) = _
              rw [if_pos rfl]
              congr 1
              simp
      · simp only [size_condLt, size_var, hvj]
        omega
    · -- an already marked target: the slot contributes nothing
      have hwin : w ∈ M ∪ l.toFinset := by
        have := mem_of_indicator_ne hMKl hwlt hMKw
        simpa using this
      have hc : (Cond.eq (.get "mark" (.var "w")) (.lit 0)).evalB B ρ₁ = some false := by
        refine (evalB_condEq (m := MKl (w : ℕ)) (n := 0)
          (evalB_get (k := (w : ℕ)) (by simp [hρ₁]; omega)
            (by rw [hmarkl₁, getElem?_arrOf MKl hwlt])
            (by rw [hMKl (w : ℕ) hwlt]; split <;> omega))
          (evalB_lit (by omega))).trans ?_
        simp [hMKw]
      set ρ₃ : Env := ρ₁.setVar "j" (ρ.vars "j" + 1) with hρ₃
      have hvj : ρ₃.vars "j" = ρ.vars "j" + 1 := by simp [hρ₃]
      refine ⟨ρ₃, 30, (Run.seq r₁ (Run.seq (Run.ite_false hc Run.skip)
          (Run.assign (v := ρ.vars "j" + 1) (by simp [hρ₁]; omega)))).mono (by simp),
        ?_, ?_⟩
      · refine ⟨?_, ?_, by simp [hρ₃, hρ₁, hinp], by simp [hρ₃, hρ₁, hout],
          by omega, by omega, l, hnd, ?_, by simp [hρ₃, hρ₁]; omega,
          ⟨MKl, by simp [hρ₃, hρ₁, hmarkl], hMKl⟩,
          ⟨TRl, by simp [hρ₃, hρ₁, htraill], hTRlo, hTRhi⟩⟩
        · intro y h1 h2 h3
          rw [show ρ₃.vars y = ρ.vars y by simp [hρ₃, hρ₁, h1, h2]]
          exact hfr y h1 h2 h3
        · intro a h1 h2
          rw [show ρ₃.arrs a = ρ.arrs a by simp [hρ₃, hρ₁]]
          exact harr a h1 h2
        · intro x
          rw [hvj]
          constructor
          · intro hx
            obtain ⟨hx1, p, hp1, hp2, hp3⟩ := (hmem x).1 hx
            exact ⟨hx1, p, hp1, by omega, hp3⟩
          · rintro ⟨hx1, p, hp1, hp2, hp3⟩
            rcases Nat.lt_or_ge p (ρ.vars "j") with hp | hp
            · exact (hmem x).2 ⟨hx1, p, hp1, hp, hp3⟩
            · have hpe : p = ρ.vars "j" := by omega
              subst hpe
              have hxw : x = w := Fin.ext (by rw [hwval, hp3])
              subst hxw
              rcases Finset.mem_union.1 hwin with h | h
              · exact absurd h hx1
              · exact List.mem_toFinset.1 h
      · simp only [size_condLt, size_var, hvj]
        omega
  obtain ⟨τ', K, hrun, ⟨hfr', harr', hinp', hout', hlo', hhi', l, hnd', hmem', htt'',
      ⟨MK', hmark', hMK'⟩, ⟨TR', htrail', hTRlo', hTRhi'⟩⟩, hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := Cond.lt (.var "j") (.var "jend")) (c := rowStep)
      (RowInv g v M tb TR τ) (fun ρ => 40 * (offset g ((v : ℕ) + 1) - ρ.vars "j"))
      (fun ρ hρ => by
        obtain ⟨hfr, -, -, -, -, hhi, -⟩ := hρ
        refine evalB_condLt_vars (by omega) ?_
        rw [hfr "jend" (by decide) (by decide) (by decide), hjend]
        omega)
      hstep ⟨fun y _ _ _ => rfl, fun a _ _ => rfl, rfl, rfl, by omega,
        by rw [hj]; exact offset_mono' hg (by omega) v.2, [], List.nodup_nil,
        (by
          intro x
          simp only [List.not_mem_nil, false_iff, not_and, hj]
          rintro - ⟨p, hp1, hp2, -⟩
          omega),
        by simpa using htt, ⟨MK, hmark, by simpa using hMK⟩,
        ⟨TR, htrail, fun i _ => rfl, by simp⟩⟩
  · have hjend' : τ'.vars "jend" = offset g ((v : ℕ) + 1) := by
      rw [hfr' "jend" (by decide) (by decide) (by decide), hjend]
    have hjeq : τ'.vars "j" = offset g ((v : ℕ) + 1) := by
      have := le_of_condLt_false hfalse
      omega
    refine ⟨τ', l, MK', TR', K, hrun, hnd', ?_, htt'', hmark', hMK', htrail', hTRlo',
      hTRhi', harr', hfr', hinp', hout', ?_⟩
    · ext x
      rw [List.mem_toFinset, hmem' x, hjeq]
      constructor
      · rintro ⟨hx, p, hp1, hp2, hp3⟩
        obtain ⟨ha, hb, hadj⟩ := adjn_of_slot hg v.2 hp1 hp2
        refine mem_resNbhd.2 ⟨?_, hx⟩
        have : (⟨target g p, hb⟩ : Fin n) = x := Fin.ext hp3
        rw [← this]
        simpa using hadj
      · intro hx
        obtain ⟨j₀, h₁, h₂, h₃, -⟩ := exists_slot_of_mem_resNbhd hg hx
        exact ⟨(mem_resNbhd.1 hx).2, j₀, h₁, h₂, h₃⟩
    · have h₀ : 40 * (offset g ((v : ℕ) + 1) - τ.vars "j") ≤ 40 * (2 * m) := by
        have : offset g ((v : ℕ) + 1) - τ.vars "j" ≤ 2 * m := by omega
        omega
      simp only [size_condLt, size_var] at hpay
      omega

/-! ### The descend scan: what one slot does to the counts

The scan's registers move by the transport lemmas of `Residual.lean`,
against the same slot vocabulary those lemmas are stated in. Two facts
carry the whole of it: a slot has exactly one owner, so passing a slot
can add at most its own owner to the residual owners; and two unmarked
slots of one block with different targets are two residual neighbours.
The second is the per-vertex form of `exists_two_slots_iff`, which
quantifies over the owner and so cannot name the witness the scan
found. -/

/-- A slot belongs to one block: the offsets are nondecreasing, so two
blocks containing the same slot are the same block. -/
theorem owner_unique (hg : EncodesGraph g n G) {o U p : ℕ} (ho : o ≤ n) (hu : U ≤ n)
    (h1 : offset g o ≤ p) (h2 : p < offset g (o + 1))
    (h3 : offset g U ≤ p) (h4 : p < offset g (U + 1)) : o = U := by
  rcases lt_trichotomy o U with h | h | h
  · have := offset_mono' hg (show o + 1 ≤ U by omega) hu
    omega
  · exact h
  · have := offset_mono' hg (show U + 1 ≤ o by omega) ho
    omega

/-- Passing one slot adds at most its owner to the residual owners. -/
theorem mem_resOwners_succ (hg : EncodesGraph g n G) {U p : ℕ} (hu : U < n)
    (h1 : offset g U ≤ p) (h2 : p < offset g (U + 1)) {o : Fin n} :
    o ∈ ResOwners g M (p + 1) ↔ o ∈ ResOwners g M p ∨
      ((o : ℕ) = U ∧ o ∉ M ∧ U < target g p ∧ target g p ∉ markedVals M) := by
  constructor
  · intro ho
    obtain ⟨hoM, q, hq1, hq2, hq3, hq4, hq5⟩ := mem_resOwners.1 ho
    rcases Nat.lt_or_ge q p with hqp | hqp
    · exact Or.inl (mem_resOwners.2 ⟨hoM, q, hqp, hq2, hq3, hq4, hq5⟩)
    · have hqe : q = p := by omega
      subst hqe
      have hoU : (o : ℕ) = U := owner_unique hg (le_of_lt o.2) (le_of_lt hu) hq2 hq3 h1 h2
      exact Or.inr ⟨hoU, hoM, by rw [← hoU]; exact hq4, hq5⟩
  · rintro (ho | ⟨hoU, hoM, hlt, htg⟩)
    · obtain ⟨hoM, q, hq1, hq2, hq3, hq4, hq5⟩ := mem_resOwners.1 ho
      exact mem_resOwners.2 ⟨hoM, q, by omega, hq2, hq3, hq4, hq5⟩
    · exact mem_resOwners.2 ⟨hoM, p, by omega, by rw [hoU]; exact h1,
        by rw [hoU]; exact h2, by rw [hoU]; exact hlt, htg⟩

/-- A residual slot puts its owner on the list. -/
theorem resOwners_succ_of_residual (hg : EncodesGraph g n G) {U p : ℕ} (hu : U < n)
    (h1 : offset g U ≤ p) (h2 : p < offset g (U + 1)) (ho : (⟨U, hu⟩ : Fin n) ∉ M)
    (hlt : U < target g p) (htg : target g p ∉ markedVals M) :
    ResOwners g M (p + 1) = insert (⟨U, hu⟩ : Fin n) (ResOwners g M p) := by
  ext o
  rw [mem_resOwners_succ hg hu h1 h2, Finset.mem_insert]
  constructor
  · rintro (h | ⟨hoU, -, -, -⟩)
    · exact Or.inr h
    · exact Or.inl (Fin.ext hoU)
  · rintro (rfl | h)
    · exact Or.inr ⟨rfl, ho, hlt, htg⟩
    · exact Or.inl h

/-- A slot that is not residual leaves the list alone. -/
theorem resOwners_succ_of_not (hg : EncodesGraph g n G) {U p : ℕ} (hu : U < n)
    (h1 : offset g U ≤ p) (h2 : p < offset g (U + 1))
    (hno : ¬ ((⟨U, hu⟩ : Fin n) ∉ M ∧ U < target g p ∧ target g p ∉ markedVals M)) :
    ResOwners g M (p + 1) = ResOwners g M p := by
  ext o
  rw [mem_resOwners_succ hg hu h1 h2]
  constructor
  · rintro (h | ⟨hoU, h⟩)
    · exact h
    · exact absurd (by
        have : (⟨U, hu⟩ : Fin n) = o := Fin.ext hoU.symm
        rw [this]; exact h) hno
  · exact Or.inl

/-- **Two unmarked slots of one block with different targets are two
residual neighbours.** This is `exists_two_slots_iff` for the vertex the
scan actually found, which is what the branch needs: the flag names its
witness. -/
theorem two_le_resDeg_of_slots (hg : EncodesGraph g n G) {o : Fin n} {p₁ p₂ : ℕ}
    (ha₁ : offset g (o : ℕ) ≤ p₁) (hb₁ : p₁ < offset g ((o : ℕ) + 1))
    (ha₂ : offset g (o : ℕ) ≤ p₂) (hb₂ : p₂ < offset g ((o : ℕ) + 1))
    (hu₁ : target g p₁ ∉ markedVals M) (hu₂ : target g p₂ ∉ markedVals M)
    (hne : target g p₁ ≠ target g p₂) : 2 ≤ resDeg G M o := by
  rw [resDeg_eq_card]
  have key : ∀ p, offset g (o : ℕ) ≤ p → (hp : p < offset g ((o : ℕ) + 1)) →
      target g p ∉ markedVals M →
      (⟨target g p, target_lt' hg o.2 hp⟩ : Fin n) ∈ ResNbhd G M o := by
    intro p hp₁ hp₂ hp₃
    obtain ⟨ha, hb, hadj⟩ := adjn_of_slot hg o.2 hp₁ hp₂
    refine mem_resNbhd.2 ⟨?_, fun hm => hp₃ ((mem_markedVals_iff _).2 hm)⟩
    have : (⟨target g p, hb⟩ : Fin n) = ⟨target g p, target_lt' hg o.2 hp₂⟩ := rfl
    rw [← this]
    simpa using hadj
  exact Finset.one_lt_card.2 ⟨_, key p₁ ha₁ hb₁ hu₁, _, key p₂ ha₂ hb₂ hu₂,
    fun h => hne (congrArg Fin.val h)⟩

/-! ### The two halves of a slot step -/

/-- The half of `slotStep` that counts the owner into `ro`. -/
def countBlock : Com :=
  .ite (.eq (.var "cnted") (.lit 0))
    (.ite (.lt (.var "u") (.var "w"))
      (.seq (.assign "ro" (.add (.var "ro") (.lit 1))) (.assign "cnted" (.lit 1)))
      .skip)
    .skip

/-- The half of `slotStep` that runs the distinct-target test. -/
def seenBlock : Com :=
  .ite (.eq (.var "seen") (.lit 0))
    (.seq (.assign "seen" (.lit 1)) (.assign "t1" (.var "w")))
    (.ite (.lt (.var "w") (.var "t1")) recordFound
      (.ite (.lt (.var "t1") (.var "w")) recordFound .skip))

theorem slotStep_eq :
    slotStep = .seq
      (.ite (.eq (.get "mark" (.var "u")) (.lit 0))
        (.seq (.assign "w" (.get "tgt" (.var "j")))
          (.ite (.eq (.get "mark" (.var "w")) (.lit 0)) (.seq countBlock seenBlock) .skip))
        .skip)
      (.assign "j" (.add (.var "j") (.lit 1))) := rfl

/-- **The counting half.** It raises `ro` exactly on an uncounted block
whose slot names a larger vertex, and touches nothing but `ro` and
`cnted`. -/
theorem countBlock_run {ρ : Env} (h1B : 1 < B) (hcB : ρ.vars "cnted" < B)
    (huB : ρ.vars "u" < B) (hwB : ρ.vars "w" < B)
    (hroB : ρ.vars "cnted" = 0 → ρ.vars "u" < ρ.vars "w" → ρ.vars "ro" + 1 < B) :
    ∃ ρ' K, Run B countBlock ρ ρ' K ∧ K ≤ 20 ∧ ρ'.arrs = ρ.arrs ∧ ρ'.inp = ρ.inp ∧
      ρ'.out = ρ.out ∧ (∀ y, y ≠ "ro" → y ≠ "cnted" → ρ'.vars y = ρ.vars y) ∧
      ((ρ.vars "cnted" = 0 ∧ ρ.vars "u" < ρ.vars "w" ∧
          ρ'.vars "ro" = ρ.vars "ro" + 1 ∧ ρ'.vars "cnted" = 1) ∨
       (¬ (ρ.vars "cnted" = 0 ∧ ρ.vars "u" < ρ.vars "w") ∧
          ρ'.vars "ro" = ρ.vars "ro" ∧ ρ'.vars "cnted" = ρ.vars "cnted")) := by
  by_cases hc0 : ρ.vars "cnted" = 0
  · by_cases hlt : ρ.vars "u" < ρ.vars "w"
    · have hroB' := hroB hc0 hlt
      refine ⟨(ρ.setVar "ro" (ρ.vars "ro" + 1)).setVar "cnted" 1, 20,
        (Run.ite_true ((evalB_condEq (evalB_var hcB) (evalB_lit (by omega))).trans
            (by simp [hc0]))
          (Run.ite_true ((evalB_condLt (evalB_var huB) (evalB_var hwB)).trans
              (by simp [hlt]))
            (Run.seq (Run.assign (v := ρ.vars "ro" + 1) (by simp; omega))
              (Run.assign (v := 1) (by simp; omega))))).mono (by simp),
        le_rfl, rfl, rfl, rfl, ?_, Or.inl ⟨hc0, hlt, by simp, by simp⟩⟩
      intro y h1 h2
      simp [h1, h2]
    · refine ⟨ρ, 20, (Run.ite_true ((evalB_condEq (evalB_var hcB) (evalB_lit (by omega))).trans
          (by simp [hc0]))
          (Run.ite_false ((evalB_condLt (evalB_var huB) (evalB_var hwB)).trans
            (by simp [hlt])) Run.skip)).mono (by simp),
        le_rfl, rfl, rfl, rfl, fun y _ _ => rfl,
        Or.inr ⟨fun h => hlt h.2, rfl, rfl⟩⟩
  · refine ⟨ρ, 20, (Run.ite_false ((evalB_condEq (evalB_var hcB) (evalB_lit (by omega))).trans
        (by simp [hc0])) Run.skip).mono (by simp),
      le_rfl, rfl, rfl, rfl, fun y _ _ => rfl, Or.inr ⟨fun h => hc0 h.1, rfl, rfl⟩⟩

/-- **The distinct-target half.** On the block's first unmarked slot it
records the target in `t1`; on a later one it raises the flag exactly
when the target differs, keeping the witness the flag already has. -/
theorem seenBlock_run {ρ : Env} (h1B : 1 < B) (hsB : ρ.vars "seen" < B)
    (htB : ρ.vars "t1" < B) (hwB : ρ.vars "w" < B) (hfB : ρ.vars "found" < B)
    (hf01 : ρ.vars "found" ≤ 1) (huB : ρ.vars "u" < B) :
    ∃ ρ' K, Run B seenBlock ρ ρ' K ∧ K ≤ 30 ∧ ρ'.arrs = ρ.arrs ∧ ρ'.inp = ρ.inp ∧
      ρ'.out = ρ.out ∧
      (∀ y, y ≠ "seen" → y ≠ "t1" → y ≠ "found" → y ≠ "v" → ρ'.vars y = ρ.vars y) ∧
      ((ρ.vars "seen" = 0 ∧ ρ'.vars "seen" = 1 ∧ ρ'.vars "t1" = ρ.vars "w" ∧
          ρ'.vars "found" = ρ.vars "found" ∧ ρ'.vars "v" = ρ.vars "v") ∨
       (ρ.vars "seen" ≠ 0 ∧ ρ.vars "w" = ρ.vars "t1" ∧ ρ'.vars "seen" = ρ.vars "seen" ∧
          ρ'.vars "t1" = ρ.vars "t1" ∧ ρ'.vars "found" = ρ.vars "found" ∧
          ρ'.vars "v" = ρ.vars "v") ∨
       (ρ.vars "seen" ≠ 0 ∧ ρ.vars "w" ≠ ρ.vars "t1" ∧ ρ'.vars "seen" = ρ.vars "seen" ∧
          ρ'.vars "t1" = ρ.vars "t1" ∧ ρ'.vars "found" = 1 ∧
          ((ρ.vars "found" = 0 ∧ ρ'.vars "v" = ρ.vars "u") ∨
            (ρ.vars "found" = 1 ∧ ρ'.vars "v" = ρ.vars "v")))) := by
  have hrec : ∀ σ : Env, σ.vars "found" < B → σ.vars "u" < B →
      ∃ σ' K, Run B recordFound σ σ' K ∧ K ≤ 15 ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        σ'.out = σ.out ∧ (∀ y, y ≠ "found" → y ≠ "v" → σ'.vars y = σ.vars y) ∧
        ((σ.vars "found" = 0 ∧ σ'.vars "found" = 1 ∧ σ'.vars "v" = σ.vars "u") ∨
          (σ.vars "found" ≠ 0 ∧ σ'.vars "found" = σ.vars "found" ∧
            σ'.vars "v" = σ.vars "v")) := by
    intro σ hfσ huσ
    by_cases hf0 : σ.vars "found" = 0
    · refine ⟨(σ.setVar "found" 1).setVar "v" (σ.vars "u"), 15,
        (Run.ite_true ((evalB_condEq (evalB_var hfσ) (evalB_lit (by omega))).trans
            (by simp [hf0]))
          (Run.seq (Run.assign (v := 1) (by simp; omega))
            (Run.assign (v := σ.vars "u") (by simp; omega)))).mono (by simp),
        le_rfl, rfl, rfl, rfl, ?_, Or.inl ⟨hf0, by simp, by simp⟩⟩
      intro y h1 h2
      simp [h1, h2]
    · exact ⟨σ, 15, (Run.ite_false ((evalB_condEq (evalB_var hfσ) (evalB_lit (by omega))).trans
        (by simp [hf0])) Run.skip).mono (by simp),
        le_rfl, rfl, rfl, rfl, fun y _ _ => rfl, Or.inr ⟨hf0, rfl, rfl⟩⟩
  by_cases hs0 : ρ.vars "seen" = 0
  · refine ⟨(ρ.setVar "seen" 1).setVar "t1" (ρ.vars "w"), 30,
      (Run.ite_true ((evalB_condEq (evalB_var hsB) (evalB_lit (by omega))).trans
          (by simp [hs0]))
        (Run.seq (Run.assign (v := 1) (by simp; omega))
          (Run.assign (v := ρ.vars "w") (by simp; omega)))).mono (by simp),
      le_rfl, rfl, rfl, rfl, ?_, Or.inl ⟨hs0, by simp, by simp, by simp, by simp⟩⟩
    intro y h1 h2 h3 h4
    simp [h1, h2]
  · by_cases hwt : ρ.vars "w" = ρ.vars "t1"
    · refine ⟨ρ, 30, (Run.ite_false ((evalB_condEq (evalB_var hsB) (evalB_lit (by omega))).trans
          (by simp [hs0]))
          (Run.ite_false ((evalB_condLt (evalB_var hwB) (evalB_var htB)).trans (by simp [hwt]))
            (Run.ite_false ((evalB_condLt (evalB_var htB) (evalB_var hwB)).trans
              (by simp [hwt])) Run.skip))).mono (by simp),
        le_rfl, rfl, rfl, rfl, fun y _ _ _ _ => rfl,
        Or.inr (Or.inl ⟨hs0, hwt, rfl, rfl, rfl, rfl⟩)⟩
    · obtain ⟨ρ', K, hrun, hK, harr, hinp, hout, hfr, hcase⟩ := hrec ρ hfB huB
      have hgoal : ∃ K', Run B (.ite (.lt (.var "w") (.var "t1")) recordFound
          (.ite (.lt (.var "t1") (.var "w")) recordFound .skip)) ρ ρ' K' ∧ K' ≤ 24 := by
        rcases Nat.lt_or_ge (ρ.vars "w") (ρ.vars "t1") with h | h
        · exact ⟨_, Run.ite_true ((evalB_condLt (evalB_var hwB) (evalB_var htB)).trans
            (by simp [h])) hrun, by simp; omega⟩
        · exact ⟨_, Run.ite_false ((evalB_condLt (evalB_var hwB) (evalB_var htB)).trans
              (by simp; omega))
            (Run.ite_true ((evalB_condLt (evalB_var htB) (evalB_var hwB)).trans
              (by simp; omega)) hrun), by simp; omega⟩
      obtain ⟨K', hrun', hK'⟩ := hgoal
      refine ⟨ρ', 30, (Run.ite_false ((evalB_condEq (evalB_var hsB)
        (evalB_lit (by omega))).trans (by simp [hs0])) hrun').mono (by simp; omega),
        le_rfl, harr, hinp, hout, fun y h1 h2 h3 h4 => hfr y h3 h4, Or.inr (Or.inr ?_)⟩
      have hsu : ρ'.vars "seen" = ρ.vars "seen" := hfr "seen" (by decide) (by decide)
      have htu : ρ'.vars "t1" = ρ.vars "t1" := hfr "t1" (by decide) (by decide)
      rcases hcase with ⟨hf0, hf1, hv⟩ | ⟨hf0, hf1, hv⟩
      · exact ⟨hs0, hwt, hsu, htu, hf1, Or.inl ⟨hf0, hv⟩⟩
      · exact ⟨hs0, hwt, hsu, htu, by omega, Or.inr ⟨by omega, hv⟩⟩

/-! ### The descend scan

One pass over the whole target array. The loop is not flat — an inner
loop walks the block owner alongside the slot pointer — so its cost is
not constant per slot, and the potential `100·(2m − j) + 100·(n − u)`
pays for both kinds of turn at once, the same amortization the `2^k`
driver used.

The conclusion is the two things the pass computes. `ro` is the number
of *residual owners*, the count `Residual.lean` bounds against the
residual edges from both sides; and the flag is the branching test, in
its slot form — no unmarked vertex has two differently-targeted
unmarked slots, which is `ThinBlocks`, or a named one does, which is a
vertex of residual degree at least two. -/

/-- A turn of the scan, and a turn of the owner advance inside it, move
only names the whole scan moves. The scan's invariant therefore frames
against `descendScan.wvars` and each turn discharges its own frame
obligation through `Run.frame_var_sub`; the two inclusions are decided
once here instead of at every use. -/
theorem wvars_slotStep_sub : slotStep.wvars ⊆ descendScan.wvars := by decide

theorem wvars_ownerAdvance_sub : ownerAdvance.wvars ⊆ descendScan.wvars := by decide

/-- The residual owners below no slot at all. -/
theorem resOwners_zero : ResOwners g M 0 = ∅ := by
  ext o
  rw [mem_resOwners]
  constructor
  · rintro ⟨-, p, hp, -⟩
    exact absurd hp (by omega)
  · intro h
    simp at h

/-- The invariant of the descend scan. Beyond the frame conditions and
the position of the owner: `ro` counts the residual owners below the
pointer, `cnted` says whether the current owner is among them, `seen`
and `t1` remember the first unmarked target of the current block, and
the flag is the dichotomy — nothing branchable below the pointer, or a
recorded pair of unmarked slots with different targets. -/
def ScanInv (g : List ℕ) {n : ℕ} (m : ℕ) (M : Finset (Fin n)) (σ τ : Env) : Prop :=
  (∀ y, y ∉ descendScan.wvars → τ.vars y = σ.vars y) ∧ τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧
  τ.out = σ.out ∧ τ.vars "found" ≤ 1 ∧ τ.vars "cnted" ≤ 1 ∧ τ.vars "seen" ≤ 1 ∧
  τ.vars "t1" ≤ n ∧
  τ.vars "u" ≤ n ∧ offset g (τ.vars "u") ≤ τ.vars "j" ∧
  τ.vars "j" ≤ offset g (τ.vars "u" + 1) ∧ τ.vars "j" ≤ 2 * m ∧
  τ.vars "ro" = (ResOwners g M (τ.vars "j")).card ∧
  (∀ o : Fin n, (o : ℕ) = τ.vars "u" →
    (τ.vars "cnted" ≠ 0 ↔ o ∈ ResOwners g M (τ.vars "j"))) ∧
  (∀ o : Fin n, (o : ℕ) = τ.vars "u" →
    (τ.vars "seen" = 0 → ∀ p, offset g (o : ℕ) ≤ p → p < τ.vars "j" →
      o ∈ M ∨ target g p ∈ markedVals M) ∧
    (τ.vars "seen" ≠ 0 → o ∉ M ∧
      ∃ p, offset g (o : ℕ) ≤ p ∧ p < τ.vars "j" ∧ target g p = τ.vars "t1" ∧
        target g p ∉ markedVals M)) ∧
  ((τ.vars "found" = 0 ∧ ∀ o : Fin n, o ∉ M → ∀ p₁ p₂, offset g (o : ℕ) ≤ p₁ →
      p₁ < offset g ((o : ℕ) + 1) → p₁ < τ.vars "j" → offset g (o : ℕ) ≤ p₂ →
      p₂ < offset g ((o : ℕ) + 1) → p₂ < τ.vars "j" → target g p₁ ∉ markedVals M →
      target g p₂ ∉ markedVals M → target g p₁ = target g p₂) ∨
   (τ.vars "found" = 1 ∧ ∃ v : Fin n, (v : ℕ) = τ.vars "v" ∧ v ∉ M ∧
      ∃ p₁ p₂, offset g (v : ℕ) ≤ p₁ ∧ p₁ < offset g ((v : ℕ) + 1) ∧
        offset g (v : ℕ) ≤ p₂ ∧ p₂ < offset g ((v : ℕ) + 1) ∧
        target g p₁ ∉ markedVals M ∧ target g p₂ ∉ markedVals M ∧
        target g p₁ ≠ target g p₂))

/-- **The descend scan.** Started on a represented state, one pass over
the target array leaves the configuration represented and every array
untouched, having counted the residual owners into `ro` and decided the
branching test. -/
theorem descendScan_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ p < 2 * m, T p = target g p)
    (h1B : 1 < B) (hnB : n < B) (hmB : 2 * m < B)
    {C : Config n} {τ : Env} (hRep : Rep n m O T C τ) :
    ∃ (τ' : Env) (K : ℕ), Run B descendScan τ τ' K ∧ Rep n m O T C τ' ∧
      τ'.arrs = τ.arrs ∧ τ'.inp = τ.inp ∧ τ'.out = τ.out ∧
      τ'.vars "ro" = (ResOwners g (marked C.frames) (2 * edgeCount g)).card ∧
      ((τ'.vars "found" = 0 ∧ ThinBlocks g (marked C.frames)) ∨
        (τ'.vars "found" = 1 ∧ ∃ v : Fin n, (v : ℕ) = τ'.vars "v" ∧
          v ∉ marked C.frames ∧ 2 ≤ resDeg G (marked C.frames) v)) ∧
      K ≤ 250 * (n + 2 * m + 1) := by
  obtain ⟨MK, hmark, hMK⟩ := hRep.mark
  have hm2 := hRep.m2
  have hoff := hRep.off
  have htgt := hRep.tgt
  set M : Finset (Fin n) := marked C.frames with hMdef
  have hMKB : ∀ i, i < n → MK i < B := fun i hi => indicator_lt h1B hMK hi
  have hOB : ∀ i, i ≤ n → O i < B := by
    intro i hi
    have h1 := hO i hi
    have h2 := offset_le hg hi
    omega
  have hoffn : offset g n = 2 * m := by rw [hg.offset_last, hm]
  have hcardle : ∀ p, (ResOwners g M p).card ≤ n := by
    intro p
    simpa using Finset.card_le_univ (ResOwners g M p)
  -- the owner is a vertex as long as the pointer is a slot
  have hult : ∀ ρ : Env, ρ.vars "u" ≤ n → offset g (ρ.vars "u") ≤ ρ.vars "j" →
      ρ.vars "j" < 2 * m → ρ.vars "u" < n := by
    intro ρ h1 h2 h3
    rcases Nat.lt_or_ge (ρ.vars "u") n with h | h
    · exact h
    · exfalso
      have hun : ρ.vars "u" = n := by omega
      rw [hun, hoffn] at h2
      omega
  -- the inner loop's condition, evaluated
  have hcondval : ∀ ρ : Env, ρ.arrs = τ.arrs → ρ.vars "u" < n → ρ.vars "j" < 2 * m →
      (Cond.lt (.get "off" (.add (.var "u") (.lit 1))) (.add (.var "j") (.lit 1))).evalB B ρ
        = some (decide (offset g (ρ.vars "u" + 1) < ρ.vars "j" + 1)) := by
    intro ρ harrs hu hj
    have hOu : O (ρ.vars "u" + 1) = offset g (ρ.vars "u" + 1) := hO _ (by omega)
    have := evalB_condLt (B := B) (σ := ρ)
      (e := .get "off" (.add (.var "u") (.lit 1))) (f := .add (.var "j") (.lit 1))
      (m := O (ρ.vars "u" + 1)) (n := ρ.vars "j" + 1)
      (evalB_get (k := ρ.vars "u" + 1)
        (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
        (by rw [harrs, hoff, getElem?_arrOf O (by omega)]) (hOB _ (by omega)))
      (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
    rwa [hOu] at this
  -- the owner advance
  have hadv : ∀ ρ : Env, ScanInv g m M τ ρ → ρ.vars "j" < 2 * m →
      ∃ ρ' K, Run B ownerAdvance ρ ρ' K ∧ ScanInv g m M τ ρ' ∧
        ρ'.vars "j" = ρ.vars "j" ∧ ρ'.vars "j" < offset g (ρ'.vars "u" + 1) ∧
        K + 100 * (n - ρ'.vars "u") ≤ 100 * (n - ρ.vars "u") + 10 := by
    intro ρ hI hj
    have hstep : ∀ ν : Env, (ScanInv g m M τ ν ∧ ν.vars "j" = ρ.vars "j") →
        (Cond.lt (.get "off" (.add (.var "u") (.lit 1)))
          (.add (.var "j") (.lit 1))).evalB B ν = some true →
        ∃ ν' K, Run B (.seq (.assign "u" (.add (.var "u") (.lit 1)))
            (.seq (.assign "seen" (.lit 0))
              (.seq (.assign "t1" (.lit 0)) (.assign "cnted" (.lit 0))))) ν ν' K ∧
          (ScanInv g m M τ ν' ∧ ν'.vars "j" = ρ.vars "j") ∧
          1 + (Cond.lt (Expr.get "off" ((Expr.var "u").add (Expr.lit 1)))
              ((Expr.var "j").add (Expr.lit 1))).size + K + 100 * (n - ν'.vars "u") ≤
            100 * (n - ν.vars "u") := by
      rintro ν ⟨⟨hfr, harrs, hinp, hout, hf01, hc01, hs01, ht1n, hun, hlo, hhi, hj2m, hro,
        hcnt, hseen, hdich⟩, hjν⟩ hcond
      have hjlt : ν.vars "j" < 2 * m := by omega
      have hu : ν.vars "u" < n := hult ν hun hlo hjlt
      rw [hcondval ν harrs hu hjlt] at hcond
      have hadvlt : offset g (ν.vars "u" + 1) ≤ ν.vars "j" := by
        have : decide (offset g (ν.vars "u" + 1) < ν.vars "j" + 1) = true := by
          simpa using hcond
        simp only [decide_eq_true_eq] at this
        omega
      have heq : offset g (ν.vars "u" + 1) = ν.vars "j" := by omega
      have hu1 : ν.vars "u" + 1 < n := by
        rcases Nat.lt_or_ge (ν.vars "u" + 1) n with h | h
        · exact h
        · exfalso
          have : ν.vars "u" + 1 = n := by omega
          rw [this, hoffn] at heq
          omega
      set ν' : Env := (((ν.setVar "u" (ν.vars "u" + 1)).setVar "seen" 0).setVar "t1"
        0).setVar "cnted" 0 with hν'
      have hvu : ν'.vars "u" = ν.vars "u" + 1 := by simp [hν']
      have hvj : ν'.vars "j" = ν.vars "j" := by simp [hν']
      have rbody : Run B (.seq (.assign "u" (.add (.var "u") (.lit 1)))
          (.seq (.assign "seen" (.lit 0))
            (.seq (.assign "t1" (.lit 0)) (.assign "cnted" (.lit 0))))) ν ν' 12 :=
        (Run.seq (Run.assign (v := ν.vars "u" + 1) (by simp; omega))
          (Run.seq (Run.assign (v := 0) (by simp; omega))
            (Run.seq (Run.assign (v := 0) (by simp; omega))
              (Run.assign (v := 0) (by simp; omega))))).mono (by simp)
      refine ⟨ν', 12, rbody, ⟨⟨?_, ?_,
        by simp [hν', hinp], by simp [hν', hout], by simp [hν']; omega,
        by simp [hν'], by simp [hν'], by simp [hν'],
        by omega, by rw [hvu, hvj, heq], ?_, by omega, ?_, ?_, ?_, ?_⟩, by rw [hvj, hjν]⟩, ?_⟩
      · intro y hy
        exact (rbody.frame_var_sub y wvars_ownerAdvance_sub hy).trans (hfr y hy)
      · simp [hν', harrs]
      · rw [hvu, hvj, ← heq]
        exact offset_mono' hg (by omega) (by omega)
      · rw [hvj, show ν'.vars "ro" = ν.vars "ro" by simp [hν']]
        exact hro
      · intro o ho
        rw [hvu] at ho
        rw [show ν'.vars "cnted" = 0 by simp [hν'], hvj]
        simp only [ne_eq, not_true_eq_false, false_iff]
        intro hmem
        obtain ⟨-, q, hq1, hq2, hq3, -, -⟩ := mem_resOwners.1 hmem
        rw [ho] at hq2
        omega
      · intro o ho
        rw [hvu] at ho
        refine ⟨fun _ p hp1 hp2 => ?_, fun hs => absurd (show ν'.vars "seen" = 0 by
          simp [hν']) hs⟩
        exfalso
        rw [ho] at hp1
        rw [hvj] at hp2
        omega
      · rw [hvj, show ν'.vars "found" = ν.vars "found" by simp [hν'],
          show ν'.vars "v" = ν.vars "v" by simp [hν']]
        exact hdich
      · simp only [size_condLt, size_get, size_var, size_bin, size_lit, hvu]
        omega
    obtain ⟨ρ', K, hrun, ⟨hIρ', hjρ'⟩, hfalse, hpay⟩ :=
      Run.while_potential (B := B)
        (b := Cond.lt (.get "off" (.add (.var "u") (.lit 1))) (.add (.var "j") (.lit 1)))
        (c := .seq (.assign "u" (.add (.var "u") (.lit 1)))
          (.seq (.assign "seen" (.lit 0))
            (.seq (.assign "t1" (.lit 0)) (.assign "cnted" (.lit 0)))))
        (fun ν => ScanInv g m M τ ν ∧ ν.vars "j" = ρ.vars "j")
        (fun ν => 100 * (n - ν.vars "u"))
        (fun ν hν => by
          obtain ⟨⟨-, harrs, -, -, -, -, -, -, hun, hlo, -, -, -⟩, hjν⟩ := hν
          exact ⟨_, hcondval ν harrs (hult ν hun hlo (by omega)) (by omega)⟩)
        hstep ⟨hI, rfl⟩
    have hu' : ρ'.vars "u" < n :=
      hult ρ' hIρ'.2.2.2.2.2.2.2.2.1 hIρ'.2.2.2.2.2.2.2.2.2.1 (by omega)
    rw [hcondval ρ' hIρ'.2.1 hu' (by omega)] at hfalse
    refine ⟨ρ', K, hrun, hIρ', hjρ', ?_, ?_⟩
    · have : decide (offset g (ρ'.vars "u" + 1) < ρ'.vars "j" + 1) = false := by
        simpa using hfalse
      simp only [decide_eq_false_iff_not, not_lt] at this
      omega
    · simp only [size_condLt, size_get, size_var, size_bin, size_lit] at hpay
      omega
  -- one turn of the pass: the owner advance, then the slot
  have hstep : ∀ ρ, ScanInv g m M τ ρ →
      (Cond.lt (.var "j") (.var "m2")).evalB B ρ = some true →
      ∃ ρ' K, Run B (.seq ownerAdvance slotStep) ρ ρ' K ∧ ScanInv g m M τ ρ' ∧
        1 + (Cond.lt (Expr.var "j") (Expr.var "m2")).size + K +
          (200 * (2 * m - ρ'.vars "j") + 100 * (n - ρ'.vars "u")) ≤
            200 * (2 * m - ρ.vars "j") + 100 * (n - ρ.vars "u") := by
    intro ρ hI hcond
    have hm2ρ : ρ.vars "m2" = 2 * m := by rw [hI.1 "m2" (by decide), hm2]
    have hjlt : ρ.vars "j" < 2 * m := by
      have := lt_of_condLt_true hcond
      omega
    obtain ⟨ρ₁, K₁, r₁, hI₁, hj₁, hblk, hpay₁⟩ := hadv ρ hI hjlt
    obtain ⟨hfr, harrs, hinp, hout, hf01, hc01, hs01, ht1n, hun, hlo, hhi, hj2m, hro,
      hcnt, hseen, hdich⟩ := hI₁
    have hjρ₁ : ρ₁.vars "j" < 2 * m := by omega
    have hu : ρ₁.vars "u" < n := hult ρ₁ hun hlo hjρ₁
    have hmarkρ : ρ₁.arrs "mark" = arrOf n MK := by rw [harrs, hmark]
    have htgtρ : ρ₁.arrs "tgt" = arrOf (2 * m) T := by rw [harrs, htgt]
    have htj : T (ρ₁.vars "j") = target g (ρ₁.vars "j") := hT _ hjρ₁
    have htjn : target g (ρ₁.vars "j") < n := target_lt' hg hu hblk
    have hcondmark : ∀ (ν : Env) (x : String), ν.arrs "mark" = arrOf n MK →
        ν.vars x < n → (Cond.eq (.get "mark" (.var x)) (.lit 0)).evalB B ν
          = some (MK (ν.vars x) == 0) := by
      intro ν x hmν hx
      exact evalB_condEq (evalB_get (k := ν.vars x) (evalB_var (by omega))
        (by rw [hmν, getElem?_arrOf MK hx]) (hMKB _ hx)) (evalB_lit (by omega))
    -- the slot changes nothing but the pointer whenever it is not a residual slot
    have hskip : ∀ ρ' : Env, ρ'.arrs = ρ₁.arrs → ρ'.inp = ρ₁.inp → ρ'.out = ρ₁.out →
        (∀ y, y ≠ "j" → y ≠ "w" → ρ'.vars y = ρ₁.vars y) →
        ρ'.vars "j" = ρ₁.vars "j" + 1 →
        ((⟨ρ₁.vars "u", hu⟩ : Fin n) ∈ M ∨ target g (ρ₁.vars "j") ∈ markedVals M) →
        ScanInv g m M τ ρ' := by
      intro ρ' ha hi ho hv hj hdead
      have hu' : ρ'.vars "u" = ρ₁.vars "u" := hv "u" (by decide) (by decide)
      have hRO : ResOwners g M (ρ₁.vars "j" + 1) = ResOwners g M (ρ₁.vars "j") := by
        refine resOwners_succ_of_not hg hu hlo hblk ?_
        rintro ⟨h1, h2, h3⟩
        rcases hdead with h | h
        · exact h1 h
        · exact h3 h
      have hmk : (⟨ρ'.vars "u", hu' ▸ hu⟩ : Fin n) = ⟨ρ₁.vars "u", hu⟩ := Fin.ext hu'
      refine ⟨fun y hy => ?_, by rw [ha, harrs], by rw [hi, hinp], by rw [ho, hout],
        by rw [hv "found" (by decide) (by decide)]; exact hf01,
        by rw [hv "cnted" (by decide) (by decide)]; exact hc01,
        by rw [hv "seen" (by decide) (by decide)]; exact hs01,
        by rw [hv "t1" (by decide) (by decide)]; exact ht1n,
        by rw [hu']; exact hun, by rw [hu', hj]; omega, by rw [hu', hj]; omega,
        by rw [hj]; omega, ?_, ?_, ?_, ?_⟩
      · rw [hv y (notMem_wvars_ne hy (by decide)) (notMem_wvars_ne hy (by decide))]
        exact hfr y hy
      · rw [hv "ro" (by decide) (by decide), hj, hRO]
        exact hro
      · intro o ho
        rw [hu'] at ho
        rw [hv "cnted" (by decide) (by decide), hj, hRO]
        exact hcnt o ho
      · intro o ho
        rw [hu'] at ho
        rw [hv "seen" (by decide) (by decide), hv "t1" (by decide) (by decide), hj]
        have hoeq : o = (⟨ρ₁.vars "u", hu⟩ : Fin n) := Fin.ext ho
        refine ⟨fun hs p hp1 hp2 => ?_, fun hs => ?_⟩
        · rcases Nat.lt_or_ge p (ρ₁.vars "j") with hp | hp
          · exact (hseen o ho).1 hs p hp1 hp
          · have hpe : p = ρ₁.vars "j" := by omega
            subst hpe
            rcases hdead with h | h
            · exact Or.inl (hoeq ▸ h)
            · exact Or.inr h
        · obtain ⟨h1, p, hp1, hp2, hp3, hp4⟩ := (hseen o ho).2 hs
          exact ⟨h1, p, hp1, by omega, hp3, hp4⟩
      · rw [hv "found" (by decide) (by decide), hv "v" (by decide) (by decide), hj]
        rcases hdich with ⟨hf, hall⟩ | ⟨hf, hv1⟩
        · refine Or.inl ⟨hf, ?_⟩
          intro o ho p₁ p₂ ha₁ hb₁ hc₁ ha₂ hb₂ hc₂ hd₁ hd₂
          have key : ∀ p, offset g (o : ℕ) ≤ p → p < offset g ((o : ℕ) + 1) →
              p < ρ₁.vars "j" + 1 → target g p ∉ markedVals M → p < ρ₁.vars "j" := by
            intro p hpa hpb hpc hpd
            rcases Nat.lt_or_ge p (ρ₁.vars "j") with h | h
            · exact h
            · exfalso
              have hpe : p = ρ₁.vars "j" := by omega
              subst hpe
              have hou : (o : ℕ) = ρ₁.vars "u" :=
                owner_unique hg (le_of_lt o.2) (le_of_lt hu) hpa hpb hlo hblk
              have hoeq : o = (⟨ρ₁.vars "u", hu⟩ : Fin n) := Fin.ext hou
              rcases hdead with h' | h'
              · exact ho (hoeq ▸ h')
              · exact hpd h'
          exact hall o ho p₁ p₂ ha₁ hb₁ (key p₁ ha₁ hb₁ hc₁ hd₁) ha₂ hb₂
            (key p₂ ha₂ hb₂ hc₂ hd₂) hd₁ hd₂
        · exact Or.inr ⟨hf, hv1⟩
    -- the three shapes a slot can have
    by_cases hMKu : MK (ρ₁.vars "u") = 0
    · have hUnot : (⟨ρ₁.vars "u", hu⟩ : Fin n) ∉ M := not_mem_of_indicator_eq hMK hu hMKu
      have hcu : (Cond.eq (.get "mark" (.var "u")) (.lit 0)).evalB B ρ₁ = some true := by
        rw [hcondmark ρ₁ "u" hmarkρ hu]
        simp [hMKu]
      have rw₁ : Run B (.assign "w" (.get "tgt" (.var "j"))) ρ₁
          (ρ₁.setVar "w" (target g (ρ₁.vars "j"))) 3 :=
        (Run.assign (v := target g (ρ₁.vars "j")) (evalB_get (k := ρ₁.vars "j")
          (evalB_var (by omega)) (by rw [htgtρ, getElem?_arrOf T hjρ₁, htj])
          (by omega))).mono (by simp)
      have hmarkρ₂ : (ρ₁.setVar "w" (target g (ρ₁.vars "j"))).arrs "mark" = arrOf n MK := by
        rw [arrs_setVar, hmarkρ]
      have hvw : (ρ₁.setVar "w" (target g (ρ₁.vars "j"))).vars "w" =
          target g (ρ₁.vars "j") := by simp
      by_cases hMKw : MK (target g (ρ₁.vars "j")) = 0
      · -- a residual slot: the counters move
        have htjnot : target g (ρ₁.vars "j") ∉ markedVals M :=
          (indicator_zero_iff hMK htjn).1 hMKw
        have hcw : (Cond.eq (.get "mark" (.var "w")) (.lit 0)).evalB B
            (ρ₁.setVar "w" (target g (ρ₁.vars "j"))) = some true := by
          rw [hcondmark _ "w" hmarkρ₂ (by rw [hvw]; exact htjn), hvw]
          simp [hMKw]
        obtain ⟨ρ₃, K₃, r₃, hK₃, ha₃, hi₃, ho₃, hv₃, hcase₃⟩ :=
          countBlock_run (B := B) (ρ := ρ₁.setVar "w" (target g (ρ₁.vars "j")))
            h1B (by simp; omega) (by simp; omega) (by rw [hvw]; omega) (by
              intro hc0 hltw
              have hnotmem : (⟨ρ₁.vars "u", hu⟩ : Fin n) ∉ ResOwners g M (ρ₁.vars "j") := by
                intro hmem
                have hc0' : ρ₁.vars "cnted" = 0 := by simpa using hc0
                exact absurd ((hcnt ⟨ρ₁.vars "u", hu⟩ rfl).2 hmem) (by simp [hc0'])
              have hins : ResOwners g M (ρ₁.vars "j" + 1) =
                  insert (⟨ρ₁.vars "u", hu⟩ : Fin n) (ResOwners g M (ρ₁.vars "j")) :=
                resOwners_succ_of_residual hg hu hlo hblk hUnot (by simpa [hvw] using hltw)
                  htjnot
              have hcard : (ResOwners g M (ρ₁.vars "j" + 1)).card =
                  (ResOwners g M (ρ₁.vars "j")).card + 1 := by
                rw [hins, Finset.card_insert_of_notMem hnotmem]
              have := hcardle (ρ₁.vars "j" + 1)
              simp only [vars_setVar, if_neg (show ¬ ("ro" = "w") by decide)]
              omega)
        have hv₃u : ρ₃.vars "u" = ρ₁.vars "u" := by
          rw [hv₃ "u" (by decide) (by decide)]; simp
        have hv₃w : ρ₃.vars "w" = target g (ρ₁.vars "j") := by
          rw [hv₃ "w" (by decide) (by decide), hvw]
        obtain ⟨ρ₄, K₄, r₄, hK₄, ha₄, hi₄, ho₄, hv₄, hcase₄⟩ :=
          seenBlock_run (B := B) (ρ := ρ₃) h1B
            (by rw [hv₃ "seen" (by decide) (by decide)]; simp; omega)
            (by rw [hv₃ "t1" (by decide) (by decide)]; simp; omega)
            (by rw [hv₃w]; omega)
            (by rw [hv₃ "found" (by decide) (by decide)]; simp; omega)
            (by rw [hv₃ "found" (by decide) (by decide)]; simp; omega)
            (by rw [hv₃u]; omega)
        have hj₄ : ρ₄.vars "j" = ρ₁.vars "j" := by
          rw [hv₄ "j" (by decide) (by decide) (by decide) (by decide),
            hv₃ "j" (by decide) (by decide)]
          simp
        have hu₄ : ρ₄.vars "u" = ρ₁.vars "u" := by
          rw [hv₄ "u" (by decide) (by decide) (by decide) (by decide),
            hv₃ "u" (by decide) (by decide)]
          simp
        have rslot : Run B slotStep ρ₁ (ρ₄.setVar "j" (ρ₁.vars "j" + 1)) 90 :=
          (Run.seq
            (Run.ite_true hcu (Run.seq rw₁ (Run.ite_true hcw (Run.seq r₃ r₄))))
            (Run.assign (v := ρ₁.vars "j" + 1) (by
              simp [hj₄]; omega))).mono (by simp; omega)
        refine ⟨ρ₄.setVar "j" (ρ₁.vars "j" + 1), K₁ + 90, Run.seq r₁ rslot, ?_, ?_⟩
        · -- the invariant, after a residual slot
          have hju : (ρ₄.setVar "j" (ρ₁.vars "j" + 1)).vars "u" = ρ₁.vars "u" := by
            rw [vars_setVar, if_neg (by decide), hu₄]
          have hjj : (ρ₄.setVar "j" (ρ₁.vars "j" + 1)).vars "j" = ρ₁.vars "j" + 1 := by simp
          have hmk : (⟨(ρ₄.setVar "j" (ρ₁.vars "j" + 1)).vars "u", hju ▸ hu⟩ : Fin n) =
              ⟨ρ₁.vars "u", hu⟩ := Fin.ext hju
          have hro₄ : (ρ₄.setVar "j" (ρ₁.vars "j" + 1)).vars "ro" = ρ₃.vars "ro" := by
            rw [vars_setVar, if_neg (by decide), hv₄ "ro" (by decide) (by decide)
              (by decide) (by decide)]
          have hcn₄ : (ρ₄.setVar "j" (ρ₁.vars "j" + 1)).vars "cnted" = ρ₃.vars "cnted" := by
            rw [vars_setVar, if_neg (by decide), hv₄ "cnted" (by decide) (by decide)
              (by decide) (by decide)]
          have hse₄ : (ρ₄.setVar "j" (ρ₁.vars "j" + 1)).vars "seen" = ρ₄.vars "seen" := by
            simp
          have ht1₄ : (ρ₄.setVar "j" (ρ₁.vars "j" + 1)).vars "t1" = ρ₄.vars "t1" := by simp
          have hfo₄ : (ρ₄.setVar "j" (ρ₁.vars "j" + 1)).vars "found" = ρ₄.vars "found" := by
            simp
          have hvv₄ : (ρ₄.setVar "j" (ρ₁.vars "j" + 1)).vars "v" = ρ₄.vars "v" := by simp
          have hseenρ₃ : ρ₃.vars "seen" = ρ₁.vars "seen" := by
            rw [hv₃ "seen" (by decide) (by decide)]; simp
          have ht1ρ₃ : ρ₃.vars "t1" = ρ₁.vars "t1" := by
            rw [hv₃ "t1" (by decide) (by decide)]; simp
          have hfoundρ₃ : ρ₃.vars "found" = ρ₁.vars "found" := by
            rw [hv₃ "found" (by decide) (by decide)]; simp
          have hvρ₃ : ρ₃.vars "v" = ρ₁.vars "v" := by
            rw [hv₃ "v" (by decide) (by decide)]; simp
          refine ⟨fun y hy => ?_,
            by rw [arrs_setVar, ha₄, ha₃, arrs_setVar, harrs],
            by rw [inp_setVar, hi₄, hi₃, inp_setVar, hinp],
            by rw [out_setVar, ho₄, ho₃, out_setVar, hout], ?_, ?_, ?_, ?_,
            by rw [hju]; exact hun, by rw [hju, hjj]; omega, by rw [hju, hjj]; omega,
            by rw [hjj]; omega, ?_, ?_, ?_, ?_⟩
          · exact (rslot.frame_var_sub y wvars_slotStep_sub hy).trans (hfr y hy)
          · rcases hcase₄ with ⟨-, -, -, hf, -⟩ | ⟨-, -, -, -, hf, -⟩ | ⟨-, -, -, -, hf, -⟩
            · rw [hfo₄, hf, hfoundρ₃]; exact hf01
            · rw [hfo₄, hf, hfoundρ₃]; exact hf01
            · rw [hfo₄, hf]
          · rcases hcase₃ with ⟨-, -, -, hc⟩ | ⟨-, -, hc⟩
            · rw [hcn₄, hc]
            · rw [hcn₄, hc, vars_setVar, if_neg (by decide)]; exact hc01
          · rcases hcase₄ with ⟨-, hs, -, -, -⟩ | ⟨-, -, hs, -, -, -⟩ | ⟨-, -, hs, -, -, -⟩
            · rw [hse₄, hs]
            · rw [hse₄, hs, hseenρ₃]; exact hs01
            · rw [hse₄, hs, hseenρ₃]; exact hs01
          · rcases hcase₄ with ⟨-, -, ht, -, -⟩ | ⟨-, -, -, ht, -, -⟩ | ⟨-, -, -, ht, -, -⟩
            · rw [ht1₄, ht, hv₃w]; omega
            · rw [ht1₄, ht, ht1ρ₃]; exact ht1n
            · rw [ht1₄, ht, ht1ρ₃]; exact ht1n
          · -- the count
            rw [hro₄, hjj]
            rcases hcase₃ with ⟨hc0, hltw, hr, -⟩ | ⟨hno, hr, -⟩
            · have hnotmem : (⟨ρ₁.vars "u", hu⟩ : Fin n) ∉ ResOwners g M (ρ₁.vars "j") := by
                intro hmem
                have hc0' : ρ₁.vars "cnted" = 0 := by simpa using hc0
                exact absurd ((hcnt ⟨ρ₁.vars "u", hu⟩ rfl).2 hmem) (by simp [hc0'])
              rw [hr, resOwners_succ_of_residual hg hu hlo hblk hUnot
                (by simpa [hvw] using hltw) htjnot,
                Finset.card_insert_of_notMem hnotmem, vars_setVar, if_neg (by decide), hro]
            · rw [hr, vars_setVar, if_neg (by decide), hro]
              congr 1
              refine Eq.symm ?_
              by_cases hc0 : ρ₁.vars "cnted" = 0
              · refine resOwners_succ_of_not hg hu hlo hblk ?_
                rintro ⟨-, h2, -⟩
                exact hno ⟨by simpa using hc0, by simpa [hvw] using h2⟩
              · rcases Nat.lt_or_ge (ρ₁.vars "u") (target g (ρ₁.vars "j")) with hlt | hge
                · rw [resOwners_succ_of_residual hg hu hlo hblk hUnot hlt htjnot,
                    Finset.insert_eq_self.2 ((hcnt ⟨ρ₁.vars "u", hu⟩ rfl).1 hc0)]
                · refine resOwners_succ_of_not hg hu hlo hblk ?_
                  rintro ⟨-, h2, -⟩
                  omega
          · -- the counted flag
            intro o ho
            rw [hju] at ho
            rw [show o = (⟨ρ₁.vars "u", hu⟩ : Fin n) from Fin.ext ho, hcn₄, hjj]
            rcases hcase₃ with ⟨hc0, hltw, -, hc⟩ | ⟨hno, -, hc⟩
            · rw [hc, resOwners_succ_of_residual hg hu hlo hblk hUnot
                (by simpa [hvw] using hltw) htjnot]
              simp
            · rw [hc, vars_setVar, if_neg (by decide)]
              by_cases hc0 : ρ₁.vars "cnted" = 0
              · rw [show ResOwners g M (ρ₁.vars "j" + 1) = ResOwners g M (ρ₁.vars "j") from
                  resOwners_succ_of_not hg hu hlo hblk (by
                    rintro ⟨-, h2, -⟩
                    exact hno ⟨by simpa using hc0, by simpa [hvw] using h2⟩)]
                exact hcnt ⟨ρ₁.vars "u", hu⟩ rfl
              · rw [show ResOwners g M (ρ₁.vars "j" + 1) = ResOwners g M (ρ₁.vars "j") from by
                  rcases Nat.lt_or_ge (ρ₁.vars "u") (target g (ρ₁.vars "j")) with hlt | hge
                  · rw [resOwners_succ_of_residual hg hu hlo hblk hUnot hlt htjnot,
                      Finset.insert_eq_self.2 ((hcnt ⟨ρ₁.vars "u", hu⟩ rfl).1 hc0)]
                  · exact resOwners_succ_of_not hg hu hlo hblk (by
                      rintro ⟨-, h2, -⟩; omega)]
                exact hcnt ⟨ρ₁.vars "u", hu⟩ rfl
          · -- the block registers
            intro o ho
            rw [hju] at ho
            rw [show o = (⟨ρ₁.vars "u", hu⟩ : Fin n) from Fin.ext ho, hse₄, ht1₄, hjj]
            rcases hcase₄ with ⟨hs0, hs1, ht, -, -⟩ | ⟨hs0, hwt, hs1, ht, -, -⟩ |
              ⟨hs0, hwt, hs1, ht, -, -⟩
            · refine ⟨fun hz => absurd hs1 (by omega), fun _ => ⟨hUnot, ρ₁.vars "j",
                hlo, by omega, by rw [ht, hv₃w], htjnot⟩⟩
            · rw [hs1, hseenρ₃, ht, ht1ρ₃]
              refine ⟨fun hz => absurd hz (by simpa [hseenρ₃] using hs0), fun hz => ?_⟩
              obtain ⟨h1, p, hp1, hp2, hp3, hp4⟩ := (hseen ⟨ρ₁.vars "u", hu⟩ rfl).2 (by
                simpa [hseenρ₃] using hs0)
              exact ⟨h1, p, hp1, by omega, hp3, hp4⟩
            · rw [hs1, hseenρ₃, ht, ht1ρ₃]
              refine ⟨fun hz => absurd hz (by simpa [hseenρ₃] using hs0), fun hz => ?_⟩
              obtain ⟨h1, p, hp1, hp2, hp3, hp4⟩ := (hseen ⟨ρ₁.vars "u", hu⟩ rfl).2 (by
                simpa [hseenρ₃] using hs0)
              exact ⟨h1, p, hp1, by omega, hp3, hp4⟩
          · -- the flag
            rw [hfo₄, hvv₄, hjj]
            rcases hcase₄ with ⟨hs0, hs1, ht, hf, hvv⟩ | ⟨hs0, hwt, hs1, ht, hf, hvv⟩ |
              ⟨hs0, hwt, hs1, ht, hf, hvcase⟩
            · -- the block's first unmarked slot
              have hs0' : ρ₁.vars "seen" = 0 := by rw [← hseenρ₃]; exact hs0
              rw [hf, hfoundρ₃, hvv, hvρ₃]
              rcases hdich with ⟨hfz, hall'⟩ | ⟨hfz, hv1⟩
              · refine Or.inl ⟨hfz, ?_⟩
                intro o ho p₁ p₂ ha₁ hb₁ hc₁ ha₂ hb₂ hc₂ hd₁ hd₂
                have howner : ∀ p, offset g (o : ℕ) ≤ p → p < offset g ((o : ℕ) + 1) →
                    p = ρ₁.vars "j" → (o : ℕ) = ρ₁.vars "u" := by
                  intro p hpa hpb hpe
                  subst hpe
                  exact owner_unique hg (le_of_lt o.2) (le_of_lt hu) hpa hpb hlo hblk
                have hone : ∀ p, offset g (o : ℕ) ≤ p → p < ρ₁.vars "j" →
                    target g p ∉ markedVals M → (o : ℕ) = ρ₁.vars "u" → False := by
                  intro p hpa hpc hpd hou
                  rcases (hseen o hou).1 hs0' p hpa hpc with h' | h'
                  · exact ho h'
                  · exact hpd h'
                rcases Nat.lt_or_ge p₁ (ρ₁.vars "j") with h₁ | h₁ <;>
                  rcases Nat.lt_or_ge p₂ (ρ₁.vars "j") with h₂ | h₂
                · exact hall' o ho p₁ p₂ ha₁ hb₁ h₁ ha₂ hb₂ h₂ hd₁ hd₂
                · exact absurd (hone p₁ ha₁ h₁ hd₁ (howner p₂ ha₂ hb₂ (by omega)))
                    not_false
                · exact absurd (hone p₂ ha₂ h₂ hd₂ (howner p₁ ha₁ hb₁ (by omega)))
                    not_false
                · rw [show p₁ = ρ₁.vars "j" by omega, show p₂ = ρ₁.vars "j" by omega]
              · exact Or.inr ⟨hfz, hv1⟩
            · -- a repeat of the block's first unmarked target
              have hs0' : ρ₁.vars "seen" ≠ 0 := by rw [← hseenρ₃]; exact hs0
              have hwt' : target g (ρ₁.vars "j") = ρ₁.vars "t1" := by
                rw [← ht1ρ₃, ← hwt, hv₃w]
              rw [hf, hfoundρ₃, hvv, hvρ₃]
              obtain ⟨hUn, p₀, hp₀a, hp₀b, hp₀c, hp₀d⟩ := (hseen ⟨ρ₁.vars "u", hu⟩ rfl).2 hs0'
              rcases hdich with ⟨hfz, hall'⟩ | ⟨hfz, hv1⟩
              · refine Or.inl ⟨hfz, ?_⟩
                intro o ho p₁ p₂ ha₁ hb₁ hc₁ ha₂ hb₂ hc₂ hd₁ hd₂
                have howner : ∀ p, offset g (o : ℕ) ≤ p → p < offset g ((o : ℕ) + 1) →
                    p = ρ₁.vars "j" → (o : ℕ) = ρ₁.vars "u" := by
                  intro p hpa hpb hpe
                  subst hpe
                  exact owner_unique hg (le_of_lt o.2) (le_of_lt hu) hpa hpb hlo hblk
                have hone : ∀ p, offset g (o : ℕ) ≤ p → p < offset g ((o : ℕ) + 1) →
                    p < ρ₁.vars "j" → target g p ∉ markedVals M → (o : ℕ) = ρ₁.vars "u" →
                    target g p = ρ₁.vars "t1" := by
                  intro p hpa hpb hpc hpd hou
                  rw [← hp₀c]
                  exact hall' o ho p p₀ hpa hpb hpc (by rw [hou]; exact hp₀a)
                    (by rw [hou]; omega) hp₀b hpd hp₀d
                rcases Nat.lt_or_ge p₁ (ρ₁.vars "j") with h₁ | h₁ <;>
                  rcases Nat.lt_or_ge p₂ (ρ₁.vars "j") with h₂ | h₂
                · exact hall' o ho p₁ p₂ ha₁ hb₁ h₁ ha₂ hb₂ h₂ hd₁ hd₂
                · rw [hone p₁ ha₁ hb₁ h₁ hd₁ (howner p₂ ha₂ hb₂ (by omega)),
                    show p₂ = ρ₁.vars "j" by omega, hwt']
                · rw [hone p₂ ha₂ hb₂ h₂ hd₂ (howner p₁ ha₁ hb₁ (by omega)),
                    show p₁ = ρ₁.vars "j" by omega, hwt']
                · rw [show p₁ = ρ₁.vars "j" by omega, show p₂ = ρ₁.vars "j" by omega]
              · exact Or.inr ⟨hfz, hv1⟩
            · -- a second unmarked target: the flag goes up
              have hs0' : ρ₁.vars "seen" ≠ 0 := by rw [← hseenρ₃]; exact hs0
              have hwt' : target g (ρ₁.vars "j") ≠ ρ₁.vars "t1" := by
                rw [← ht1ρ₃, ← hv₃w]; exact hwt
              obtain ⟨hUn, p₀, hp₀a, hp₀b, hp₀c, hp₀d⟩ := (hseen ⟨ρ₁.vars "u", hu⟩ rfl).2 hs0'
              refine Or.inr ⟨hf, ?_⟩
              rcases hvcase with ⟨hfz, hvv⟩ | ⟨hfz, hvv⟩
              · refine ⟨⟨ρ₁.vars "u", hu⟩, by rw [hvv, hv₃u], hUnot, p₀, ρ₁.vars "j",
                  hp₀a, lt_trans hp₀b hblk, hlo, hblk, hp₀d, htjnot, ?_⟩
                rw [hp₀c]
                exact fun h => hwt' h.symm
              · rcases hdich with ⟨hfz', -⟩ | ⟨-, v₀, hv0, hv1⟩
                · exact absurd hfz' (by rw [hfoundρ₃] at hfz; omega)
                · exact ⟨v₀, by rw [hvv, hvρ₃]; exact hv0, hv1⟩
        · -- the payment
          have hju : (ρ₄.setVar "j" (ρ₁.vars "j" + 1)).vars "u" = ρ₁.vars "u" := by
            rw [vars_setVar, if_neg (by decide), hu₄]
          have hjj : (ρ₄.setVar "j" (ρ₁.vars "j" + 1)).vars "j" = ρ₁.vars "j" + 1 := by
            simp
          simp only [size_condLt, size_var, hju, hjj]
          omega
      · -- the target is marked
        refine ⟨(ρ₁.setVar "w" (target g (ρ₁.vars "j"))).setVar "j" (ρ₁.vars "j" + 1),
          K₁ + 90, Run.seq r₁ ((Run.seq (Run.ite_true hcu (Run.seq rw₁
            (Run.ite_false (by
              rw [hcondmark _ "w" hmarkρ₂ (by rw [hvw]; exact htjn), hvw]
              simp [hMKw]) Run.skip)))
            (Run.assign (v := ρ₁.vars "j" + 1) (by simp; omega))).mono (by simp)), ?_, ?_⟩
        · refine hskip _ (by simp) (by simp) (by simp) (fun y h1 h2 => by simp [h1, h2])
            (by simp) (Or.inr ?_)
          by_contra hcon
          exact hMKw ((indicator_zero_iff hMK htjn).2 hcon)
        · have hjj : ((ρ₁.setVar "w" (target g (ρ₁.vars "j"))).setVar "j"
              (ρ₁.vars "j" + 1)).vars "j" = ρ₁.vars "j" + 1 := by simp
          have hju : ((ρ₁.setVar "w" (target g (ρ₁.vars "j"))).setVar "j"
              (ρ₁.vars "j" + 1)).vars "u" = ρ₁.vars "u" := by simp
          simp only [size_condLt, size_var, hjj, hju]
          omega
    · -- the owner is marked
      refine ⟨ρ₁.setVar "j" (ρ₁.vars "j" + 1), K₁ + 90,
        Run.seq r₁ ((Run.seq (Run.ite_false (by
            rw [hcondmark ρ₁ "u" hmarkρ hu]
            simp [hMKu]) Run.skip)
          (Run.assign (v := ρ₁.vars "j" + 1) (by simp; omega))).mono (by simp)), ?_, ?_⟩
      · exact hskip _ (by simp) (by simp) (by simp) (fun y h1 h2 => by simp [h1])
          (by simp) (Or.inl (mem_of_indicator_ne hMK hu hMKu))
      · have hjj : (ρ₁.setVar "j" (ρ₁.vars "j" + 1)).vars "j" = ρ₁.vars "j" + 1 := by simp
        have hju : (ρ₁.setVar "j" (ρ₁.vars "j" + 1)).vars "u" = ρ₁.vars "u" := by simp
        simp only [size_condLt, size_var, hjj, hju]
        omega
  -- the pass, from the initial state of its registers
  set σ₀ : Env := ((((((τ.setVar "j" 0).setVar "u" 0).setVar "ro" 0).setVar "found"
    0).setVar "seen" 0).setVar "t1" 0).setVar "cnted" 0 with hσ₀
  have hI₀ : ScanInv g m M τ σ₀ := by
    refine ⟨fun y hy => ?_, by simp [hσ₀], by simp [hσ₀], by simp [hσ₀], by simp [hσ₀],
      by simp [hσ₀], by simp [hσ₀], by simp [hσ₀], by simp [hσ₀], ?_, ?_, by simp [hσ₀],
      ?_, ?_, ?_, ?_⟩
    · have hne : ∀ z ∈ descendScan.wvars, y ≠ z := fun _ hz => notMem_wvars_ne hy hz
      simp [hσ₀, hne "j" (by decide), hne "u" (by decide), hne "ro" (by decide),
        hne "found" (by decide), hne "seen" (by decide), hne "t1" (by decide),
        hne "cnted" (by decide)]
    · simp [hσ₀, hg.offset_zero]
    · simp [hσ₀]
    · simp [hσ₀, resOwners_zero]
    · intro o ho
      rw [show σ₀.vars "cnted" = 0 by simp [hσ₀], show σ₀.vars "j" = 0 by simp [hσ₀],
        resOwners_zero]
      simp
    · intro o ho
      refine ⟨fun _ p hp1 hp2 => absurd hp2 (by simp [hσ₀]), fun hs => ?_⟩
      exact absurd (show σ₀.vars "seen" = 0 by simp [hσ₀]) hs
    · refine Or.inl ⟨by simp [hσ₀], fun o ho p₁ p₂ h1 h2 h3 => absurd h3 (by simp [hσ₀])⟩
  obtain ⟨τ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := Cond.lt (.var "j") (.var "m2"))
      (c := .seq ownerAdvance slotStep) (ScanInv g m M τ)
      (fun ν => 200 * (2 * m - ν.vars "j") + 100 * (n - ν.vars "u"))
      (fun ν hν => by
        have h1 : ν.vars "m2" = 2 * m := by rw [hν.1 "m2" (by decide), hm2]
        exact evalB_condLt_vars (by
          have := hν.2.2.2.2.2.2.2.2.2.2.2.1
          omega) (by omega))
      hstep hI₀
  obtain ⟨hfr', harrs', hinp', hout', hf01', hc01', hs01', ht1n', hun', hlo', hhi',
    hj2m', hro', hcnt', hseen', hdich'⟩ := hI'
  have hm2' : τ'.vars "m2" = 2 * m := by rw [hfr' "m2" (by decide), hm2]
  have hjend : τ'.vars "j" = 2 * m := by
    have := le_of_condLt_false hfalse
    omega
  refine ⟨τ', 250 * (n + 2 * m + 1),
    ((Run.seq (Run.assign (v := 0) (by simp; omega))
      (Run.seq (Run.assign (v := 0) (by simp; omega))
        (Run.seq (Run.assign (v := 0) (by simp; omega))
          (Run.seq (Run.assign (v := 0) (by simp; omega))
            (Run.seq (Run.assign (v := 0) (by simp; omega))
              (Run.seq (Run.assign (v := 0) (by simp; omega))
                (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun)))))))).mono ?_,
    ?_, harrs', hinp', hout', ?_, ?_, le_rfl⟩
  · simp only [hσ₀] at hpay
    simp only [size_condLt, size_var, size_lit] at hpay ⊢
    have h₀ : (200 * (2 * m - 0) + 100 * (n - 0)) = 400 * m + 100 * n := by omega
    simp only [vars_setVar] at hpay
    omega
  · exact hRep.of_vars_eq harrs' (by rw [hfr' "m2" (by decide)])
      (by rw [hfr' "mode" (by decide)]) (by rw [hfr' "bud" (by decide)])
      (by rw [hfr' "ans" (by decide)]) (by rw [hfr' "top" (by decide)])
      (by rw [hfr' "tt" (by decide)])
  · rw [hro', hjend, hm]
  · rcases hdich' with ⟨hf, hall⟩ | ⟨hf, hv1⟩
    · refine Or.inl ⟨hf, ?_⟩
      intro o ho p₁ p₂ h1 h2 h3 h4 h5 h6
      have hb₁ : p₁ < 2 * m := by
        have := offset_le hg (show (o : ℕ) + 1 ≤ n from o.2)
        omega
      have hb₂ : p₂ < 2 * m := by
        have := offset_le hg (show (o : ℕ) + 1 ≤ n from o.2)
        omega
      exact hall o ho p₁ p₂ h1 h2 (by omega) h3 h4 (by omega) h5 h6
    · obtain ⟨v₀, hv0, hvM, p₁, p₂, h1, h2, h3, h4, h5, h6, h7⟩ := hv1
      exact Or.inr ⟨hf, v₀, hv0, hvM,
        two_le_resDeg_of_slots (M := marked C.frames) hg h1 h2 h3 h4 h5 h6 h7⟩

end Lax15Proofs.VC
