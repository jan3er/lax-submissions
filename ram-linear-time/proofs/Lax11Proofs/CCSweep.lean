import Lax11Proofs.CCSearch

/-!
The sweep over the vertices, and the driver end to end.

The searches are behind us; what is left is to say that starting one at
every unlabelled vertex labels everything. Two clauses carry that. *No
label above `u` has been written* makes an unlabelled vertex the least
of its component — nothing below it can have reached it, or it would
carry that smaller label — which is what licences labelling it with
itself. *Every component below `u` is done* is what the exit argument
of the search hands back, and at `u = n` it says every vertex is
labelled, so the array holds the answer.

The potential of the sweep is the search's plus a constant per vertex
not yet swept. It is one potential for the whole loop, so the searches
are never counted separately: a search that runs long has already
consumed the slots and the queue room it is paid out of, and the sweep
around it only ever pays the per-vertex constant.
-/

namespace Lax11Proofs.CC

open Lax11.Ram Lax11.RamComputes Lax11.GraphEncoding Lax11.ConnectedComponents
open Lax11Proofs.Imp Lax11Proofs.Compile Lax11Proofs.Reasoning Lax11Proofs.Labels

variable {x : List ℕ} {n m : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}

/-! ### The sweep over the vertices -/

/-- The invariant of the outer loop: between searches the queue is
exhausted, every component below `u` is labelled, and no label above
`u` has been written. -/
def SweepInv (x : List ℕ) (n m : ℕ) (G : SimpleGraph (Fin n)) (O T : ℕ → ℕ)
    (τ : Env) : Prop :=
  τ.vars "n" = n ∧ τ.vars "m" = m ∧ τ.vars "u" ≤ n ∧
  τ.arrs "off" = arrOf (n + 1) O ∧ τ.arrs "tgt" = arrOf (2 * m) T ∧
  τ.vars "head" = τ.vars "tail" ∧
  ∃ L Q, τ.arrs "lab" = arrOf n L ∧ τ.arrs "q" = arrOf n Q ∧
    Base x n G L Q (τ.vars "head") (τ.vars "tail") ∧
    (∀ w < n, lbl G w < τ.vars "u" → L w ≠ n) ∧
    (∀ w < n, L w ≠ n → L w < τ.vars "u") ∧
    τ.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head"), deg x (Q i)

/-- The potential of the whole sweep: the search's, plus twenty-seven
per vertex not yet swept. -/
def SweepPot (n m : ℕ) (τ : Env) : ℕ := Pot n m τ + 27 * (n - τ.vars "u")

/-- One vertex of the sweep. -/
theorem outerBody_run (hx : EncodesGraph x n G) (hm : edgeCount x = m)
    (hO : ∀ i ≤ n, O i = offset x i) (hT : ∀ j < 2 * m, T j = target x j)
    {τ : Env} (hI : SweepInv x n m G O T τ)
    (hc : (Cond.lt (.var "u") (.var "n")).eval τ = some true) :
    ∃ τ' K, Run outerBody τ τ' K ∧ SweepInv x n m G O T τ' ∧
      1 + (Cond.lt (Expr.var "u") (Expr.var "n")).size + K + SweepPot n m τ'
        ≤ SweepPot n m τ := by
  obtain ⟨hn, hmm, hun, hoff, htgt, hht, L, Q, hlab, hq, hB, hdone, hlow, hsum⟩ := hI
  have hu : τ.vars "u" < n := by simp [hn] at hc; omega
  have hhd := hB.hd
  have htl := hB.tl
  by_cases hLu : L (τ.vars "u") = n
  · -- an unlabelled vertex: it is the least of its component, so search from it
    have hlu : lbl G (τ.vars "u") = τ.vars "u" := by
      have h₁ := lbl_le (G := G) hu
      have h₂ : ¬ lbl G (τ.vars "u") < τ.vars "u" := fun h => hdone _ hu h hLu
      omega
    have htail : τ.vars "tail" < n := hB.tail_lt hu hLu
    have hceval : (Cond.eq (.get "lab" (.var "u")) (.var "n")).eval τ = some true := by
      simp [hlab, getElem?_arrOf L hu, hn, hLu]
    have hQne : ∀ p, p < τ.vars "tail" → Q p ≠ τ.vars "u" := by
      intro p hp hpu
      exact (hB.qmem p hp).2 (by rw [hpu, hLu])
    -- the state the search starts from
    have hdrainI : DrainInv x n m (τ.vars "u") G O T
        (((τ.setArr "lab" (τ.vars "u") (τ.vars "u")).setArr "q" (τ.vars "tail")
          (τ.vars "u")).setVar "tail" (τ.vars "tail" + 1)) := by
      refine ⟨fun z => if z = τ.vars "u" then τ.vars "u" else L z,
        fun i => if i = τ.vars "tail" then τ.vars "u" else Q i,
        ⟨by simp [hn], by simp [hmm], by simp, by simp [hoff], by simp [htgt],
          by simp [hlab, set_arrOf], by simp [hq, set_arrOf]⟩, ?_, ?_⟩
      · refine ⟨⟨?_, by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
        · intro z hz
          by_cases hzu : z = τ.vars "u"
          · exact Or.inr (by simp [hzu, hlu])
          · simpa [if_neg hzu] using hB.lab z hz
        · intro i hi
          simp at hi
          by_cases hit : i = τ.vars "tail"
          · simp [hit, hu]; omega
          · have hi' : i < τ.vars "tail" := by omega
            rw [if_neg hit, if_neg (hQne i hi')]
            exact hB.qmem i hi'
        · intro z hz hlz
          by_cases hzu : z = τ.vars "u"
          · exact ⟨τ.vars "tail", by simp, by simp [hzu]⟩
          · rw [if_neg hzu] at hlz
            obtain ⟨i, hi, rfl⟩ := hB.qall z hz hlz
            exact ⟨i, by simp; omega, by simp [if_neg (show i ≠ τ.vars "tail" by omega)]⟩
        · intro i hi j hj hij
          simp at hi hj
          by_cases hit : i = τ.vars "tail" <;> by_cases hjt : j = τ.vars "tail"
          · omega
          · rw [if_pos hit, if_neg hjt] at hij
            exact absurd hij.symm (hQne j (by omega))
          · rw [if_neg hit, if_pos hjt] at hij
            exact absurd hij (hQne i (by omega))
          · rw [if_neg hit, if_neg hjt] at hij
            exact hB.qinj i (by omega) j (by omega) hij
        · intro i hi j hj₁ hj₂
          simp at hi
          have hit : i ≠ τ.vars "tail" := by omega
          rw [if_neg hit] at hj₁ hj₂ ⊢
          have hnotu : target x j ≠ τ.vars "u" := by
            intro hju
            have := hB.exp i (by omega) j hj₁ hj₂
            rw [hju, hLu] at this
            exact (hB.qmem i (by omega)).2 this.symm
          rw [if_neg hnotu, if_neg (hQne i (by omega))]
          exact hB.exp i (by omega) j hj₁ hj₂
        · intro z hz hlz
          by_cases hzu : z = τ.vars "u"
          · simp [hzu]; omega
          · simpa [if_neg hzu] using hdone z hz hlz
        · intro z hz hlz
          by_cases hzu : z = τ.vars "u"
          · simp [hzu]
          · rw [if_neg hzu] at hlz ⊢
            exact le_of_lt (hlow z hz hlz)
        · simp
          omega
        · intro i hi₁ hi₂
          simp at hi₁ hi₂
          have hit : i = τ.vars "tail" := by omega
          simp [hit]
      · show τ.vars "sc" = _
        simp only [vars_setVar]
        rw [hsum]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp at hi
        rw [if_neg (show i ≠ τ.vars "tail" by omega)]
    obtain ⟨τ₄, K₄, hdrun, hdI, hdhead, hdpay⟩ :=
      drain_run hx hm hO hT hu hdrainI
    obtain ⟨L₄, Q₄, ⟨hn₄, hm₄, hu₄, hoff₄, htgt₄, hlab₄, hq₄⟩, hL₄, hsum₄⟩ := hdI
    refine ⟨τ₄.setVar "u" (τ.vars "u" + 1), _,
      Run.seq (Run.ite_true hceval
        (Run.seq (Run.store (idx := τ.vars "u") (v := τ.vars "u")
            (by simp) (by simp) (by simp [hlab, hu]))
          (Run.seq (Run.store (idx := τ.vars "tail") (v := τ.vars "u")
              (by simp) (by simp) (by simp [hq, htail]))
            (Run.seq (Run.assign (v := τ.vars "tail" + 1) (by simp)) hdrun))))
        (Run.assign (v := τ.vars "u" + 1) (by simp [hu₄])), ?_, ?_⟩
    · refine ⟨by simp [hn₄], by simp [hm₄], by simp; omega, by simp [hoff₄],
        by simp [htgt₄], by simp [hdhead], L₄, Q₄, by simp [hlab₄], by simp [hq₄],
        by simpa using hL₄.base, ?_, ?_, by simpa using hsum₄⟩
      · intro w hw hlw
        simp at hlw
        rcases Nat.lt_or_ge (lbl G w) (τ.vars "u") with h | h
        · exact hL₄.done w hw h
        · have hlweq : lbl G w = τ.vars "u" := by omega
          have hrch : Rch G (τ.vars "u") w := hlweq ▸ rch_lbl (G := G) hw
          have hBt : Base x n G L₄ Q₄ (τ₄.vars "tail") (τ₄.vars "tail") := hdhead ▸ hL₄.base
          exact hBt.rch_labelled hx hrch hL₄.root
      · intro w hw hlw
        have := hL₄.low w hw hlw
        have hset : (τ₄.setVar "u" (τ.vars "u" + 1)).vars "u" = τ.vars "u" + 1 := by simp
        omega
    · -- the cost: the drain pays for itself, and the twenty-seven left over
      -- by the vertex just swept covers the sweep's own step
      have hhd4 := hL₄.base.hd
      have htl4 := hL₄.base.tl
      have hpot₄ : SweepPot n m (τ₄.setVar "u" (τ.vars "u" + 1))
          = Pot n m τ₄ + 27 * (n - (τ.vars "u" + 1)) := by simp [SweepPot, Pot]
      have hpot₁ : Pot n m (((τ.setArr "lab" (τ.vars "u") (τ.vars "u")).setArr "q"
          (τ.vars "tail") (τ.vars "u")).setVar "tail" (τ.vars "tail" + 1)) = Pot n m τ := by
        simp [Pot, hht]
        omega
      rw [hpot₁] at hdpay
      rw [hpot₄, SweepPot]
      simp only [size_condLt, size_condEq, size_get, size_add, size_lit, size_var]
      omega
  · -- an already labelled vertex: nothing to do
    have hceval : (Cond.eq (.get "lab" (.var "u")) (.var "n")).eval τ = some false := by
      simp [hlab, getElem?_arrOf L hu, hn]
      omega
    refine ⟨τ.setVar "u" (τ.vars "u" + 1), _,
      Run.seq (Run.ite_false hceval Run.skip) (Run.assign (v := τ.vars "u" + 1) (by simp)),
      ?_, ?_⟩
    · refine ⟨by simp [hn], by simp [hmm], by simp; omega, by simp [hoff], by simp [htgt],
        by simp [hht], L, Q, by simp [hlab], by simp [hq], by simpa using hB, ?_, ?_,
        by simpa using hsum⟩
      · intro w hw hlw
        simp at hlw
        rcases Nat.lt_or_ge (lbl G w) (τ.vars "u") with h | h
        · exact hdone w hw h
        · -- `u` belongs to an older component, so nothing has label `u`
          have hlueq : lbl G w = τ.vars "u" := by omega
          have hLuu : L (τ.vars "u") = lbl G (τ.vars "u") :=
            (hB.lab _ hu).resolve_left hLu
          have h₁ : lbl G (τ.vars "u") < τ.vars "u" := by
            have := hlow _ hu hLu; omega
          have h₂ : Rch G (τ.vars "u") w := hlueq ▸ rch_lbl (G := G) hw
          have := lbl_eq_of_rch h₂
          omega
      · intro w hw hlw
        have := hlow w hw hlw
        have hset : (τ.setVar "u" (τ.vars "u" + 1)).vars "u" = τ.vars "u" + 1 := by simp
        omega
    · have := hB.hd
      have := hB.tl
      have hpot : SweepPot n m (τ.setVar "u" (τ.vars "u" + 1))
          = Pot n m τ + 27 * (n - (τ.vars "u" + 1)) := by simp [SweepPot, Pot]
      rw [hpot, SweepPot]
      simp only [size_condLt, size_condEq, size_get, size_add, size_lit, size_var]
      omega

/-- **The sweep.** Every vertex is looked at, and what is left in the
label array is the answer: at `u = n` the clause "every component below
`u` is done" says that every vertex is labelled, and a written label is
the right one. -/
theorem sweep_run (hx : EncodesGraph x n G) (hm : edgeCount x = m)
    (hO : ∀ i ≤ n, O i = offset x i) (hT : ∀ j < 2 * m, T j = target x j)
    {τ : Env} (hI : SweepInv x n m G O T τ) :
    ∃ (τ' : Env) (L : ℕ → ℕ) (K : ℕ),
      Run (.while (.lt (.var "u") (.var "n")) outerBody) τ τ' K ∧
      τ'.vars "n" = n ∧ τ'.arrs "lab" = arrOf n L ∧ (∀ w < n, L w = lbl G w) ∧
      K + SweepPot n m τ' ≤ SweepPot n m τ + 4 := by
  obtain ⟨τ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_pot (b := Cond.lt (.var "u") (.var "n")) (c := outerBody)
      (SweepInv x n m G O T) (SweepPot n m) (fun _ _ => ⟨_, rfl⟩)
      (fun σ hσ hc => outerBody_run hx hm hO hT hσ hc) hI
  obtain ⟨hn', -, hun', -, -, -, L, Q, hlab', -, hB', hdone', -, -⟩ := hI'
  have hun : τ'.vars "u" = n := by simp [hn'] at hfalse; omega
  refine ⟨τ', L, K, hrun, hn', hlab', fun w hw => ?_, by simpa using hpay⟩
  exact (hB'.lab w hw).resolve_left (hdone' w hw (by rw [hun]; exact lbl_lt hw))

/-! ### The driver, end to end

What is left is bookkeeping: the four phases in a row, each handed the
frame conditions of the one before. The only choice is the array
extents, and they are the obvious ones — the encoding says how long the
offset and target arrays are, and the labels and the queue need one
entry per vertex. -/

/-- The array extents the driver runs with. -/
def ccExt (n m : ℕ) (a : String) : ℕ :=
  if a = "off" then n + 1 else if a = "tgt" then 2 * m else n

theorem getD_take {l : List ℕ} {k i : ℕ} (h : i < k) :
    (l.take k).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_drop {l : List ℕ} {k i : ℕ} :
    (l.drop k).getD i 0 = l.getD (k + i) 0 := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_cons_cons {a b i : ℕ} {l : List ℕ} :
    (a :: b :: l).getD (2 + i) 0 = l.getD i 0 := by
  have h : 2 + i = i + 1 + 1 := by omega
  rw [h]
  simp [List.getD_eq_getElem?_getD]

/-- The whole run of the driver on an encoded graph: the labels come
out, and the cost is linear in the length of the word. The constant is
not fought over anywhere — every phase was bounded loosely, and this is
the sum of those bounds, rounded up to the length of the input. -/
theorem ccCom_run (hx : EncodesGraph x n G) (hm : edgeCount x = m) :
    ∃ (σ' : Env) (K : ℕ), Run ccCom (initEnv (ccExt n m) x) σ' K ∧
      σ'.out = ccLabels G ∧ K ≤ 84 * (x.length + 1) := by
  -- the word: the two header entries, then the offsets and the targets
  have hlen := hx.length_eq
  rw [hm] at hlen
  obtain ⟨rest, hxr⟩ : ∃ rest, x = n :: m :: rest := by
    rcases x with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hlen; omega
    · simp at hlen; omega
    · have ha : a = n := by simpa [vertexCount] using hx.vertexCount_eq
      have hb : b = m := by simpa [edgeCount] using hm
      exact ⟨rest, by rw [ha, hb]⟩
  have hrest : rest.length = 1 + n + 2 * m := by rw [hxr] at hlen; simp at hlen; omega
  set ys := rest.take (n + 1) with hys_def
  set zs := rest.drop (n + 1) with hzs_def
  have hys : ys.length = n + 1 := by rw [hys_def, List.length_take]; omega
  have hzs : zs.length = 2 * m := by rw [hzs_def, List.length_drop]; omega
  have hsplit : rest = ys ++ zs := (List.take_append_drop _ _).symm
  -- what the two arrays hold once they are read in
  have hyd : ∀ i < n + 1, ys.getD i 0 = offset x i := by
    intro i hi
    rw [hys_def, getD_take hi, offset, hxr, getD_cons_cons]
  have hzd : ∀ j < 2 * m, zs.getD j 0 = target x j := by
    intro j _
    rw [hzs_def, getD_drop, target, hx.vertexCount_eq, hxr]
    have h : 3 + n + j = 2 + (n + 1 + j) := by omega
    rw [h, getD_cons_cons]
  -- the reads
  have e₁ : (initEnv (ccExt n m) x).inp = n :: (m :: rest) := hxr
  set σ₁ : Env := { (initEnv (ccExt n m) x).setVar "n" n with inp := m :: rest } with hσ₁
  set σ₂ : Env := { σ₁.setVar "m" m with inp := rest } with hσ₂
  set σ₃ : Env := σ₂.setVar "len" (n + 1) with hσ₃
  have r₁ : Run (.read "n") (initEnv (ccExt n m) x) σ₁ 1 := Run.read e₁
  have r₂ : Run (.read "m") σ₁ σ₂ 1 := Run.read rfl
  have r₃ : Run (.assign "len" (.add (.var "n") (.lit 1))) σ₂ σ₃ 4 :=
    (Run.assign (v := n + 1) (by simp [hσ₂, hσ₁, initEnv])).mono (by simp)
  -- the offsets
  obtain ⟨σ₄, O, r₄, hoff₄, hO₄, harr₄, hinp₄, hout₄, hvar₄⟩ :=
    readLoop_run (a := "off") (lim := "len") (by decide) (by decide) (σ := σ₃)
      (g := fun _ => 0) (k := n + 1) (ys := ys) (rest := zs)
      (by simp [hσ₃, hσ₂, hσ₁, initEnv, ccExt, replicate_eq_arrOf])
      (by simp [hσ₃]) hys (by simp [hσ₃, hσ₂, hsplit])
  have hO : ∀ i ≤ n, O i = offset x i := fun i hi => by
    rw [hO₄ i (by omega), hyd i (by omega)]
  -- the targets
  set σ₅ : Env := σ₄.setVar "len" (2 * m) with hσ₅
  have r₅ : Run (.assign "len" (.add (.var "m") (.var "m"))) σ₄ σ₅ 4 :=
    (Run.assign (v := 2 * m)
      (by simp [hvar₄ "m" (by decide) (by decide), hσ₃, hσ₂, hσ₁, initEnv, two_mul])).mono
        (by simp)
  obtain ⟨σ₆, T, r₆, htgt₆, hT₆, harr₆, hinp₆, hout₆, hvar₆⟩ :=
    readLoop_run (a := "tgt") (lim := "len") (by decide) (by decide) (σ := σ₅)
      (g := fun _ => 0) (k := 2 * m) (ys := zs) (rest := [])
      (by rw [hσ₅, arrs_setVar, harr₄ "tgt" (by decide)]
          simp [hσ₃, hσ₂, hσ₁, initEnv, ccExt, replicate_eq_arrOf])
      (by simp [hσ₅]) hzs (by simp [hσ₅, hinp₄])
  have hT : ∀ j < 2 * m, T j = target x j := fun j hj => by rw [hT₆ j hj, hzd j hj]
  -- the labels, cleared
  obtain ⟨σ₇, L₀, r₇, hlab₇, hL₀, harr₇, hinp₇, hout₇, hvar₇⟩ :=
    initLab_run (σ := σ₆) (g := fun _ => 0) (n := n)
      (by rw [harr₆ "lab" (by decide), hσ₅, arrs_setVar, harr₄ "lab" (by decide)]
          simp [hσ₃, hσ₂, hσ₁, initEnv, ccExt, replicate_eq_arrOf])
      (by rw [hvar₆ "n" (by decide) (by decide), hσ₅, vars_setVar,
              if_neg (by decide : "n" ≠ "len"), hvar₄ "n" (by decide) (by decide)]
          simp [hσ₃, hσ₂, hσ₁, initEnv])
  -- the four scalars the sweep starts from
  set σ₁₁ : Env := (((σ₇.setVar "u" 0).setVar "head" 0).setVar "tail" 0).setVar "sc" 0
    with hσ₁₁
  have r₈ : Run (.assign "u" (.lit 0)) σ₇ (σ₇.setVar "u" 0) 2 :=
    (Run.assign (v := 0) rfl).mono (by simp)
  have r₉ : Run (.assign "head" (.lit 0)) (σ₇.setVar "u" 0)
      ((σ₇.setVar "u" 0).setVar "head" 0) 2 := (Run.assign (v := 0) rfl).mono (by simp)
  have r₁₀ : Run (.assign "tail" (.lit 0)) ((σ₇.setVar "u" 0).setVar "head" 0)
      (((σ₇.setVar "u" 0).setVar "head" 0).setVar "tail" 0) 2 :=
    (Run.assign (v := 0) rfl).mono (by simp)
  have r₁₁ : Run (.assign "sc" (.lit 0)) (((σ₇.setVar "u" 0).setVar "head" 0).setVar "tail" 0)
      σ₁₁ 2 := (Run.assign (v := 0) rfl).mono (by simp)
  -- what the sweep starts from
  have hn₇ : σ₇.vars "n" = n := by
    rw [hvar₇ "n" (by decide), hvar₆ "n" (by decide) (by decide), hσ₅, vars_setVar,
      if_neg (by decide : "n" ≠ "len"), hvar₄ "n" (by decide) (by decide)]
    simp [hσ₃, hσ₂, hσ₁, initEnv]
  have hm₇ : σ₇.vars "m" = m := by
    rw [hvar₇ "m" (by decide), hvar₆ "m" (by decide) (by decide), hσ₅, vars_setVar,
      if_neg (by decide : "m" ≠ "len"), hvar₄ "m" (by decide) (by decide)]
    simp [hσ₃, hσ₂, hσ₁, initEnv]
  have hoff₇ : σ₇.arrs "off" = arrOf (n + 1) O := by
    rw [harr₇ "off" (by decide), harr₆ "off" (by decide), hσ₅, arrs_setVar, hoff₄]
  have htgt₇ : σ₇.arrs "tgt" = arrOf (2 * m) T := by
    rw [harr₇ "tgt" (by decide), htgt₆]
  have hq₇ : σ₇.arrs "q" = arrOf n (fun _ => 0) := by
    rw [harr₇ "q" (by decide), harr₆ "q" (by decide), hσ₅, arrs_setVar,
      harr₄ "q" (by decide)]
    simp [hσ₃, hσ₂, hσ₁, initEnv, ccExt, replicate_eq_arrOf]
  have hout₇' : σ₇.out = [] := by
    rw [hout₇, hout₆, hσ₅, out_setVar, hout₄]
    simp [hσ₃, hσ₂, hσ₁, initEnv]
  -- the sweep
  have hI : SweepInv x n m G O T σ₁₁ := by
    refine ⟨by simp [hσ₁₁, hn₇], by simp [hσ₁₁, hm₇], by simp [hσ₁₁],
      by simp [hσ₁₁, hoff₇], by simp [hσ₁₁, htgt₇], by simp [hσ₁₁],
      L₀, fun _ => 0, by simp [hσ₁₁, hlab₇], by simp [hσ₁₁, hq₇],
      ⟨fun w hw => Or.inl (hL₀ w hw), by simp [hσ₁₁], by simp [hσ₁₁],
        by simp [hσ₁₁], ?_, by simp [hσ₁₁], by simp [hσ₁₁]⟩,
      ?_, ?_, by simp [hσ₁₁]⟩
    · intro w hw hlw
      exact absurd (hL₀ w hw) hlw
    · intro w hw hlw
      simp [hσ₁₁] at hlw
    · intro w hw hlw
      exact absurd (hL₀ w hw) hlw
  obtain ⟨σ₁₂, L, K, r₁₂, hn₁₂, hlab₁₂, hL, hpay⟩ := sweep_run hx hm hO hT hI
  have hK : K ≤ 60 * m + 50 * n + 4 := by
    have hsp : SweepPot n m σ₁₁ = 60 * m + 50 * n := by
      simp [hσ₁₁, SweepPot, Pot]; omega
    omega
  have hout₁₂ : σ₁₂.out = [] := by
    rw [← show σ₁₁.out = [] by simp [hσ₁₁, hout₇']]
    exact r₁₂.out_eq (by simp [Com.NoWrite, outerBody, drain, expandBody, scanBody])
  -- the labels, written out
  obtain ⟨σ₁₃, r₁₃, hout₁₃⟩ := writeLoop_run hlab₁₂ hn₁₂
  have s₁₂ := Run.seq (r₁₂.mono hK) r₁₃
  have s₁₁ := Run.seq r₁₁ s₁₂
  have s₁₀ := Run.seq r₁₀ s₁₁
  have s₉ := Run.seq r₉ s₁₀
  have s₈ := Run.seq r₈ s₉
  have s₇ := Run.seq r₇ s₈
  have s₆ := Run.seq r₆ s₇
  have s₅ := Run.seq r₅ s₆
  have s₄ := Run.seq r₄ s₅
  have s₃ := Run.seq r₃ s₄
  have s₂ := Run.seq r₂ s₃
  refine ⟨σ₁₃, _, Run.seq r₁ s₂, ?_, ?_⟩
  · rw [hout₁₃, hout₁₂, List.nil_append]
    refine List.ext_getElem (by simp [ccLabels]) fun i h₁ h₂ => ?_
    simp only [List.length_map, List.length_range] at h₁
    rw [List.getElem_map, List.getElem_range, hL i h₁, lbl_eq h₁]
    simp [ccLabels]
  · rw [hxr] at hlen ⊢
    simp at hlen ⊢
    omega

end Lax11Proofs.CC
