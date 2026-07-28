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

The driver takes its value bound from the input word and nothing else:
every number it ever holds is a vertex, an offset, a counter of either,
or a number it read, and each of those is below the length of the word,
by `mem_lt_length` and by the encoding's own conditions. So the single
hypothesis `x.length ≤ B` is what the whole run needs, and it is what
becomes the word-length hypothesis of the statement.

The driver's thirteen commands are walked by `run_vcg`, which assembles
the run, adds the costs and proves the announced bound. It is handed
three specifications, and the *grouping* is what matters: the four
commands that fill the arrays go over as one, matched as a prefix of the
block. A handed specification gives back a state the walk knows nothing
else about, so every fact the sweep needs must be carried in a
postcondition — but inside one specification those facts are read off
the runs it already holds, one `frame_var` apiece and at any distance.
Forward composition pays per phase; a frame lookup pays per fact.

`outerBody_run` stays hand-built, and honestly so: a turn of the sweep
pays for itself out of the potential, which neither a `Spec`'s single
cost nor the walk's `K ≤` shape can state.
-/

namespace Lax11Proofs.CC

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding Lax11.ConnectedComponents
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax11Proofs.Labels
open Lax13Proofs.Reasoning.Lib

variable {x : List ℕ} {B n m : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}

/-! ### The sweep over the vertices -/

/-- The invariant of the outer loop: between searches the queue is
exhausted, every component below `u` is labelled, and no label above
`u` has been written. -/
def SweepInv (x : List ℕ) (n m : ℕ) (G : SimpleGraph (Fin n)) (O T : ℕ → ℕ)
    (τ : Env) : Prop :=
  τ.vars "n" = n ∧ τ.vars "u" ≤ n ∧
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
    (hnB : n < B) (hmB : 2 * m < B)
    {τ : Env} (hI : SweepInv x n m G O T τ)
    (hc : (Cond.lt (.var "u") (.var "n")).evalB B τ = some true) :
    ∃ τ' K, Run B outerBody τ τ' K ∧ SweepInv x n m G O T τ' ∧
      1 + (Cond.lt (Expr.var "u") (Expr.var "n")).size + K + SweepPot n m τ'
        ≤ SweepPot n m τ := by
  obtain ⟨hn, hun, hoff, htgt, hht, L, Q, hlab, hq, hB, hdone, hlow, hsum⟩ := hI
  have hu : τ.vars "u" < n := by simp [hn] at hc; omega
  have hhd := hB.hd
  have htl := hB.tl
  have hLun : L (τ.vars "u") ≤ n := hB.lab_le hu
  by_cases hLu : L (τ.vars "u") = n
  · -- an unlabelled vertex: it is the least of its component, so search from it
    have hlu : lbl G (τ.vars "u") = τ.vars "u" := by
      have h₁ := lbl_le (G := G) hu
      have h₂ : ¬ lbl G (τ.vars "u") < τ.vars "u" := fun h => hdone _ hu h hLu
      omega
    have htail : τ.vars "tail" < n := hB.tail_lt hu hLu
    have hceval : (Cond.eq (.get "lab" (.var "u")) (.var "n")).evalB B τ = some true := by
      simp [hlab, getElem?_arrOf L hu, hn, hLu]; omega
    -- the state the search starts from: the root labelled with itself and
    -- put on the queue, which is `Base.enqueue`
    have hdrainI : DrainInv x n m (τ.vars "u") G O T
        (((τ.setArr "lab" (τ.vars "u") (τ.vars "u")).setArr "q" (τ.vars "tail")
          (τ.vars "u")).setVar "tail" (τ.vars "tail" + 1)) := by
      refine ⟨upd L (τ.vars "u") (τ.vars "u"), upd Q (τ.vars "tail") (τ.vars "u"),
        ⟨by simp [hn], by simp, by simp [hoff], by simp [htgt],
          by simp [hlab, set_arrOf_eq_upd], by simp [hq, set_arrOf_eq_upd]⟩,
        ⟨by simpa using hB.enqueue hu hLu hlu, fun z hz hlz => ?_, fun z hz hlz => ?_,
          by simp; omega, fun i hi₁ hi₂ => ?_⟩, ?_⟩
      · by_cases hzu : z = τ.vars "u"
        · rw [hzu, upd_self]; omega
        · rw [upd_of_ne _ hzu]; exact hdone z hz (by simpa using hlz)
      · by_cases hzu : z = τ.vars "u"
        · rw [hzu, upd_self]
        · rw [upd_of_ne _ hzu] at hlz ⊢; exact le_of_lt (hlow z hz hlz)
      · simp only [vars_setVar, vars_setArr] at hi₁ hi₂
        rw [show i = τ.vars "tail" by simp at hi₁ hi₂; omega, upd_self, upd_self]
      · show τ.vars "sc" = _
        rw [hsum]
        exact Finset.sum_congr rfl fun i hi => by
          rw [upd_of_ne _ (show i ≠ τ.vars "tail" by simp at hi; omega)]
    obtain ⟨τ₄, K₄, hdrun, hdI, hdhead, hdpay⟩ :=
      drain_run hx hm hO hT hu hnB hmB hdrainI
    obtain ⟨L₄, Q₄, ⟨hn₄, hu₄, hoff₄, htgt₄, hlab₄, hq₄⟩, hL₄, hsum₄⟩ := hdI
    have htl₄ := hL₄.base.tl
    refine ⟨τ₄.setVar "u" (τ.vars "u" + 1), _,
      Run.seq (Run.ite_true hceval
        (Run.seq (Run.store (idx := τ.vars "u") (v := τ.vars "u")
            (by simp; omega) (by simp; omega) (by simp [hlab, hu]))
          (Run.seq (Run.store (idx := τ.vars "tail") (v := τ.vars "u")
              (by simp; omega) (by simp; omega) (by simp [hq, htail]))
            (Run.seq (Run.assign (v := τ.vars "tail" + 1) (by simp; omega)) hdrun))))
        (Run.assign (v := τ.vars "u" + 1) (by simp [hu₄]; omega)), ?_, ?_⟩
    · refine ⟨by simp [hn₄], by simp; omega, by simp [hoff₄],
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
      simp only [size_condLt, size_condEq, size_get, Expr.add_def, size_bin, size_lit, size_var]
      omega
  · -- an already labelled vertex: nothing to do
    have hceval : (Cond.eq (.get "lab" (.var "u")) (.var "n")).evalB B τ = some false := by
      simp [hlab, getElem?_arrOf L hu, hn]
      omega
    refine ⟨τ.setVar "u" (τ.vars "u" + 1), _,
      Run.seq (Run.ite_false hceval Run.skip)
        (Run.assign (v := τ.vars "u" + 1) (by simp; omega)),
      ?_, ?_⟩
    · refine ⟨by simp [hn], by simp; omega, by simp [hoff], by simp [htgt],
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
      simp only [size_condLt, size_condEq, size_get, Expr.add_def, size_bin, size_lit, size_var]
      omega

/-- What the sweep leaves: the labels, and an output tape still empty. -/
abbrev Swept (n : ℕ) (G : SimpleGraph (Fin n)) (τ : Env) : Prop :=
  ∃ L, τ.vars "n" = n ∧ τ.arrs "lab" = arrOf n L ∧ τ.out = [] ∧ ∀ w < n, L w = lbl G w

/-- The sweep, as a specification with a constant cost — the potential
at entry, which the caller bounds once. The two array functions are
existential in the precondition and absent from the conclusion, because
the phase that fills the arrays runs *inside* the block this
specification is a step of: `run_vcg` elaborates what it is handed
before it starts walking, so a handed specification cannot mention
anything a step before it produced. -/
theorem sweep_spec (hx : EncodesGraph x n G) (hm : edgeCount x = m)
    (hnB : n < B) (hmB : 2 * m < B) (Kp : ℕ) :
    Spec B (fun τ => ∃ O T, (∀ i ≤ n, O i = offset x i) ∧ (∀ j < 2 * m, T j = target x j) ∧
        SweepInv x n m G O T τ ∧ SweepPot n m τ ≤ Kp ∧ τ.out = [])
      (.while (.lt (.var "u") (.var "n")) outerBody) (fun _ τ' => Swept n G τ') (Kp + 4) := by
  rintro τ ⟨O, T, hO, hT, hI⟩
  refine Spec.run ((Spec.while_potential (K := Kp + 4)
    (P := fun τ => SweepInv x n m G O T τ ∧ SweepPot n m τ ≤ Kp ∧ τ.out = [])
    (SweepInv x n m G O T) (SweepPot n m)
    (fun σ hσ => by obtain ⟨hn, hun, -⟩ := hσ; exact evalB_condLt_vars (by omega) (by omega))
    (fun σ hσ hc => outerBody_run hx hm hO hT hnB hmB hσ hc)
    (fun _ h => h.1) (fun _ h => by have := h.2.1; simp; omega)).frame.post
      (Q' := fun _ τ' => Swept n G τ') ?_) hI
  rintro σ σ' ⟨-, -, hout⟩ ⟨⟨hI', hfalse⟩, -, -, -, hout'⟩
  obtain ⟨hn', hun', -, -, -, L, Q, hlab', -, hB', hdone', -, -⟩ := hI'
  have hun : σ'.vars "u" = n := by simp [hn'] at hfalse; omega
  exact ⟨L, hn', hlab', (hout' (by decide)).trans hout, fun w hw =>
    (hB'.lab w hw).resolve_left (hdone' w hw (by rw [hun]; exact lbl_lt hw))⟩

/-! ### The driver, end to end

What is left is bookkeeping. The only choice is the array extents, and
they are the obvious ones — the encoding says how long the offset and
target arrays are, and the labels and the queue need one entry per
vertex. -/

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

/-- Writing the labels out, which is where the run meets the concept:
what lands on the tape is `ccLabels G` itself. -/
theorem write_spec (hnB : n < B) :
    Spec B (Swept n G) writeLoop (fun _ σ' => σ'.out = ccLabels G) (11 * n + 6) := by
  rintro σ ⟨L, hn, hlab, hout₀, hL⟩
  obtain ⟨σ', hr, hout⟩ := writeLoop_run (B := B) hlab hn hnB
    (fun i hi => by rw [hL i hi]; have := lbl_lt (G := G) hi; omega)
  refine ⟨σ', hr, ?_⟩
  show σ'.out = ccLabels G
  rw [hout, hout₀, List.nil_append]
  refine List.ext_getElem (by simp [ccLabels]) fun i h₁ h₂ => ?_
  simp only [List.length_map, List.length_range] at h₁
  rw [List.getElem_map, List.getElem_range, hL i h₁, lbl_eq h₁]
  simp [ccLabels]

/-- What the setup leaves: the three arrays filled, the queue still
empty, and nothing written. Naming it is what lets the sweep's
obligation read it back off the walk's context. -/
abbrev SetupPost (x : List ℕ) (n m : ℕ) (τ : Env) : Prop :=
  ∃ O T L, (∀ i ≤ n, O i = offset x i) ∧ (∀ j < 2 * m, T j = target x j) ∧
    (∀ i < n, L i = n) ∧ τ.vars "n" = n ∧ τ.arrs "off" = arrOf (n + 1) O ∧
    τ.arrs "tgt" = arrOf (2 * m) T ∧ τ.arrs "lab" = arrOf n L ∧
    τ.arrs "q" = arrOf n (fun _ => 0) ∧ τ.out = []

/-- The whole run of the driver on an encoded graph: the labels come
out, the cost is linear in the length of the word, and every value the
run produces stays below any bound the word itself stays below. The
constant is not fought over anywhere — every phase was bounded loosely,
and this is the sum of those bounds, rounded up to the length of the
input. -/
theorem ccCom_run (hx : EncodesGraph x n G) (hm : edgeCount x = m) (hB : x.length ≤ B) :
    ∃ (σ' : Env) (K : ℕ), Run B ccCom (initEnv (ccExt n m) x) σ' K ∧
      K ≤ 84 * (x.length + 1) ∧ σ'.out = ccLabels G := by
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
  -- everything the run holds is an entry of the word, a count of them, or below one
  have hnB : n < B := by omega
  have hmB : 2 * m < B := by omega
  have hn1B : n + 1 < B := by omega
  have hrestB : ∀ v ∈ rest, v < B :=
    fun v hv => lt_of_lt_of_le
      (mem_lt_length hx (by rw [hxr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)))
      hB
  obtain ⟨ys, zs, hys, hzs, hsplit, hyd, hzd⟩ :
      ∃ ys zs, ys.length = n + 1 ∧ zs.length = 2 * m ∧ rest = ys ++ zs ∧
        (∀ i < n + 1, ys.getD i 0 = offset x i) ∧ (∀ j < 2 * m, zs.getD j 0 = target x j) := by
    refine ⟨rest.take (n + 1), rest.drop (n + 1), by simp; omega, by simp; omega,
      (List.take_append_drop _ _).symm, fun i hi => ?_, fun j _ => ?_⟩
    · rw [getD_take hi, offset, hxr, getD_cons_cons]
    · rw [getD_drop, target, hx.vertexCount_eq, hxr]
      rw [show 3 + n + j = 2 + (n + 1 + j) by omega, getD_cons_cons]
  have hysB : ∀ v ∈ ys, v < B :=
    fun v hv => hrestB v (by rw [hsplit]; exact List.mem_append_left _ hv)
  have hzsB : ∀ v ∈ zs, v < B :=
    fun v hv => hrestB v (by rw [hsplit]; exact List.mem_append_right _ hv)
  have e₁ : (initEnv (ccExt n m) x).inp = n :: m :: rest := hxr
  -- the three phases that fill the arrays, as one specification
  have hsetup : Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "m" = m ∧ σ.vars "len" = n + 1 ∧ σ.inp = ys ++ zs ∧
        σ.arrs "off" = arrOf (n + 1) (fun _ => 0) ∧ σ.arrs "tgt" = arrOf (2 * m) (fun _ => 0) ∧
        σ.arrs "lab" = arrOf n (fun _ => 0) ∧ σ.arrs "q" = arrOf n (fun _ => 0) ∧ σ.out = [])
      (.seq (readLoop "off" "len") (.seq (.assign "len" (.add (.var "m") (.var "m")))
        (.seq (readLoop "tgt" "len") initLab)))
      (fun _ σ' => SetupPost x n m σ') (23 * n + 24 * m + 34) := by
    rintro σ ⟨hn, hm', hlen', hinp, hoff, htgt, hlab, hq, hout⟩
    obtain ⟨σ₄, O, r₄, hoff₄, hO₄, hinp₄⟩ :=
      readLoop_run (B := B) (a := "off") (lim := "len") (by decide) (by decide)
        hoff hlen' hys hinp hn1B hysB
    have r₅ : Run B (.assign "len" (.add (.var "m") (.var "m"))) σ₄
        (σ₄.setVar "len" (2 * m)) 4 :=
      (Run.assign (v := 2 * m)
        (by simp [(r₄.frame_var "m" (by decide)).trans hm', two_mul]; omega)).mono (by simp)
    obtain ⟨σ₆, T, r₆, htgt₆, hT₆, hinp₆⟩ :=
      readLoop_run (B := B) (a := "tgt") (lim := "len") (by decide) (by decide)
        (σ := σ₄.setVar "len" (2 * m)) (g := fun _ => 0) (k := 2 * m) (ys := zs) (rest := [])
        (by simp [(r₄.frame_arr "tgt" (by decide)).trans htgt]) (by simp) hzs
        (by simp [hinp₄]) hmB hzsB
    obtain ⟨σ₇, L₀, r₇, hlab₇, hL₀⟩ :=
      initLab_run (B := B) (σ := σ₆) (g := fun _ => 0) (n := n)
        (by simp [r₆.frame_arr "lab" (by decide), r₄.frame_arr "lab" (by decide), hlab])
        (by simp [r₆.frame_var "n" (by decide), r₄.frame_var "n" (by decide), hn]) hnB
    exact ⟨σ₇, (r₄.seq (r₅.seq (r₆.seq r₇))).mono (by omega), O, T, L₀,
      fun i hi => by rw [hO₄ i (by omega), hyd i (by omega)],
      fun j hj => by rw [hT₆ j hj, hzd j hj], hL₀,
      by simp [r₇.frame_var "n" (by decide), r₆.frame_var "n" (by decide),
        r₄.frame_var "n" (by decide), hn],
      by simp [r₇.frame_arr "off" (by decide), r₆.frame_arr "off" (by decide), hoff₄],
      by simp [r₇.frame_arr "tgt" (by decide), htgt₆], hlab₇,
      by simp [r₇.frame_arr "q" (by decide), r₆.frame_arr "q" (by decide),
        r₄.frame_arr "q" (by decide), hq],
      by simp [r₇.out_eq (by decide), r₆.out_eq (by decide), r₄.out_eq (by decide), hout]⟩
  run_vcg [hsetup, sweep_spec hx hm hnB hmB (60 * m + 50 * n), write_spec (G := G) hnB]
  · -- the output tape is what the write phase said it would be
    assumption
  -- the two header entries are words, being entries of the word
  · simp [e₁]; omega
  · simp [e₁]; omega
  · -- the setup starts on a zeroed layout with the tape at the offsets
    simp [hxr, hsplit, initEnv, ccExt, replicate_eq_arrOf]
  · -- the sweep starts from what the setup left and four zeroed scalars
    obtain ⟨O, T, L₀, hO, hT, hL₀, hn₇, hoff₇, htgt₇, hlab₇, hq₇, hout₇⟩ :=
      ‹SetupPost x n m _›
    refine ⟨O, T, hO, hT, ⟨by simp [hn₇], by simp, by simp [hoff₇], by simp [htgt₇], by simp,
      L₀, fun _ => 0, by simp [hlab₇], by simp [hq₇],
      ⟨fun w hw => Or.inl (hL₀ w hw), by simp, by simp, by simp, ?_, by simp, by simp⟩,
      ?_, ?_, by simp⟩, by simp [SweepPot, Pot]; omega, by simp [hout₇]⟩
    · intro w hw hlw
      exact absurd (hL₀ w hw) hlw
    · intro w hw hlw
      simp at hlw
    · intro w hw hlw
      exact absurd (hL₀ w hw) hlw
  · -- and the write phase from what the sweep left
    assumption

end Lax11Proofs.CC
