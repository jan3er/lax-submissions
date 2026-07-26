import Lax11Proofs.CCGraph
import Lax11Proofs.CCPhases

/-!
The search: scanning one block, emptying the queue, and the sweep over
the vertices.

Everything rests on one observation, which is what keeps the invariant
small: **a label, once written, is already the right one.** A vertex is
labelled only when it is found from a root `u` that was unlabelled when
the sweep reached it, and such a `u` is the least vertex of its own
component; so the label written is the label the answer calls for. The
array therefore always holds, at each vertex, either the marker `n` or
the true label, and the algorithm's remaining job is only to *reach*
every vertex.

`Base` is what holds throughout the run, whichever search is going on:
the labels are right or absent, the queue holds exactly the labelled
vertices without repetition, and everything before `head` has had its
whole block looked at — with its neighbours getting *its* label, not
the current root's, which is what makes that clause survive the change
of root. `Live` adds what holds only inside a search from `u`.

The queue is never reset, so `Base` speaks about all of it and the
searches are told apart only by `Live.cur`, the fact that the part
still to be expanded belongs to the current search. That is what buys
the cost argument its global budget.
-/

namespace Lax11Proofs.CC

open Lax11.Ram Lax11.GraphEncoding Lax11.ConnectedComponents
open Lax11Proofs.Imp Lax11Proofs.Compile Lax11Proofs.Reasoning

variable {x : List ℕ} {n m u head tail : ℕ} {G : SimpleGraph (Fin n)} {O T L Q : ℕ → ℕ}

/-! ### What holds throughout the run -/

/-- The state of the label array and the queue, at any point of the
run. -/
structure Base (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) (L Q : ℕ → ℕ)
    (head tail : ℕ) : Prop where
  /-- A written label is the right label. -/
  lab : ∀ w < n, L w = n ∨ L w = lbl G w
  /-- The queue is a segment. -/
  hd : head ≤ tail
  /-- The queue holds vertices. -/
  tl : tail ≤ n
  /-- Everything on the queue is a labelled vertex. -/
  qmem : ∀ i < tail, Q i < n ∧ L (Q i) ≠ n
  /-- Every labelled vertex is on the queue. -/
  qall : ∀ w < n, L w ≠ n → ∃ i < tail, Q i = w
  /-- Nothing is on the queue twice. -/
  qinj : ∀ i < tail, ∀ j < tail, Q i = Q j → i = j
  /-- The block of a vertex before `head` has been looked at, and its
  neighbours carry that vertex's own label. -/
  exp : ∀ i < head, ∀ j, offset x (Q i) ≤ j → j < offset x (Q i + 1) →
    L (target x j) = L (Q i)

/-- What holds during a search from the root `u`. -/
structure Live (x : List ℕ) (n u : ℕ) (G : SimpleGraph (Fin n)) (L Q : ℕ → ℕ)
    (head tail : ℕ) : Prop where
  /-- The state of the arrays. -/
  base : Base x n G L Q head tail
  /-- Every component below `u` is done. -/
  done : ∀ w < n, lbl G w < u → L w ≠ n
  /-- No label above `u` has been written. -/
  low : ∀ w < n, L w ≠ n → L w ≤ u
  /-- The root is labelled. -/
  root : L u ≠ n
  /-- What is left on the queue belongs to this search. -/
  cur : ∀ i, head ≤ i → i < tail → L (Q i) = u

/-- An unlabelled vertex is not on the queue, so there is room for one
more. -/
theorem Base.tail_lt (hB : Base x n G L Q head tail) {w : ℕ} (hw : w < n)
    (hL : L w = n) : tail < n := by
  have hsub : (Finset.range tail).image Q ⊆ (Finset.range n).erase w := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
    have hi' := Finset.mem_range.1 hi
    refine Finset.mem_erase.2 ⟨fun h => (hB.qmem i hi').2 (h ▸ hL), ?_⟩
    exact Finset.mem_range.2 (hB.qmem i hi').1
  have hcard : ((Finset.range tail).image Q).card = tail := by
    rw [Finset.card_image_of_injOn (fun i hi j hj h =>
      hB.qinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) h)]
    exact Finset.card_range tail
  have := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_range.2 hw), Finset.card_range] at this
  omega

/-- **The exit argument.** When the queue is empty, the labelled
vertices are closed under adjacency, hence under reachability. -/
theorem Base.rch_labelled (hx : EncodesGraph x n G) (hB : Base x n G L Q tail tail)
    {a b : ℕ} (h : Rch G a b) (ha : L a ≠ n) : L b ≠ n := by
  refine rch_closed (P := fun z => L z ≠ n) ?_ h ha
  intro c d hcd hc
  obtain ⟨i, hi, rfl⟩ := hB.qall c hcd.1 hc
  obtain ⟨j, hj₁, hj₂, hj₃⟩ := slot_of_adjn hx hcd
  rw [← hj₃, hB.exp i hi j hj₁ hj₂]
  exact hc

/-! ### The state of the machine -/

/-- The arrays and the three scalars that a search does not move. -/
def SearchEnv (n m u : ℕ) (O T L Q : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "n" = n ∧ τ.vars "m" = m ∧ τ.vars "u" = u ∧
  τ.arrs "off" = arrOf (n + 1) O ∧ τ.arrs "tgt" = arrOf (2 * m) T ∧
  τ.arrs "lab" = arrOf n L ∧ τ.arrs "q" = arrOf n Q

/-- The potential the search is paid out of: thirty units per adjacency
slot not yet looked at, twenty-three per vertex not yet enqueued, and
twenty-three per vertex waiting on the queue. -/
def Pot (n m : ℕ) (τ : Env) : ℕ :=
  30 * (2 * m - τ.vars "sc") + 23 * (n - τ.vars "tail") +
    23 * (τ.vars "tail" - τ.vars "head")

/-! ### Scanning one block -/

/-- The invariant of the scan loop: a live search, the position reached
in the block of `v`, and the two facts that make the scan a step of the
search — what has been looked at is labelled `u`, and the queue below
`head` has not moved. -/
def ScanInv (x : List ℕ) (n m u v head sc₀ : ℕ) (G : SimpleGraph (Fin n))
    (O T Q₀ : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ L Q, SearchEnv n m u O T L Q τ ∧ Live x n u G L Q head (τ.vars "tail") ∧
    τ.vars "head" = head ∧ head < τ.vars "tail" ∧ Q head = v ∧
    τ.vars "v" = v ∧ τ.vars "jend" = offset x (v + 1) ∧
    offset x v ≤ τ.vars "j" ∧ τ.vars "j" ≤ offset x (v + 1) ∧
    τ.vars "sc" = sc₀ + (τ.vars "j" - offset x v) ∧
    (∀ j', offset x v ≤ j' → j' < τ.vars "j" → L (target x j') = u) ∧
    (∀ i < head, Q i = Q₀ i)

/-- One slot of the block of `v`: if it names an unlabelled vertex,
that vertex is labelled and enqueued. -/
theorem scanBody_run (hx : EncodesGraph x n G) (hm : edgeCount x = m)
    (hT : ∀ j < 2 * m, T j = target x j) (hu : u < n) {v head sc₀ : ℕ} (hv : v < n)
    {Q₀ : ℕ → ℕ} {τ : Env} (hI : ScanInv x n m u v head sc₀ G O T Q₀ τ)
    (hcond : (Cond.lt (.var "j") (.var "jend")).eval τ = some true) :
    ∃ τ', Run scanBody τ τ' 26 ∧ ScanInv x n m u v head sc₀ G O T Q₀ τ' ∧
      (offset x (v + 1) - τ'.vars "j") < (offset x (v + 1) - τ.vars "j") := by
  obtain ⟨L, Q, ⟨hn, hmm, hup, hoff, htgt, hlab, hq⟩, hL, hhead, hht, hqv, hvv, hje,
    hj₁, hj₂, hsc, hscan, hq₀⟩ := hI
  have hB := hL.base
  have hjlt : τ.vars "j" < offset x (v + 1) := by simp [hje] at hcond; omega
  have h2m : offset x (v + 1) ≤ 2 * m := hm ▸ offset_le hx (by omega)
  have hjm : τ.vars "j" < 2 * m := by omega
  obtain ⟨w, hw⟩ : ∃ w, target x (τ.vars "j") = w := ⟨_, rfl⟩
  have hwn : w < n := hw ▸ target_lt' hx hv hjlt
  have hadj : Adjn G v w := hw ▸ adjn_of_slot hx hv hj₁ hjlt
  have hLv : L v = u := hqv ▸ hL.cur head le_rfl hht
  have hlv : lbl G v = u := by
    have := (hB.lab v hv).resolve_left (by rw [hLv]; omega)
    omega
  have hlw : lbl G w = u := by
    have := lbl_eq_of_rch (Rch.of_adjn hadj); omega
  have hteval : (Expr.get "tgt" (.var "j")).eval τ = some w := by
    simp [htgt, getElem?_arrOf T hjm, hT _ hjm, hw]
  by_cases hnew : L w = n
  · -- unlabelled: label it and enqueue it
    have htail : τ.vars "tail" < n := hB.tail_lt hwn hnew
    have hceval : (Cond.eq (.get "lab" (.var "w")) (.var "n")).eval (τ.setVar "w" w)
        = some true := by simp [hlab, getElem?_arrOf L hwn, hn, hnew]
    have hnotexp : ∀ i < head, ∀ j, offset x (Q i) ≤ j → j < offset x (Q i + 1) →
        target x j ≠ w := by
      intro i hi j hj₁' hj₂' hjw
      have h₁ := hB.exp i hi j hj₁' hj₂'
      rw [hjw, hnew] at h₁
      exact (hB.qmem i (by have := hB.hd; omega)).2 h₁.symm
    have hQne : ∀ p, p < τ.vars "tail" → Q p ≠ w := by
      intro p hp hpw
      exact (hB.qmem p hp).2 (by rw [hpw, hnew])
    refine ⟨_, (Run.seq (Run.assign (v := w) hteval)
      (Run.seq (Run.ite_true hceval
        (Run.seq (Run.store (idx := w) (v := u) (by simp) (by simp [hup]) (by simp [hlab, hwn]))
          (Run.seq (Run.store (idx := τ.vars "tail") (v := w)
              (by simp) (by simp) (by simp [hq, htail]))
            (Run.assign (v := τ.vars "tail" + 1) (by simp)))))
        (Run.seq (Run.assign (v := τ.vars "sc" + 1) (by simp))
          (Run.assign (v := τ.vars "j" + 1) (by simp))))).mono (by simp), ?_, by simp; omega⟩
    refine ⟨fun z => if z = w then u else L z, fun i => if i = τ.vars "tail" then w else Q i,
      ⟨by simp [hn], by simp [hmm], by simp [hup], by simp [hoff], by simp [htgt],
        by simp [hlab, set_arrOf], by simp [hq, set_arrOf]⟩, ?_,
      by simp [hhead], by simp; omega, by simp [hqv, show head ≠ τ.vars "tail" by omega],
      by simp [hvv], by simp [hje], by simp; omega, by simp; omega, by simp [hsc]; omega,
      ?_, ?_⟩
    · refine ⟨⟨?_, by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · -- lab
        intro z hz
        by_cases hzw : z = w
        · exact Or.inr (by simp [hzw, hlw])
        · simpa [if_neg hzw] using hB.lab z hz
      · -- qmem
        intro i hi
        simp only [vars_setVar] at hi
        by_cases hit : i = τ.vars "tail"
        · simp [hit, hwn]; omega
        · have hi' : i < τ.vars "tail" := by simp at hi; omega
          rw [if_neg hit, if_neg (hQne i hi')]
          exact hB.qmem i hi'
      · -- qall
        intro z hz hlz
        by_cases hzw : z = w
        · exact ⟨τ.vars "tail", by simp, by simp [hzw]⟩
        · rw [if_neg hzw] at hlz
          obtain ⟨i, hi, rfl⟩ := hB.qall z hz hlz
          exact ⟨i, by simp; omega, by simp [if_neg (show i ≠ τ.vars "tail" by omega)]⟩
      · -- qinj
        intro i hi j hj hij
        simp only [vars_setVar] at hi hj
        by_cases hit : i = τ.vars "tail" <;> by_cases hjt : j = τ.vars "tail"
        · omega
        · rw [if_pos hit, if_neg hjt] at hij
          exact absurd hij.symm (hQne j (by simp at hj; omega))
        · rw [if_neg hit, if_pos hjt] at hij
          exact absurd hij (hQne i (by simp at hi; omega))
        · rw [if_neg hit, if_neg hjt] at hij
          exact hB.qinj i (by simp at hi; omega) j (by simp at hj; omega) hij
      · -- exp
        intro i hi j hj₁' hj₂'
        have hit : i ≠ τ.vars "tail" := by have := hB.hd; omega
        rw [if_neg hit] at hj₁' hj₂' ⊢
        rw [if_neg (hnotexp i hi j hj₁' hj₂'), if_neg (hQne i (by have := hB.hd; omega))]
        exact hB.exp i hi j hj₁' hj₂'
      · -- done
        intro z hz hlz
        by_cases hzw : z = w
        · simp [hzw]; omega
        · simpa [if_neg hzw] using hL.done z hz hlz
      · -- low
        intro z hz hlz
        by_cases hzw : z = w
        · simp [hzw]
        · rw [if_neg hzw] at hlz ⊢; exact hL.low z hz hlz
      · -- root
        by_cases huw : u = w
        · simp [huw]; omega
        · simpa [if_neg huw] using hL.root
      · -- cur
        intro i hi₁ hi₂
        simp only [vars_setVar] at hi₁ hi₂
        by_cases hit : i = τ.vars "tail"
        · simp [hit]
        · have hi' : i < τ.vars "tail" := by simp at hi₂; omega
          rw [if_neg hit, if_neg (hQne i hi')]
          exact hL.cur i (by omega) hi'
    · intro j' hj₁' hj₂'
      simp only [vars_setVar] at hj₂'
      by_cases hyw : target x j' = w
      · simp [hyw]
      · simp only [if_neg hyw]
        rcases Nat.lt_or_ge j' (τ.vars "j") with h | h
        · exact hscan j' hj₁' h
        · exact absurd (show j' = τ.vars "j" by simp at hj₂'; omega) (by
            rintro rfl; exact hyw hw)
    · intro i hi
      have hit : i ≠ τ.vars "tail" := by have := hB.hd; omega
      simp only [if_neg hit]; exact hq₀ i hi
  · -- already labelled, and by this search
    have hLw : L w = u := by
      have := (hB.lab w hwn).resolve_left hnew; omega
    have hceval : (Cond.eq (.get "lab" (.var "w")) (.var "n")).eval (τ.setVar "w" w)
        = some false := by
      simp [hlab, getElem?_arrOf L hwn, hn, hLw]; omega
    refine ⟨_, (Run.seq (Run.assign (v := w) hteval)
      (Run.seq (Run.ite_false hceval Run.skip)
        (Run.seq (Run.assign (v := τ.vars "sc" + 1) (by simp))
          (Run.assign (v := τ.vars "j" + 1) (by simp))))).mono (by simp), ?_, by simp; omega⟩
    refine ⟨L, Q, ⟨by simp [hn], by simp [hmm], by simp [hup], by simp [hoff], by simp [htgt],
      by simp [hlab], by simp [hq]⟩, by simpa using hL, by simp [hhead], by simp [hht],
      hqv, by simp [hvv], by simp [hje], by simp; omega, by simp; omega,
      by simp [hsc]; omega, ?_, hq₀⟩
    intro j' hj₁' hj₂'
    simp only [vars_setVar] at hj₂'
    rcases Nat.lt_or_ge j' (τ.vars "j") with h | h
    · exact hscan j' hj₁' h
    · have : j' = τ.vars "j" := by simp at hj₂'; omega
      rw [this, hw]; exact hLw

/-- The whole block of `v`, scanned. -/
theorem scan_run (hx : EncodesGraph x n G) (hm : edgeCount x = m)
    (hT : ∀ j < 2 * m, T j = target x j) (hu : u < n) {v head sc₀ : ℕ} (hv : v < n)
    {Q₀ : ℕ → ℕ} {τ : Env} (hI : ScanInv x n m u v head sc₀ G O T Q₀ τ)
    (hjs : τ.vars "j" = offset x v) :
    ∃ τ', Run (.while (.lt (.var "j") (.var "jend")) scanBody) τ τ' (30 * deg x v + 4) ∧
      ScanInv x n m u v head sc₀ G O T Q₀ τ' ∧ τ'.vars "j" = offset x (v + 1) := by
  obtain ⟨τ', hrun, hI', hfalse⟩ :=
    Run.while_count (b := Cond.lt (.var "j") (.var "jend")) (c := scanBody)
      (ScanInv x n m u v head sc₀ G O T Q₀) (fun σ => offset x (v + 1) - σ.vars "j") 26
      (fun _ _ => ⟨_, rfl⟩) (fun σ h hc => scanBody_run hx hm hT hu hv h hc) hI
  obtain ⟨L₁, Q₁, h₃, h₄, h₅, h₆, h₇, h₈, hje, h₁₀, hjle, h₁₂, h₁₃, h₁₄⟩ := hI'
  have hj : τ'.vars "j" = offset x (v + 1) := by
    simp [hje] at hfalse; omega
  exact ⟨τ', hrun.mono (by simp [deg, hjs]),
    ⟨L₁, Q₁, h₃, h₄, h₅, h₆, h₇, h₈, hje, h₁₀, hjle, h₁₂, h₁₃, h₁₄⟩, hj⟩

/-- Taking one vertex off the queue and scanning its block: the cost is
thirty per slot of that block and nineteen besides. -/
theorem expandBody_run (hx : EncodesGraph x n G) (hm : edgeCount x = m)
    (hO : ∀ i ≤ n, O i = offset x i) (hT : ∀ j < 2 * m, T j = target x j) (hu : u < n)
    {τ : Env} (hSE : SearchEnv n m u O T L Q τ)
    (hL : Live x n u G L Q (τ.vars "head") (τ.vars "tail"))
    (hht : τ.vars "head" < τ.vars "tail")
    (hsc : τ.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head"), deg x (Q i)) :
    ∃ (τ' : Env) (L' Q' : ℕ → ℕ) (K : ℕ), Run expandBody τ τ' K ∧
      SearchEnv n m u O T L' Q' τ' ∧
      Live x n u G L' Q' (τ'.vars "head") (τ'.vars "tail") ∧
      τ'.vars "head" = τ.vars "head" + 1 ∧
      τ'.vars "sc" = ∑ i ∈ Finset.range (τ'.vars "head"), deg x (Q' i) ∧
      τ'.vars "sc" = τ.vars "sc" + deg x (Q (τ.vars "head")) ∧
      K ≤ 30 * deg x (Q (τ.vars "head")) + 19 := by
  obtain ⟨hn, hmm, hup, hoff, htgt, hlab, hq⟩ := hSE
  have hB := hL.base
  have hheadn : τ.vars "head" < n := by have := hB.tl; omega
  obtain ⟨v, hvdef⟩ : ∃ v, Q (τ.vars "head") = v := ⟨_, rfl⟩
  rw [hvdef]
  have hvn : v < n := hvdef ▸ (hB.qmem _ hht).1
  -- read the vertex, its block start and its block end
  have e₁ : (Expr.get "q" (.var "head")).eval τ = some v := by
    simp [hq, getElem?_arrOf Q hheadn, hvdef]
  have e₂ : (Expr.get "off" (.var "v")).eval (τ.setVar "v" v) = some (offset x v) := by
    simp [hoff, getElem?_arrOf O (show v < n + 1 by omega), hO v (by omega)]
  have e₃ : (Expr.get "off" (.add (.var "v") (.lit 1))).eval
      ((τ.setVar "v" v).setVar "j" (offset x v)) = some (offset x (v + 1)) := by
    simp [hoff, getElem?_arrOf O (show v + 1 < n + 1 by omega), hO (v + 1) (by omega)]
  -- the scan
  have hI₃ : ScanInv x n m u v (τ.vars "head") (τ.vars "sc") G O T Q
      (((τ.setVar "v" v).setVar "j" (offset x v)).setVar "jend" (offset x (v + 1))) :=
    ⟨L, Q, ⟨by simp [hn], by simp [hmm], by simp [hup], by simp [hoff], by simp [htgt],
        by simp [hlab], by simp [hq]⟩, by simpa using hL, by simp, by simpa using hht,
      hvdef, by simp, by simp, by simp,
      by simpa using offset_mono' hx (Nat.le_succ v) (show v + 1 ≤ n by omega),
      by simp, by intro j' h₁ h₂; simp at h₂; omega, fun i _ => rfl⟩
  obtain ⟨τ₄, hscan, hI₄, hj₄⟩ := scan_run hx hm hT hu hvn hI₃ (by simp)
  obtain ⟨L', Q', ⟨hn', hmm', hup', hoff', htgt', hlab', hq'⟩, hL', hhead', hht', hqv',
    hvv', hje', hjge', hjle', hsc', hscanned, hq₀'⟩ := hI₄
  refine ⟨τ₄.setVar "head" (τ.vars "head" + 1), L', Q', _,
    Run.seq (Run.assign (v := v) e₁)
      (Run.seq (Run.assign (v := offset x v) e₂)
        (Run.seq (Run.assign (v := offset x (v + 1)) e₃)
          (Run.seq hscan (Run.assign (v := τ.vars "head" + 1) (by simp [hhead']))))),
    ⟨by simp [hn'], by simp [hmm'], by simp [hup'], by simp [hoff'], by simp [htgt'],
      by simp [hlab'], by simp [hq']⟩, ?_, by simp, ?_, ?_, by simp; omega⟩
  · -- the search is live one step further along
    have hLv : L' v = u := by rw [← hqv']; exact hL'.cur _ le_rfl hht'
    refine ⟨⟨hL'.base.lab, by simp; omega, by simpa using hL'.base.tl,
      by simpa using hL'.base.qmem, by simpa using hL'.base.qall,
      by simpa using hL'.base.qinj, ?_⟩,
      hL'.done, hL'.low, hL'.root, ?_⟩
    · intro i hi j hj₁ hj₂
      simp at hi
      rcases Nat.lt_or_ge i (τ.vars "head") with h | h
      · exact hL'.base.exp i h j hj₁ hj₂
      · have hie : i = τ.vars "head" := by omega
        subst hie
        rw [hqv'] at hj₁ hj₂ ⊢
        rw [hLv]
        exact hscanned j hj₁ (by rw [hj₄]; exact hj₂)
    · intro i hi₁ hi₂
      simp at hi₁ hi₂
      exact hL'.cur i (by omega) hi₂
  · -- the count of scanned slots is the sum over the queue
    have hcongr : ∑ i ∈ Finset.range (τ.vars "head"), deg x (Q' i)
        = ∑ i ∈ Finset.range (τ.vars "head"), deg x (Q i) :=
      Finset.sum_congr rfl fun i hi => by rw [hq₀' i (Finset.mem_range.1 hi)]
    show τ₄.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head" + 1), deg x (Q' i)
    rw [Finset.sum_range_succ, hcongr, ← hsc, hqv', hsc', hj₄, deg]
  · show τ₄.vars "sc" = τ.vars "sc" + deg x v
    rw [hsc', hj₄, deg]


/-! ### Emptying the queue -/

/-- The invariant of the search loop. -/
def DrainInv (x : List ℕ) (n m u : ℕ) (G : SimpleGraph (Fin n)) (O T : ℕ → ℕ)
    (τ : Env) : Prop :=
  ∃ L Q, SearchEnv n m u O T L Q τ ∧ Live x n u G L Q (τ.vars "head") (τ.vars "tail") ∧
    τ.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head"), deg x (Q i)

/-- **The search.** The queue is emptied, and the whole cost of doing
so is paid out of the potential — including the scans, whose cost no
constant per turn of the loop could bound. -/
theorem drain_run (hx : EncodesGraph x n G) (hm : edgeCount x = m)
    (hO : ∀ i ≤ n, O i = offset x i) (hT : ∀ j < 2 * m, T j = target x j) (hu : u < n)
    {τ : Env} (hI : DrainInv x n m u G O T τ) :
    ∃ (τ' : Env) (K : ℕ), Run drain τ τ' K ∧ DrainInv x n m u G O T τ' ∧
      τ'.vars "head" = τ'.vars "tail" ∧ K + Pot n m τ' ≤ Pot n m τ + 4 := by
  have hstep : ∀ σ : Env, DrainInv x n m u G O T σ →
      (Cond.lt (.var "head") (.var "tail")).eval σ = some true →
      ∃ σ' K, Run expandBody σ σ' K ∧ DrainInv x n m u G O T σ' ∧
        1 + (Cond.lt (Expr.var "head") (Expr.var "tail")).size + K + Pot n m σ' ≤ Pot n m σ := by
    intro σ hσ hc
    obtain ⟨L₁, Q₁, hSE, hLive, hsum⟩ := hσ
    have hht : σ.vars "head" < σ.vars "tail" := by simp at hc; omega
    obtain ⟨σ', L₂, Q₂, K, hrun, hSE', hLive', hhead', hsum', hsc', hK⟩ :=
      expandBody_run hx hm hO hT hu hSE hLive hht hsum
    refine ⟨σ', K, hrun, ⟨L₂, Q₂, hSE', hLive', hsum'⟩, ?_⟩
    have hhd := hLive'.base.hd
    have h2m : σ'.vars "sc" ≤ 2 * m := by
      rw [hsum', ← hm]
      exact sum_deg_queue hx (fun i hi => (hLive'.base.qmem i (by omega)).1)
        (fun i hi j hj h => hLive'.base.qinj i (by omega) j (by omega) h)
    have htl := hLive'.base.tl
    have hhd0 := hLive.base.hd
    have htl0 := hLive.base.tl
    simp only [Pot, size_condLt, size_var]
    omega
  obtain ⟨τ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_pot (b := Cond.lt (.var "head") (.var "tail")) (c := expandBody)
      (DrainInv x n m u G O T) (Pot n m) (fun _ _ => ⟨_, rfl⟩) hstep hI
  obtain ⟨L₁, Q₁, hSE₁, hL₁, hsum₁⟩ := hI'
  have hhd := hL₁.base.hd
  exact ⟨τ', K, hrun, ⟨L₁, Q₁, hSE₁, hL₁, hsum₁⟩, by simp at hfalse; omega,
    by simpa using hpay⟩

end Lax11Proofs.CC
