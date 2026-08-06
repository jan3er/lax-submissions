import Lax3Proofs.Refine.ScatterBlockBfs
import Lax3Proofs.Refine.ScatterBlockMark
import Lax3Proofs.Refine.ScatterBlockClear

/-!
# The active-set greedy scatter pass

The engine itself: one turn of the member scan, the scan, and the whole
pass. The program is in `ScatterBlockProg.lean`, the charge in
`ScatterBlockCost.lean`, the two loop walks in `ScatterBlockMark.lean`
and `ScatterBlockClear.lean`, and the strengthened block search in
`ScatterBlockBfs.lean`.

**The export is the landed postcondition, character for character.**
`RamScatter.scatter_spec` leaves in `flag` the truth value of the
scatter sentence and says `flag ≤ 1`; so does `scatBlock_spec`. Nothing
downstream sees the difference, which is the point: the atom's answer is
unchanged and only its charge moves, from `scatterCost n ns t` to
`scatBlockK mm bw nb t`.

### What a turn does differently

The landed turn stands at a carrier cell and asks three questions — is
there room, is this cell in the table, is it unexcluded. The active turn
stands at a *member* and asks two, because the first question is
answered by the list it is walking. The invariant is nevertheless
carried at a **carrier** position, `memPos`, so that the landed
recursion `gsel_iff` — which quantifies over all earlier vertices, not
all earlier members — applies verbatim. `progressA_step_gap` is what
moves the invariant from one member to the next across the vertices in
between, and it is sound because everything the process selects is a
member.

### The two charges a pick pays

A pick runs the block search and then marks its ball. Both are charged
to the ball and neither mentions the carrier, but that is only true
because `ScatterBlockBfs.bfsBlockA_specW` re-exports two facts that
`BfsBlock.bfsBlock_spec` computes and drops — that a queue entry is a
vertex, and that the queue is no longer than the ball. Without the
second, the mark walk would be charged `tail ≤ n`, and the carrier term
this whole wave exists to remove would walk straight back in through the
marking pass. See that file's header.
-/

namespace Lax3Proofs.Refine.ScatterBlock

open Lax3.ColoredGraphs Lax3.ScatterSentences
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.RamScatter

variable {n ns nt mm r t : ℕ} {G : SimpleGraph (Fin n)} {M O T Mem : ℕ → ℕ}
  {X : Set (Fin n)}

/-! ### §1 The arena the active pass carries

Three differences from `RamScatter.Arena`: the member count and the
member list are in it, the table array is not, and the distance array is
required *clean*. The last is `BfsBlock`'s clean-in/clean-out contract
lifted to the pass — the pass is handed a clean `dist`, every pick
returns it clean, and the pass hands it back clean.

**The member array is at the carrier's physical length** (rebase F-2,
the length seam). The driver pre-allocates one member array per depth at
`n` cells and fills a live prefix of `mnumName j` of them
(`RamDriver.LevelPre`'s sixteenth clause; the engine entry copies that
prefix into `"mem"` at `CoverBlock.memCopyK mm = 12·mm + 6`). So the
arena pins `σ.arrs "mem" = arrOf n Mem` and not `arrOf mm Mem`: the
physical length is the carrier's, the *contract* is `MemList`'s, and
`MemList` speaks only of `k < mm`. Nothing above the live prefix is
claimed, read, or cleared — a tail clause here would be exactly the
carrier walk the whole variant exists to remove. The walks below index
the array only through `Mem k` for `k < mm`, so every read is in range
by `MemList.card_le`, and no proof of this file needs the tail.
`Refine/ArenaSeam.lean` is the driver-side discharge of the two member
clauses. -/

/-- The part of the machine the active scan carries unchanged. -/
def ArenaA (n nt mm r : ℕ) (O T M Mem : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "mm" = mm ∧
    σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
    σ.arrs "alv" = arrOf n M ∧ σ.arrs "mem" = arrOf n Mem ∧
    σ.arrs "dist" = arrOf n (fun _ => r + 1) ∧
    (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g)

theorem ArenaA.of_eq {σ σ' : Env} (h : ArenaA n nt mm r O T M Mem σ)
    (hv : σ'.vars "n" = σ.vars "n") (hv₂ : σ'.vars "mm" = σ.vars "mm")
    (h₁ : σ'.arrs "off" = σ.arrs "off") (h₂ : σ'.arrs "tgt" = σ.arrs "tgt")
    (h₃ : σ'.arrs "alv" = σ.arrs "alv") (h₄ : σ'.arrs "mem" = σ.arrs "mem")
    (h₅ : σ'.arrs "dist" = σ.arrs "dist") (h₆ : σ'.arrs "q" = σ.arrs "q")
    (h₇ : σ'.arrs "qd" = σ.arrs "qd") : ArenaA n nt mm r O T M Mem σ' := by
  obtain ⟨e₀, e₀', e₁, e₂, e₃, e₄, e₅, ⟨g₆, e₆⟩, ⟨g₇, e₇⟩⟩ := h
  exact ⟨by rw [hv, e₀], by rw [hv₂, e₀'], by rw [h₁, e₁], by rw [h₂, e₂], by rw [h₃, e₃],
    by rw [h₄, e₄], by rw [h₅, e₅], ⟨g₆, by rw [h₆, e₆]⟩, ⟨g₇, by rw [h₇, e₇]⟩⟩

theorem ArenaA.setVar {σ : Env} {x : String} {v : ℕ} (h : ArenaA n nt mm r O T M Mem σ)
    (hx : x ≠ "n") (hx₂ : x ≠ "mm") : ArenaA n nt mm r O T M Mem (σ.setVar x v) :=
  h.of_eq (by simp [Ne.symm hx]) (by simp [Ne.symm hx₂]) rfl rfl rfl rfl rfl rfl rfl

/-- **The block budget.** Every ball in the arena has slot weight at
most `bw` and size at most `nb`. A block-driven consumer passes its own
block and gets the arena-charged reading its interface asks for; this is
`BfsBlock`'s "any finite `A` containing the ball" convention, made
uniform over the sources a pass might pick. -/
def BallBudget (n r : ℕ) (G : SimpleGraph (Fin n)) (M O : ℕ → ℕ) (bw nb : ℕ) : Prop :=
  ∀ s, s < n → ∃ A : Finset ℕ, (∀ v, v < n → M v ≠ 0 → WD G M r s v → v ∈ A) ∧
    (∑ v ∈ A, Csr.rowLen O v) ≤ bw ∧ A.card ≤ nb

/-! ### §2 Frames

The block search and the marking walk both leave the scan's own scalars,
the block structure, the mask and the member list alone. Each is one
`simp` against concrete program text. -/

theorem notMem_bfsBlock_wvars (d : ℕ) (y : String)
    (hy : y ∈ ["n", "src", "sj", "mv", "cnt", "flag", "mm", "mj"]) :
    y ∉ (BfsBlock.bfsBlockCom d).wvars := by
  fin_cases hy <;>
    simp [BfsBlock.bfsBlockCom, BfsBlock.unwind, BfsBlock.unwindSlot, seedSrc, bfsDrain,
      expandRow, scanSlot, Fill.put, Csr.loadRow, Csr.scan, Queue.drain, Com.wvars]

theorem notMem_bfsBlock_warrs (d : ℕ) (a : String)
    (ha : a ∈ ["off", "tgt", "alv", "mem", "exc"]) : a ∉ (BfsBlock.bfsBlockCom d).warrs := by
  fin_cases ha <;>
    simp [BfsBlock.bfsBlockCom, BfsBlock.unwind, BfsBlock.unwindSlot, seedSrc, bfsDrain,
      expandRow, scanSlot, Fill.put, Csr.loadRow, Csr.scan, Queue.drain, Com.warrs]

/-! ### §3 What the mark decides

The landed marking sweep reads the distance array and excludes every
vertex it finds within `r`. The ball walk marks the queue segment and
the source. These are the same set, and this is the lemma that says so.

The two directions are the two ways a vertex can fail to be on the
queue: it is the source, which the search writes but never enqueues when
it is dead; or it is out of range, and then it is not within `r` either.
`alive_of_wd` is what closes the second — a walk that arrives anywhere
but its own start arrives at a live vertex, so a live-ball membership
test is no weaker than a distance test. -/

theorem marked_iff_wd {s w : ℕ} (hs : s < n) (hw : w < n) {tf : ℕ} {Q : ℕ → ℕ}
    (hseg : ∀ v, v < n → ((∃ i, i < tf ∧ Q i = v) ↔ (M v ≠ 0 ∧ WD G M r s v))) :
    ((∃ i, i < tf ∧ Q i = w) ∨ w = s) ↔ WD G M r s w := by
  constructor
  · rintro (hq | rfl)
    · exact ((hseg w hw).1 hq).2
    · exact WD.refl G M r hs
  · intro hwd
    by_cases hws : w = s
    · exact Or.inr hws
    · exact Or.inl ((hseg w hw).2 ⟨BfsBlock.alive_of_wd hwd (Ne.symm hws), hwd⟩)

/-! ### §4 One turn of the member scan

The three control-flow paths a turn has: the count is already enough; an
earlier pick excluded this member; or the member is selected, and then
one block search and one ball walk pay for it. The landed turn had a
fourth — the table said no — and it is gone, because the list is the
table.

Nothing is claimed about the cost beyond the two cases the potential
needs. -/

theorem step_run {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B)
    (hml : MemList n mm Mem X) {bw nb : ℕ} (hbud : BallBudget n r G M O bw nb)
    {σ : Env} (hA : ArenaA n nt mm r O T M Mem σ) (hsj : σ.vars "sj" < mm)
    (hP : ProgressA G M r t X (Mem (σ.vars "sj")) σ) :
    ∃ σ' K, Run B (scatBlockStep r t) σ σ' K ∧ ArenaA n nt mm r O T M Mem σ' ∧
      σ'.vars "sj" = σ.vars "sj" + 1 ∧
      ProgressA G M r t X (Mem (σ.vars "sj") + 1) σ' ∧
      ((σ'.vars "cnt" = σ.vars "cnt" ∧ K ≤ 30) ∨
        (σ'.vars "cnt" = σ.vars "cnt" + 1 ∧ σ.vars "cnt" < t ∧ K ≤ pickBlockK bw nb)) := by
  obtain ⟨hn, hmmv, hoff, htgt, halv, hmem, hdist, hqex, hqdex⟩ := id hA
  have hmmn : mm ≤ n := hml.card_le
  have hsn : Mem (σ.vars "sj") < n := hml.lt _ hsj
  have hsjB : σ.vars "sj" < B := by omega
  have hsB : Mem (σ.vars "sj") < B := by omega
  have hcntt : σ.vars "cnt" ≤ t := hP.cnt_le
  have hcntB : σ.vars "cnt" < B := by omega
  set s := Mem (σ.vars "sj") with hs_def
  -- the read that opens every turn
  have hread : (Expr.get "mem" (.var "sj")).evalB B σ = some s := by
    refine evalB_get (evalB_var (by rw [hmmv] at *; omega)) ?_ hsB
    -- the read is in range because the live prefix is inside the physical array
    rw [hmem, getElem?_arrOf Mem (show σ.vars "sj" < n by omega)]
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, τ = σ.setVar "mv" s := ⟨_, rfl⟩
  have run₀ : Run B (.assign "mv" (.get "mem" (.var "sj"))) σ τ₀ 3 := by
    rw [hτ₀]; exact (Run.assign (v := s) hread).mono (by simp [Expr.size])
  have hv₀ : ∀ y, y ≠ "mv" → τ₀.vars y = σ.vars y := by
    intro y hy; rw [hτ₀]; simp [hy]
  have ha₀ : τ₀.arrs = σ.arrs := by rw [hτ₀]; simp
  have hmv₀ : τ₀.vars "mv" = s := by rw [hτ₀]; simp
  have hA₀ : ArenaA n nt mm r O T M Mem τ₀ := by
    rw [hτ₀]; exact hA.setVar (by decide) (by decide)
  have hP₀ : ProgressA G M r t X s τ₀ :=
    hP.of_eq (hv₀ "cnt" (by decide)) (by rw [ha₀])
  have hcnt₀ : τ₀.vars "cnt" = σ.vars "cnt" := hv₀ "cnt" (by decide)
  -- the assignment that ends every turn
  have hbump : ∀ τ : Env, τ.vars "sj" = σ.vars "sj" →
      Run B (.assign "sj" (.add (.var "sj") (.lit 1))) τ
        (τ.setVar "sj" (σ.vars "sj" + 1)) 4 := by
    intro τ hτ
    refine (Run.assign (v := σ.vars "sj" + 1) ?_).mono (by simp [Expr.size])
    rw [← hτ]
    exact evalB_bin (evalB_var (by rw [hτ]; omega)) (evalB_lit (by omega)) (by simp; omega)
  have hsj₀ : τ₀.vars "sj" = σ.vars "sj" := hv₀ "sj" (by decide)
  -- a turn that leaves the machine alone
  have hnopick : ∀ K₁, Run B (scatBlockBody r t) τ₀ τ₀ K₁ → K₁ ≤ 22 →
      ¬ GSel G M r X s →
      ∃ σ' K, Run B (scatBlockStep r t) σ σ' K ∧ ArenaA n nt mm r O T M Mem σ' ∧
        σ'.vars "sj" = σ.vars "sj" + 1 ∧ ProgressA G M r t X (s + 1) σ' ∧
        ((σ'.vars "cnt" = σ.vars "cnt" ∧ K ≤ 30) ∨
          (σ'.vars "cnt" = σ.vars "cnt" + 1 ∧ σ.vars "cnt" < t ∧ K ≤ pickBlockK bw nb)) := by
    intro K₁ hrun hK hg
    refine ⟨τ₀.setVar "sj" (σ.vars "sj" + 1), 3 + (K₁ + 4),
      run₀.seq (hrun.seq (hbump τ₀ hsj₀)),
      hA₀.setVar (by decide) (by decide), by simp, ?_, Or.inl ⟨by simp [hcnt₀], by omega⟩⟩
    exact (progressA_succ_of_not hg hP₀).of_eq (by simp) rfl
  by_cases hlt : σ.vars "cnt" < t
  · -- there is still room, so the exclusion test is asked
    have hc₀ : (Cond.lt (Expr.var "cnt") (.lit t)).evalB B τ₀ = some true := by
      rw [evalB_condLt (evalB_var (by rw [hcnt₀]; omega)) (evalB_lit htB)]
      simp [hcnt₀, hlt]
    obtain ⟨-, hcnteq, E, hexc, hE1, hEiff⟩ :
        τ₀.vars "cnt" < t ∧ τ₀.vars "cnt" = (selBelow G M r X s).ncard ∧
          ∃ E, τ₀.arrs "exc" = arrOf n E ∧ (∀ w, MemOf X w → E w ≤ 1) ∧
            ∀ w, MemOf X w → (E w = 0 ↔ ∀ u < s, GSel G M r X u → ¬ WD G M r u w) := by
      rcases hP₀ with ⟨h, -⟩ | h
      · omega
      · exact h
    have hmemS : MemOf X s := hml.sound _ hsj
    have hE1s : E s ≤ 1 := hE1 _ hmemS
    have hexcv : (Expr.get "exc" (.var "mv")).evalB B τ₀ = some (E s) :=
      evalB_get (evalB_var (by rw [hmv₀]; omega))
        (by rw [hexc, hmv₀, getElem?_arrOf E hsn]) (by omega)
    by_cases hE0 : E s = 0
    · -- **the member is selected**
      have hgsel : GSel G M r X s :=
        (gsel_iff hsn).2 ⟨hmemS.2, (hEiff _ hmemS).1 hE0⟩
      have hc₁ : (Cond.eq (.get "exc" (.var "mv")) (.lit 0)).evalB B τ₀ = some true := by
        rw [evalB_condEq hexcv (evalB_lit (by omega))]; simp [hE0]
      -- count it
      obtain ⟨τ₁, hτ₁⟩ : ∃ τ, τ = τ₀.setVar "cnt" (σ.vars "cnt" + 1) := ⟨_, rfl⟩
      have run₁ : Run B (.assign "cnt" (.add (.var "cnt") (.lit 1))) τ₀ τ₁ 4 := by
        rw [hτ₁, ← hcnt₀]
        exact (Run.assign (v := τ₀.vars "cnt" + 1)
          (evalB_bin (evalB_var (by rw [hcnt₀]; omega)) (evalB_lit (by omega))
            (by simp; omega))).mono (by simp [Expr.size])
      have hv₁ : ∀ y, y ≠ "cnt" → τ₁.vars y = τ₀.vars y := by
        intro y hy; rw [hτ₁]; simp [hy]
      have ha₁ : τ₁.arrs = τ₀.arrs := by rw [hτ₁]; simp
      have hcnt₁ : τ₁.vars "cnt" = σ.vars "cnt" + 1 := by rw [hτ₁]; simp
      -- name the source
      obtain ⟨τ₂, hτ₂⟩ : ∃ τ, τ = τ₁.setVar "src" s := ⟨_, rfl⟩
      have run₂ : Run B (.assign "src" (.var "mv")) τ₁ τ₂ 2 := by
        rw [hτ₂]
        refine (Run.assign (v := s) ?_).mono (by simp [Expr.size])
        rw [← hmv₀, ← hv₁ "mv" (by decide)]
        exact evalB_var (by rw [hv₁ "mv" (by decide), hmv₀]; omega)
      have hv₂ : ∀ y, y ≠ "src" → τ₂.vars y = τ₁.vars y := by
        intro y hy; rw [hτ₂]; simp [hy]
      have ha₂ : τ₂.arrs = τ₁.arrs := by rw [hτ₂]; simp
      have hsrc₂ : τ₂.vars "src" = s := by rw [hτ₂]; simp
      -- the ball this pick is charged to
      obtain ⟨Aset, hAset, hbwA, hnbA⟩ := hbud s hsn
      -- search from it
      obtain ⟨g₆, hq₂⟩ := hqex
      obtain ⟨g₇, hqd₂⟩ := hqdex
      obtain ⟨τ₃, run₃, hdist₃, Q, QD, hq₃, hqd₃, htln, htlnb, hqn, hseg, hqinj, -⟩ :=
        (bfsBlockA_specW (G := G) (M := M) (O := O) (T := T) (ns := ns) (nt := nt)
          (d := r) (s := s) hcsr hsn hnB hnsB hnt hrB hMB hAset hbwA hnbA).run (σ := τ₂)
          ⟨by rw [hv₂ "n" (by decide), hv₁ "n" (by decide), hv₀ "n" (by decide), hn],
            hsrc₂,
            by rw [ha₂, ha₁, ha₀]; exact hoff, by rw [ha₂, ha₁, ha₀]; exact htgt,
            by rw [ha₂, ha₁, ha₀]; exact halv, by rw [ha₂, ha₁, ha₀]; exact hdist,
            ⟨g₆, by rw [ha₂, ha₁, ha₀]; exact hq₂⟩, ⟨g₇, by rw [ha₂, ha₁, ha₀]; exact hqd₂⟩⟩
      -- and mark its ball
      have hn₃ : τ₃.vars "n" = n := by
        rw [run₃.frame_var "n" (notMem_bfsBlock_wvars r "n" (by simp)),
          hv₂ "n" (by decide), hv₁ "n" (by decide), hv₀ "n" (by decide), hn]
      have hsrc₃ : τ₃.vars "src" = s := by
        rw [run₃.frame_var "src" (notMem_bfsBlock_wvars r "src" (by simp)), hsrc₂]
      have hexc₃ : τ₃.arrs "exc" = arrOf n E := by
        rw [run₃.frame_arr "exc" (notMem_bfsBlock_warrs r "exc" (by simp)),
          ha₂, ha₁]; exact hexc
      obtain ⟨τ₄, K₄, run₄, hK₄, hq₄, E', hexc₄, hmark, hkeep⟩ :=
        markBall_run (n := n) (B := B) (tf := τ₃.vars "tail") (s := s) (Q := Q) (E := E)
          hnB hsn htln (fun i hi => lt_trans (hqn i hi) hnB) hn₃ hsrc₃ rfl hq₃ hexc₃
      -- what the two phases left
      have hsj₄ : τ₄.vars "sj" = σ.vars "sj" := by
        rw [run₄.frame_var "sj" (notMem_markBall_wvars "sj" (by simp)),
          run₃.frame_var "sj" (notMem_bfsBlock_wvars r "sj" (by simp)),
          hv₂ "sj" (by decide), hv₁ "sj" (by decide), hsj₀]
      have hcnt₄ : τ₄.vars "cnt" = σ.vars "cnt" + 1 := by
        rw [run₄.frame_var "cnt" (notMem_markBall_wvars "cnt" (by simp)),
          run₃.frame_var "cnt" (notMem_bfsBlock_wvars r "cnt" (by simp)),
          hv₂ "cnt" (by decide), hcnt₁]
      have harr₄ : ∀ a, a ∈ ["off", "tgt", "alv", "mem"] → τ₄.arrs a = σ.arrs a := by
        intro a ha
        rw [run₄.frame_arr a (notMem_markBall_warrs a (by fin_cases ha <;> simp)),
          run₃.frame_arr a (notMem_bfsBlock_warrs r a (by fin_cases ha <;> simp)),
          ha₂, ha₁, ha₀]
      have hdist₄ : τ₄.arrs "dist" = arrOf n (fun _ => r + 1) := by
        rw [run₄.frame_arr "dist" (notMem_markBall_warrs "dist" (by simp))]; exact hdist₃
      have hqd₄ : τ₄.arrs "qd" = arrOf n QD := by
        rw [run₄.frame_arr "qd" (notMem_markBall_warrs "qd" (by simp))]; exact hqd₃
      have hA₄ : ArenaA n nt mm r O T M Mem τ₄ := by
        refine ⟨?_, ?_, by rw [harr₄ "off" (by simp)]; exact hoff,
          by rw [harr₄ "tgt" (by simp)]; exact htgt,
          by rw [harr₄ "alv" (by simp)]; exact halv,
          by rw [harr₄ "mem" (by simp)]; exact hmem, hdist₄, ⟨Q, hq₄⟩, ⟨QD, hqd₄⟩⟩
        · rw [run₄.frame_var "n" (notMem_markBall_wvars "n" (by simp)), hn₃]
        · rw [run₄.frame_var "mm" (notMem_markBall_wvars "mm" (by simp)),
            run₃.frame_var "mm" (notMem_bfsBlock_wvars r "mm" (by simp)),
            hv₂ "mm" (by decide), hv₁ "mm" (by decide), hv₀ "mm" (by decide), hmmv]
      -- **the mathematics of the turn**: the marked set is the ball
      have hE'iff : ∀ w, MemOf X w → (E' w = 0 ↔
          ∀ u < s + 1, GSel G M r X u → ¬ WD G M r u w) := by
        intro w hw
        have hwn : w < n := hw.lt
        have hmk := marked_iff_wd (G := G) (M := M) (r := r) hsn hwn hseg (w := w)
        constructor
        · intro h0 u hu hgu
          have hnotmark : ¬ ((∃ i, i < τ₃.vars "tail" ∧ Q i = w) ∨ w = s) := by
            intro hcon
            rw [hmark w hwn hcon] at h0; omega
          have hEw : E w = 0 := by rw [← hkeep w hwn hnotmark]; exact h0
          rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu' | rfl
          · exact (hEiff w hw).1 hEw u hu' hgu
          · exact fun hwd => hnotmark (hmk.2 hwd)
        · intro hall
          have hnotwd : ¬ WD G M r s w := fun hwd => hall s (by omega) hgsel hwd
          have hnotmark : ¬ ((∃ i, i < τ₃.vars "tail" ∧ Q i = w) ∨ w = s) :=
            fun hcon => hnotwd (hmk.1 hcon)
          rw [hkeep w hwn hnotmark]
          exact (hEiff w hw).2 (fun u hu hgu => hall u (by omega) hgu)
      have hE'1 : ∀ w, MemOf X w → E' w ≤ 1 := by
        intro w hw
        have hwn : w < n := hw.lt
        by_cases hcon : ((∃ i, i < τ₃.vars "tail" ∧ Q i = w) ∨ w = s)
        · rw [hmark w hwn hcon]
        · rw [hkeep w hwn hcon]; exact hE1 w hw
      have hncard : σ.vars "cnt" + 1 = (selBelow G M r X (s + 1)).ncard := by
        rw [ncard_selBelow_succ_of_gsel hsn hgsel, ← hcnteq, hcnt₀]
      have hlei : σ.vars "cnt" + 1 ≤ (greedySet (masked G M) r X).ncard := by
        rw [hncard]; exact ncard_selBelow_le
      refine ⟨τ₄.setVar "sj" (σ.vars "sj" + 1), _,
        run₀.seq ((Run.ite_true hc₀ (Run.ite_true hc₁
          (run₁.seq (run₂.seq (run₃.seq run₄))))).seq (hbump τ₄ hsj₄)),
        hA₄.setVar (by decide) (by decide), by simp, ?_,
        Or.inr ⟨by simp [hcnt₄], hlt, ?_⟩⟩
      · rcases Nat.lt_or_ge (σ.vars "cnt" + 1) t with hlt' | hge'
        · exact Or.inr ⟨by simp [hcnt₄]; omega, by simp [hcnt₄, ← hncard],
            E', by simp [hexc₄], hE'1, hE'iff⟩
        · exact Or.inl ⟨by simp [hcnt₄]; omega, by omega⟩
      · have hKb : K₄ ≤ markBallK nb :=
          le_trans hK₄ (by simp only [markBallK]; omega)
        simp only [pickBlockK, Cond.size, Expr.size]
        omega
    · -- an earlier pick already excluded it
      have hc₁ : (Cond.eq (.get "exc" (.var "mv")) (.lit 0)).evalB B τ₀ = some false := by
        rw [evalB_condEq hexcv (evalB_lit (by omega))]; simp [hE0]
      refine hnopick _ (Run.ite_true hc₀ (Run.ite_false hc₁ Run.skip)) (by simp [Cond.size,
        Expr.size]) fun hg => hE0 ((hEiff _ hmemS).2 ((gsel_iff hsn).1 hg).2)
  · -- the count has reached the threshold
    have hc₀ : (Cond.lt (Expr.var "cnt") (.lit t)).evalB B τ₀ = some false := by
      rw [evalB_condLt (evalB_var (by rw [hcnt₀]; omega)) (evalB_lit htB)]
      simp [hcnt₀, hlt]
    have hB : τ₀.vars "cnt" = t ∧ t ≤ (greedySet (masked G M) r X).ncard := by
      rcases hP₀ with h | ⟨h, -⟩
      · exact h
      · omega
    refine ⟨τ₀.setVar "sj" (σ.vars "sj" + 1), _,
      run₀.seq ((Run.ite_false hc₀ Run.skip).seq (hbump τ₀ hsj₀)),
      hA₀.setVar (by decide) (by decide), by simp, ?_,
      Or.inl ⟨by simp [hcnt₀], by simp [Cond.size, Expr.size]⟩⟩
    exact Or.inl ⟨by simp [hB.1], hB.2⟩

/-! ### §5 The scan

The loop rule is the kit's `Spec.while_potential`: a turn that picks
draws on the first term of the potential and a turn that does not draws
on the second, so the whole scan costs one ball per pick and a constant
per **member**. -/

/-- The invariant of the active scan. The position the invariant is read
at is `memPos`, a *carrier* position, while the counter counts members —
that mismatch is the whole design, and `progressA_step_gap` is what
bridges it. -/
def ScatBlockInv (n nt mm r t : ℕ) (G : SimpleGraph (Fin n)) (M O T Mem : ℕ → ℕ)
    (X : Set (Fin n)) (σ : Env) : Prop :=
  ArenaA n nt mm r O T M Mem σ ∧ σ.vars "sj" ≤ mm ∧
    ProgressA G M r t X (memPos n mm Mem (σ.vars "sj")) σ

/-- The potential: one ball's worth per pick still allowed, and a
constant per member not yet reached. **No carrier term.** -/
def ScatBlockPot (mm bw nb t : ℕ) (σ : Env) : ℕ :=
  pickBlockK bw nb * (t - σ.vars "cnt") + 40 * (mm - σ.vars "sj")

theorem loop_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B)
    (hml : MemList n mm Mem X) {bw nb : ℕ} (hbud : BallBudget n r G M O bw nb) :
    Spec B (fun σ => ScatBlockInv n nt mm r t G M O T Mem X (σ.setVar "sj" 0))
      (scatBlockLoop r t)
      (fun _ σ' => ArenaA n nt mm r O T M Mem σ' ∧ ProgressA G M r t X n σ' ∧
        σ'.vars "sj" = mm)
      (pickBlockK bw nb * t + 40 * mm + 6) := by
  have hmmn : mm ≤ n := hml.card_le
  have hwhile : Spec B (ScatBlockInv n nt mm r t G M O T Mem X)
      (.while (.lt (.var "sj") (.var "mm")) (scatBlockStep r t))
      (fun _ σ' => ScatBlockInv n nt mm r t G M O T Mem X σ' ∧
        (Cond.lt (Expr.var "sj") (.var "mm")).evalB B σ' = some false)
      (pickBlockK bw nb * t + 40 * mm + 4) := by
    refine Spec.while_potential _ (ScatBlockPot mm bw nb t) (fun τ hτ => ?_)
      (fun τ hτ hb => ?_) (fun _ h => h) (fun τ hτ => ?_)
    · exact evalB_condLt_vars (by have := hτ.2.1; omega)
        (by rw [hτ.1.2.1]; omega)
    · have hlt : τ.vars "sj" < mm := by
        have := lt_of_condLt_true hb; rw [hτ.1.2.1] at this; exact this
      have hPm : ProgressA G M r t X (Mem (τ.vars "sj")) τ := by
        have := hτ.2.2; rwa [memPos_of_lt hlt] at this
      obtain ⟨τ', K, hrun, hA', hsj', hP', hcase⟩ :=
        step_run hcsr hnB hnsB hnt hrB htB hMB hml hbud hτ.1 hlt hPm
      refine ⟨τ', K, hrun, ⟨hA', by omega, ?_⟩, ?_⟩
      · rw [hsj']; exact progressA_step_gap hml hlt hP'
      · have hn1 : mm - τ.vars "sj" = (mm - (τ.vars "sj" + 1)) + 1 := by omega
        simp only [ScatBlockPot, hsj', hn1]
        rcases hcase with ⟨hc, hK⟩ | ⟨hc, hct, hK⟩
        · rw [hc]; simp only [Cond.size, Expr.size]; omega
        · have hn2 : t - τ.vars "cnt" = (t - (τ.vars "cnt" + 1)) + 1 := by omega
          rw [hc, hn2, Nat.mul_succ]
          simp only [Cond.size, Expr.size]
          omega
    · have h₁ : pickBlockK bw nb * (t - τ.vars "cnt") ≤ pickBlockK bw nb * t :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have h₂ : 40 * (mm - τ.vars "sj") ≤ 40 * mm := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      simp only [ScatBlockPot, Cond.size, Expr.size]
      omega
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨σ', hrun, hI', hfalse⟩ := hwhile.run (σ := σ.setVar "sj" 0) hσ
  have hsjmm : σ'.vars "sj" = mm := by
    have h₀ := le_of_condLt_false hfalse
    have h₁ := hI'.1.2.1
    have h₂ := hI'.2.1
    omega
  refine ⟨σ', _, Run.seq (Run.assign (v := 0) (evalB_lit (by omega))) hrun,
    by simp [Expr.size]; omega, hI'.1, ?_, hsjmm⟩
  have := hI'.2.2
  rwa [hsjmm, memPos_end hml] at this

/-! ### §6 The pass

Clear, scan, report. The reporting limb is the landed one and the answer
it reports is the landed answer. -/

/-- **The active-set greedy scatter pass.** Handed a block structure for
`G`, a mask, the member list of `X`, a clean distance array, a radius
and a threshold, `scatBlockCom r t` leaves in `flag` the truth value of
the scatter sentence: `1` exactly when the greedy `r`-scattered subset
of `X` in the masked arena has at least `t` elements.

The postcondition is `RamScatter.scatter_specW`'s, verbatim. The charge
is `scatBlockK mm bw nb t`, in which **neither `n` nor `ns` occurs**. -/
theorem scatBlock_specW {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B)
    (hml : MemList n mm Mem X) {bw nb : ℕ} (hbud : BallBudget n r G M O bw nb) :
    Spec B
      (fun σ => ArenaA n nt mm r O T M Mem σ ∧ (∃ g, σ.arrs "exc" = arrOf n g))
      (scatBlockCom r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1)
      (scatBlockK mm bw nb t) := by
  have hmmn : mm ≤ n := hml.card_le
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hA, g, hexc⟩ := hσ
  obtain ⟨hn, hmmv, hoff, htgt, halv, hmem, hdist, hqex, hqdex⟩ := id hA
  -- the counter
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ, τ = σ.setVar "cnt" 0 := ⟨_, rfl⟩
  have run₁ : Run B (.assign "cnt" (.lit 0)) σ τ₁ 2 := by
    rw [hτ₁]; exact (Run.assign (v := 0) (evalB_lit (by omega))).mono (by simp [Expr.size])
  have hv₁ : ∀ y, y ≠ "cnt" → τ₁.vars y = σ.vars y := by
    intro y hy; rw [hτ₁]; simp [hy]
  have ha₁ : τ₁.arrs = σ.arrs := by rw [hτ₁]; simp
  have hcnt₁ : τ₁.vars "cnt" = 0 := by rw [hτ₁]; simp
  have hA₁ : ArenaA n nt mm r O T M Mem τ₁ := by
    rw [hτ₁]; exact hA.setVar (by decide) (by decide)
  -- the exclusion bits, at the members
  obtain ⟨τ₂, K₂, run₂, hK₂, hmem₂, E, hexc₂, hclear, -⟩ :=
    clearMem_run (n := n) (mm := mm) (B := B) (Mem := Mem) (X := X)
      hnB (by omega) hml (by rw [hv₁ "n" (by decide)]; exact hn)
      (by rw [hv₁ "mm" (by decide)]; exact hmmv)
      (by rw [ha₁]; exact hmem) (by rw [ha₁]; exact hexc)
  have hcnt₂ : τ₂.vars "cnt" = 0 := by
    rw [run₂.frame_var "cnt" (notMem_clearMem_wvars "cnt" (by simp)), hcnt₁]
  have harr₂ : ∀ a, a ∈ ["off", "tgt", "alv", "dist", "q", "qd"] → τ₂.arrs a = σ.arrs a := by
    intro a ha
    rw [run₂.frame_arr a (notMem_clearMem_warrs a (by fin_cases ha <;> simp)), ha₁]
  have hA₂ : ArenaA n nt mm r O T M Mem τ₂ := by
    obtain ⟨g₆, hq⟩ := hqex
    obtain ⟨g₇, hqd⟩ := hqdex
    refine ⟨?_, ?_, by rw [harr₂ "off" (by simp)]; exact hoff,
      by rw [harr₂ "tgt" (by simp)]; exact htgt,
      by rw [harr₂ "alv" (by simp)]; exact halv, hmem₂,
      by rw [harr₂ "dist" (by simp)]; exact hdist,
      ⟨g₆, by rw [harr₂ "q" (by simp)]; exact hq⟩,
      ⟨g₇, by rw [harr₂ "qd" (by simp)]; exact hqd⟩⟩
    · rw [run₂.frame_var "n" (notMem_clearMem_wvars "n" (by simp)),
        hv₁ "n" (by decide), hn]
    · rw [run₂.frame_var "mm" (notMem_clearMem_wvars "mm" (by simp)),
        hv₁ "mm" (by decide), hmmv]
  -- the scan starts with nothing selected and nothing excluded
  have hI₂ : ScatBlockInv n nt mm r t G M O T Mem X (τ₂.setVar "sj" 0) := by
    refine ⟨hA₂.setVar (by decide) (by decide), by simp, ?_⟩
    refine progressA_start hml ?_
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact Or.inl ⟨by simp [hcnt₂], by omega⟩
    · refine Or.inr ⟨by simp [hcnt₂]; omega, by simp [hcnt₂, selBelow_zero], E,
        by simp [hexc₂], fun w hw => by rw [hclear w hw]; omega,
        fun w hw => by rw [hclear w hw]; simp⟩
  obtain ⟨τ₃, run₃, hA₃, hP₃, hsj₃⟩ :=
    (loop_spec hcsr hnB hnsB hnt hrB htB hMB hml hbud).run (σ := τ₂) hI₂
  -- the answer
  have hcntt : τ₃.vars "cnt" ≤ t := hP₃.cnt_le
  have hcntB : τ₃.vars "cnt" < B := by omega
  have hcv : (Cond.lt (Expr.var "cnt") (.lit t)).evalB B τ₃
      = some (decide (τ₃.vars "cnt" < t)) := evalB_condLt (evalB_var hcntB) (evalB_lit htB)
  by_cases hlt : τ₃.vars "cnt" < t
  · have hns : ¬ t ≤ (greedySet (masked G M) r X).ncard := by
      rcases hP₃ with ⟨h, -⟩ | ⟨-, h, -⟩
      · omega
      · rw [selBelow_all] at h; omega
    refine ⟨τ₃.setVar "flag" 0, _,
      run₁.seq (run₂.seq (run₃.seq (Run.ite_true (by rw [hcv]; simp [hlt])
        (Run.assign (v := 0) (evalB_lit (by omega)))))),
      ?_, by simp [hns], by simp⟩
    simp only [scatBlockK, clearMemK, scanMemK, Cond.size, Expr.size]
    have : K₂ ≤ clearMemK mm := hK₂
    simp only [clearMemK] at this
    omega
  · have hyes : t ≤ (greedySet (masked G M) r X).ncard := by
      rcases hP₃ with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    refine ⟨τ₃.setVar "flag" 1, _,
      run₁.seq (run₂.seq (run₃.seq (Run.ite_false (by rw [hcv]; simp [hlt])
        (Run.assign (v := 1) (evalB_lit (by omega)))))),
      ?_, by simp [hyes], by simp⟩
    simp only [scatBlockK, clearMemK, scanMemK, Cond.size, Expr.size]
    have : K₂ ≤ clearMemK mm := hK₂
    simp only [clearMemK] at this
    omega

/-- **The active-set pass at the pinned target array** — the frozen
export, which is the widened walk at `nt = ns`. Nothing is re-walked. -/
theorem scatBlock_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B)
    (hml : MemList n mm Mem X) {bw nb : ℕ} (hbud : BallBudget n r G M O bw nb) :
    Spec B
      (fun σ => ArenaA n ns mm r O T M Mem σ ∧ (∃ g, σ.arrs "exc" = arrOf n g))
      (scatBlockCom r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1)
      (scatBlockK mm bw nb t) :=
  scatBlock_specW hcsr hnB hnsB le_rfl hrB htB hMB hml hbud

#print axioms scatBlock_spec
#print axioms scatBlock_specW

end Lax3Proofs.Refine.ScatterBlock
