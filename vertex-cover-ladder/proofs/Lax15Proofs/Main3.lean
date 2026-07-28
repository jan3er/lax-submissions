import Lax15Proofs.Loop3
import Lax15Proofs.Main
import Lax15.VertexCoverBranch

/-!
The second rung's loop, assembly, and theorem.

The three pieces are the first rung's, with one clause added to each.
The outer loop is one application of the loop rule: the invariant is
"some configuration is represented, carries the side invariant and
satisfies `J3`, and the tapes are untouched", the potential is `pot3`
read back off the two stack arrays, and `Loop3.lean`'s body pays for a
turn out of it. The assembly is the read phase — rung A's, unchanged,
since the two drivers read the same word — followed by the loop and one
`write`; what is new is that the read phase must hand the loop the side
invariant as well, which is where the array extents `vis ↦ n` and
`q ↦ n` are chosen. And the theorem is the concept's, cashed in through
the transfer theorem.

The potential the loop rule sees is a function of the environment, and
it may not consult the pure configuration. `framesOf` — rung A's, reused
verbatim, since the stack arrays and their meaning did not change —
reads the stored budget–phase pairs off `stkB` and `stkP` below `top`,
totally, and `potN3` is a function of those pairs alone, so the crossing
is rung A's `framesOf_eq` and nothing more.

The ten arrays of the layout cost the machine `49` steps per unit of
IMP+ cost, and the run itself costs at most `6500 · branchCount k` per
entry of the input word. The product `318500` is the constant of the
statement, and no part of it was fought over: `1610` for a turn of the
outer loop and `4` for its test make `1614`, times the four units of
`pot3` that the initial budget is worth, is `6456`, and the rest is
slack for the read phase.
-/

namespace Lax15Proofs.VC3

open Lax13.Ram Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax11Proofs.CC
open Lax15Proofs.VC

variable {g : List ℕ} {n m k B : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}

/-! ### The potential, read off the arrays

The loop rule's potential is a function of the environment alone. The
reading of the stack is rung A's `framesOf`; only what is summed over it
changes. -/

/-- On a represented state the numeric potential is the pure one. -/
theorem potN3_eq {C : Config n} {τ : Env} (hRep : Rep n m O T C τ)
    (hlen : C.frames.length ≤ n) :
    potN3 (τ.vars "mode") (τ.vars "bud") (framesOf τ) = pot3 C := by
  rw [hRep.mode, hRep.bud, framesOf_eq hRep hlen, ← pot3_eq_potN3]

/-! ### The loop

One application of `Run.while_potential`. A turn pays `1 + 3` for the test and
at most `1610 · (n + 2m + 1)` for the body, and buys one unit of `pot3`,
so the scale `1614 · (n + 2m + 1)` covers it. The whole search is
therefore paid for by the potential of the configuration it starts
from — and that potential is where, and only where, `branchCount k`
enters. -/

/-- **The search loop.** From a represented state satisfying the
invariant and the side invariant, the outer loop reaches a represented,
invariant state in mode `2`, in at most
`1614 · (n + 2m + 1) · pot3 C₀ + 4` steps. -/
theorem searchLoop3_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ p < 2 * m, T p = target g p)
    (h2B : 2 < B) (hnB : n + 2 < B) (hmB : 2 * m < B) (hkB : k + 1 < B)
    {C₀ : Config n} {σ : Env} (hRep : Rep n m O T C₀ σ) (hside : SideInv n σ)
    (hJ : J3 G k C₀) :
    ∃ (C' : Config n) (τ' : Env) (K : ℕ),
      Run B (.while (.lt (.var "mode") (.lit 2)) outerBody3) σ τ' K ∧
      Rep n m O T C' τ' ∧ J3 G k C' ∧ C'.mode = 2 ∧
      τ'.inp = σ.inp ∧ τ'.out = σ.out ∧
      K ≤ 1614 * (n + 2 * m + 1) * pot3 C₀ + 4 := by
  -- the test always evaluates: the mode is at most `2`, and `2` is a word
  have hdef : ∀ τ : Env,
      (∃ C, Rep n m O T C τ ∧ SideInv n τ ∧ J3 G k C ∧ τ.inp = σ.inp ∧ τ.out = σ.out) →
      ∃ v, (Cond.lt (.var "mode") (.lit 2)).evalB B τ = some v := by
    rintro τ ⟨C, hRepC, -, hJC, -, -⟩
    have hmd : τ.vars "mode" = C.mode := hRepC.mode
    have := hJC.j.1
    exact evalB_condLt_var_lit (by omega) (by omega)
  -- a turn: the body runs, both invariants survive, the potential pays
  have hstep : ∀ τ : Env,
      (∃ C, Rep n m O T C τ ∧ SideInv n τ ∧ J3 G k C ∧ τ.inp = σ.inp ∧ τ.out = σ.out) →
      (Cond.lt (.var "mode") (.lit 2)).evalB B τ = some true →
      ∃ τ'' K, Run B outerBody3 τ τ'' K ∧
        (∃ C, Rep n m O T C τ'' ∧ SideInv n τ'' ∧ J3 G k C ∧
          τ''.inp = σ.inp ∧ τ''.out = σ.out) ∧
        1 + (Cond.lt (Expr.var "mode") (Expr.lit 2)).size + K +
            1614 * (n + 2 * m + 1) *
              potN3 (τ''.vars "mode") (τ''.vars "bud") (framesOf τ'') ≤
          1614 * (n + 2 * m + 1) *
            potN3 (τ.vars "mode") (τ.vars "bud") (framesOf τ) := by
    rintro τ ⟨C, hRepC, hsideC, hJC, hinp, hout⟩ hc
    have hc' := Cond.eval_of_evalB hc
    have hmd : τ.vars "mode" = C.mode := hRepC.mode
    have hmode : C.mode < 2 := by
      simp only [Cond.eval, Expr.eval, Option.bind_some, Option.map_some,
        Option.some.injEq, decide_eq_true_eq, hmd] at hc'
      exact hc'
    obtain ⟨C', τ'', K, hrunb, hRep', hside', hJ', hpot, hi, ho, hK⟩ :=
      outerBody3_run hg hm hO hT h2B hnB hmB hkB hRepC hsideC hJC hmode
    refine ⟨τ'', K, hrunb, ⟨C', hRep', hside', hJ', by rw [hi, hinp], by rw [ho, hout]⟩, ?_⟩
    have e1 := potN3_eq hRep' hJ'.j.frames_length_le
    have e2 := potN3_eq hRepC hJC.j.frames_length_le
    have hmul : 1614 * (n + 2 * m + 1) * (pot3 C' + 1) ≤
        1614 * (n + 2 * m + 1) * pot3 C := Nat.mul_le_mul_left _ hpot
    rw [Nat.mul_succ] at hmul
    rw [e1, e2]
    simp only [size_condLt, size_var, size_lit]
    omega
  obtain ⟨τ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := Cond.lt (.var "mode") (.lit 2)) (c := outerBody3)
      (fun τ => ∃ C, Rep n m O T C τ ∧ SideInv n τ ∧ J3 G k C ∧
        τ.inp = σ.inp ∧ τ.out = σ.out)
      (fun τ => 1614 * (n + 2 * m + 1) *
        potN3 (τ.vars "mode") (τ.vars "bud") (framesOf τ))
      hdef hstep ⟨C₀, hRep, hside, hJ, rfl, rfl⟩
  -- exit: the test is false and `J` caps the mode, so the mode is `2`
  obtain ⟨C', hRep', -, hJ', hinp', hout'⟩ := hI'
  have hfalse' := Cond.eval_of_evalB hfalse
  have hmd' : τ'.vars "mode" = C'.mode := hRep'.mode
  have hmode' : C'.mode = 2 := by
    simp only [Cond.eval, Expr.eval, Option.bind_some, Option.map_some,
      Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt, hmd'] at hfalse'
    have := hJ'.j.1
    omega
  have hΦ₀ := potN3_eq hRep hJ.j.frames_length_le
  refine ⟨C', τ', K, hrun, hRep', hJ', hmode', hinp', hout', ?_⟩
  simp only [size_condLt, size_var, size_lit, hΦ₀] at hpay
  omega

end Lax15Proofs.VC3

namespace Lax15Proofs.VC3Main

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding Lax11.VertexCover
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax13Proofs.Transfer
open Lax11Proofs Lax15Proofs.VC Lax15Proofs.VC3 Lax15Proofs.VCMain

/-- The array extents the second driver runs with: the two arrays of the
encoding at the lengths the header gives them, the mark array and the
solver's two one per vertex, and the trail and the four stacks one
longer — frame health makes both heights at most `n`, and a push writes
at the height it finds. -/
def vcf3Ext (n m : ℕ) (a : String) : ℕ :=
  if a = "tgt" then 2 * m
  else if a = "mark" then n
  else if a = "vis" then n
  else if a = "q" then n
  else n + 1

/-- The machine pays forty-nine steps per unit of IMP+ cost: ten arrays
make one index computation twelve instructions long. -/
theorem const3_eq : vcf3Layout.const = 49 := by
  simp [Layout.const, Layout.idxLen, vcf3Layout]

/-- The proofs-side leaf count and the concept's are the same function:
the two definitions were written with the same four equations. -/
theorem branchCount_eq (b : ℕ) :
    branchCount b = Lax15.VertexCoverBranch.branchCount b := by
  induction b using branchCount.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 => rfl
  | case4 b ih1 ih2 =>
    rw [branchCount_add_three, ih1, ih2]
    rfl

/-- The whole run of the second driver on an encoded instance: the
answer comes out, the cost is `branchCount k` times linear in the length
of the word, and every value the run produces stays below any bound the
length of the word and the parameter together stay below. Every phase
was bounded loosely, and this is the sum of those bounds. -/
theorem vcf3Com_run {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k m B : ℕ}
    (hx : EncodesParamInstance x n G k) (hm : edgeCount x = m) (hB : x.length + k ≤ B) :
    ∃ (σ' : Env) (K : ℕ), Run B vcf3Com (initEnv (vcf3Ext n m) x) σ' K ∧
      σ'.out = [if G.vertexCoverNum ≤ (k : ℕ∞) then 1 else 0] ∧
      K ≤ 6500 * branchCount k * (x.length + 1) := by
  obtain ⟨g, rfl, hg⟩ := hx
  -- the graph block's own edge count: the appended parameter sits past index one
  have hglen := hg.length_eq
  have hmg : edgeCount g = m := by
    rw [← hm]
    simp only [edgeCount, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show 1 < g.length by omega)]
  rw [hmg] at hglen
  -- the word: the two header entries, then the offsets, the targets and the parameter
  obtain ⟨rest, hxr⟩ : ∃ rest, g = n :: m :: rest := by
    rcases g with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hglen; omega
    · simp at hglen; omega
    · have ha : a = n := by simpa [vertexCount] using hg.vertexCount_eq
      have hb : b = m := by simpa [edgeCount] using hmg
      exact ⟨rest, by rw [ha, hb]⟩
  subst hxr
  have hrest : rest.length = 1 + n + 2 * m := by simp at hglen; omega
  -- everything the run holds is an entry of the word, a count of them, or below one
  have hB' : 4 + n + 2 * m + k ≤ B := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hB
    omega
  have h2B : 2 < B := by omega
  have hmB : 2 * m < B := by omega
  have hn1B : n + 1 < B := by omega
  have hn2B : n + 2 < B := by omega
  have hk1B : k + 1 < B := by omega
  have hrestB : ∀ v ∈ rest, v < B := fun v hv =>
    lt_of_lt_of_le (CC.mem_lt_length hg (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)))
      (by simp only [List.length_cons]; omega)
  set ys := rest.take (n + 1) with hys_def
  set zs := rest.drop (n + 1) with hzs_def
  have hys : ys.length = n + 1 := by rw [hys_def, List.length_take]; omega
  have hzs : zs.length = 2 * m := by rw [hzs_def, List.length_drop]; omega
  have hsplit : rest = ys ++ zs := (List.take_append_drop _ _).symm
  have hysB : ∀ v ∈ ys, v < B :=
    fun v hv => hrestB v (by rw [hys_def] at hv; exact List.mem_of_mem_take hv)
  have hzsB : ∀ v ∈ zs, v < B :=
    fun v hv => hrestB v (by rw [hzs_def] at hv; exact List.mem_of_mem_drop hv)
  -- what the two arrays hold once they are read in
  have hyd : ∀ i < n + 1, ys.getD i 0 = offset (n :: m :: rest) i := by
    intro i hi
    rw [hys_def, CC.getD_take hi, offset, CC.getD_cons_cons]
  have hzd : ∀ p < 2 * m, zs.getD p 0 = target (n :: m :: rest) p := by
    intro p _
    rw [hzs_def, CC.getD_drop, target, hg.vertexCount_eq]
    have h : 3 + n + p = 2 + (n + 1 + p) := by omega
    rw [h, CC.getD_cons_cons]
  -- the reads
  have e₁ : (initEnv (vcf3Ext n m) (n :: m :: rest ++ [k])).inp
      = n :: (m :: (rest ++ [k])) := rfl
  set σ₁ : Env := { (initEnv (vcf3Ext n m) (n :: m :: rest ++ [k])).setVar "n" n with
    inp := m :: (rest ++ [k]) } with hσ₁
  set σ₂ : Env := { σ₁.setVar "m" m with inp := rest ++ [k] } with hσ₂
  set σ₃ : Env := σ₂.setVar "len" (n + 1) with hσ₃
  have r₁ : Run B (.read "n") (initEnv (vcf3Ext n m) (n :: m :: rest ++ [k])) σ₁ 1 :=
    Run.read e₁
  have r₂ : Run B (.read "m") σ₁ σ₂ 1 := Run.read rfl
  have r₃ : Run B (.assign "len" (.add (.var "n") (.lit 1))) σ₂ σ₃ 4 :=
    (Run.assign (v := n + 1) (by simp [hσ₂, hσ₁, initEnv]; omega)).mono (by simp)
  -- the offsets
  obtain ⟨σ₄, O, r₄, hoff₄, hO₄, hinp₄⟩ :=
    CC.readLoop_run (B := B) (a := "off") (lim := "len") (by decide) (by decide) (σ := σ₃)
      (g := fun _ => 0) (k := n + 1) (ys := ys) (rest := zs ++ [k])
      (by simp [hσ₃, hσ₂, hσ₁, initEnv, vcf3Ext, replicate_eq_arrOf])
      (by simp [hσ₃]) hys (by simp [hσ₃, hσ₂, hsplit]) hn1B hysB
  have hO : ∀ i ≤ n, O i = offset (n :: m :: rest) i := fun i hi => by
    rw [hO₄ i (by omega), hyd i (by omega)]
  -- the targets
  set σ₅ : Env := σ₄.setVar "m2" (2 * m) with hσ₅
  have r₅ : Run B (.assign "m2" (.add (.var "m") (.var "m"))) σ₄ σ₅ 4 :=
    (Run.assign (v := 2 * m)
      (by simp [r₄.frame_var "m" (by decide), hσ₃, hσ₂, hσ₁, initEnv, two_mul]
          omega)).mono (by simp)
  obtain ⟨σ₆, T, r₆, htgt₆, hT₆, hinp₆⟩ :=
    CC.readLoop_run (B := B) (a := "tgt") (lim := "m2") (by decide) (by decide) (σ := σ₅)
      (g := fun _ => 0) (k := 2 * m) (ys := zs) (rest := [k])
      (by rw [hσ₅, arrs_setVar, r₄.frame_arr "tgt" (by decide)]
          simp [hσ₃, hσ₂, hσ₁, initEnv, vcf3Ext, replicate_eq_arrOf])
      (by simp [hσ₅]) hzs (by simp [hσ₅, hinp₄]) hmB hzsB
  have hT : ∀ p < 2 * m, T p = target (n :: m :: rest) p := fun p hp => by
    rw [hT₆ p hp, hzd p hp]
  -- the budget
  set σ₇ : Env := { σ₆.setVar "bud" k with inp := [] } with hσ₇
  have r₇ : Run B (.read "bud") σ₆ σ₇ 1 := Run.read hinp₆
  -- what the search starts from
  have hm2₇ : σ₇.vars "m2" = 2 * m := by
    have h6 := r₆.frame_var "m2" (by decide)
    simp [hσ₇, h6, hσ₅]
  have hn₇ : σ₇.vars "n" = n := by
    have h6 := r₆.frame_var "n" (by decide)
    have h4 := r₄.frame_var "n" (by decide)
    simp [hσ₇, h6, hσ₅, h4, hσ₃, hσ₂, hσ₁, initEnv]
  have hbud₇ : σ₇.vars "bud" = k := by simp [hσ₇]
  have hzero : ∀ y : String, y ≠ "i" → y ≠ "t" → y ≠ "m2" → y ≠ "bud" → y ≠ "len" →
      y ≠ "n" → y ≠ "m" → σ₇.vars y = 0 := by
    intro y h1 h2 h3 h4 h5 h6 h7
    have e6 := r₆.frame_var y (by simp [h1, h2])
    have e4 := r₄.frame_var y (by simp [h1, h2])
    simp [hσ₇, h4, e6, hσ₅, h3, e4, hσ₃, hσ₂, hσ₁, initEnv, h5, h6, h7]
  have hmode₇ : σ₇.vars "mode" = 0 := hzero "mode" (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hans₇ : σ₇.vars "ans" = 0 := hzero "ans" (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have htop₇ : σ₇.vars "top" = 0 := hzero "top" (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have htt₇ : σ₇.vars "tt" = 0 := hzero "tt" (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have harr₇ : ∀ b : String, σ₇.arrs b = σ₆.arrs b := by intro b; simp [hσ₇]
  have hoff₇ : σ₇.arrs "off" = arrOf (n + 1) O := by
    rw [harr₇, r₆.frame_arr "off" (by decide), hσ₅, arrs_setVar, hoff₄]
  have htgt₇ : σ₇.arrs "tgt" = arrOf (2 * m) T := by rw [harr₇, htgt₆]
  have hmark₇ : σ₇.arrs "mark" = arrOf n (fun _ => 0) := by
    rw [harr₇, r₆.frame_arr "mark" (by decide), hσ₅, arrs_setVar, r₄.frame_arr "mark" (by decide)]
    simp [hσ₃, hσ₂, hσ₁, initEnv, vcf3Ext, replicate_eq_arrOf]
  have hvis₇ : σ₇.arrs "vis" = arrOf n (fun _ => 0) := by
    rw [harr₇, r₆.frame_arr "vis" (by decide), hσ₅, arrs_setVar, r₄.frame_arr "vis" (by decide)]
    simp [hσ₃, hσ₂, hσ₁, initEnv, vcf3Ext, replicate_eq_arrOf]
  have hq₇ : σ₇.arrs "q" = arrOf n (fun _ => 0) := by
    rw [harr₇, r₆.frame_arr "q" (by decide), hσ₅, arrs_setVar, r₄.frame_arr "q" (by decide)]
    simp [hσ₃, hσ₂, hσ₁, initEnv, vcf3Ext, replicate_eq_arrOf]
  have hrest₇ : ∀ a : String, a ≠ "off" → a ≠ "tgt" → a ≠ "mark" → a ≠ "vis" → a ≠ "q" →
      σ₇.arrs a = arrOf (n + 1) (fun _ => 0) := by
    intro a h1 h2 h3 h4 h5
    rw [harr₇, r₆.frame_arr a (by simp [h2]), hσ₅, arrs_setVar,
      r₄.frame_arr a (by simp [h1])]
    simp [hσ₃, hσ₂, hσ₁, initEnv, vcf3Ext, h2, h3, h4, h5, replicate_eq_arrOf]
  have hout₇ : σ₇.out = [] := by
    simp [hσ₇, r₆.out_eq (by decide), hσ₅, r₄.out_eq (by decide), hσ₃, hσ₂, hσ₁, initEnv]
  have hRep : Rep n m O T (⟨[], 0, k, 0⟩ : Config n) σ₇ := by
    refine ⟨hm2₇, hoff₇, htgt₇, hmode₇, hbud₇, hans₇, htop₇, htt₇,
      ⟨fun _ => 0, hmark₇, ?_⟩,
      ⟨fun _ => 0, hrest₇ "trail" (by decide) (by decide) (by decide) (by decide)
        (by decide), ?_⟩,
      fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
      hrest₇ "stkV" (by decide) (by decide) (by decide) (by decide) (by decide),
      hrest₇ "stkB" (by decide) (by decide) (by decide) (by decide) (by decide),
      hrest₇ "stkT" (by decide) (by decide) (by decide) (by decide) (by decide),
      hrest₇ "stkP" (by decide) (by decide) (by decide) (by decide) (by decide), ?_⟩
    · intro w hw; simp
    · intro i hi; simp at hi
    · intro i hi; simp at hi
  have hside : SideInv n σ₇ := ⟨hn₇, ⟨fun _ => 0, hvis₇⟩, ⟨fun _ => 0, hq₇⟩⟩
  -- the search
  obtain ⟨C', τ', K, r₈, hRep', hJ', hmode', hinp', hout', hpay⟩ :=
    searchLoop3_run hg hmg hO hT h2B hn2B hmB hk1B hRep hside (j3_init G k)
  have hK8 : K ≤ 6456 * (branchCount k * (5 + n + 2 * m)) + 4 := by
    refine hpay.trans ?_
    have ha : 1614 * (n + 2 * m + 1) ≤ 1614 * (5 + n + 2 * m) := by omega
    have hb : pot3 (⟨[], 0, k, 0⟩ : Config n) ≤ 4 * branchCount k := pot3_init_le k 0
    calc 1614 * (n + 2 * m + 1) * pot3 (⟨[], 0, k, 0⟩ : Config n) + 4
        ≤ 1614 * (5 + n + 2 * m) * (4 * branchCount k) + 4 :=
          Nat.add_le_add_right (Nat.mul_le_mul ha hb) 4
      _ = 6456 * (branchCount k * (5 + n + 2 * m)) + 4 := by ring
  -- the answer, written out
  have hansv : τ'.vars "ans" = C'.ans := hRep'.ans
  have hansle : C'.ans ≤ 1 := (hJ'.j.2.2.2.2.2 hmode').2
  have r₉ : Run B (.write (.var "ans")) τ' { τ' with out := τ'.out ++ [C'.ans] } 2 :=
    (Run.write (e := .var "ans") (v := C'.ans) (by simp [hansv]; omega)).mono (by simp)
  have hansC : C'.ans = if G.vertexCoverNum ≤ (k : ℕ∞) then 1 else 0 :=
    ans3_eq hJ' hmode'
  have s₈ := Run.seq (r₈.mono hK8) r₉
  have s₇ := Run.seq r₇ s₈
  have s₆ := Run.seq r₆ s₇
  have s₅ := Run.seq r₅ s₆
  have s₄ := Run.seq r₄ s₅
  have s₃ := Run.seq r₃ s₄
  have s₂ := Run.seq r₂ s₃
  refine ⟨_, 6500 * branchCount k * ((n :: m :: rest ++ [k]).length + 1),
    (Run.seq r₁ s₂).mono ?_, ?_, le_rfl⟩
  · have hlen2 : (n :: m :: rest ++ [k]).length + 1 = 5 + n + 2 * m := by
      simp; omega
    rw [hlen2, Nat.mul_assoc]
    have hQ : 5 + n + 2 * m ≤ branchCount k * (5 + n + 2 * m) :=
      Nat.le_mul_of_pos_left _ (branchCount_pos k)
    generalize branchCount k * (5 + n + 2 * m) = Q at hQ ⊢
    omega
  · simp [hout', hout₇, hansC]

/-- What the pipeline asks of the second driver: on every admissible
input it decides the question, at a cost of `6500 · branchCount k` per
entry of the input word, with every value it produces below the length
of that word plus the parameter. -/
theorem vcf3Com_solves (n : ℕ) (G : SimpleGraph (Fin n)) (k w : ℕ) :
    Solves vcf3Layout vcf3Com
      {x | EncodesParamInstance x n G k ∧ 318500 * (x.length + k + 1) ≤ 2 ^ w}
      (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
      (fun x => x.length + k)
      (fun x => 6500 * branchCount k * (x.length + 1)) where
  ok := vcf3Com_ok
  inp := fun _ hx _ hv => mem_lt_length_add hx.1 hv
  run := fun x hx => by
    obtain ⟨σ', K, hrun, hout, hK⟩ := vcf3Com_run hx.1 rfl le_rfl
    refine ⟨vcf3Ext n (edgeCount x), σ', hrun.mono hK, ?_⟩
    rw [hout]
    by_cases h : G.vertexCoverNum ≤ (k : ℕ∞) <;> simp [h]

/--
---
conclusion: Lax15.VertexCoverBranch.exists_branchTime_program_vertexCover
---
Vertex cover is decided in `branchCount k` time: `vcf3Program` decides,
on every graph in compressed sparse row form followed by the parameter
`k`, whether the graph has a vertex cover of at most `k` vertices,
within `318500 * branchCount k * (|x| + 1)` machine steps, at every word
length at which `318500 * (|x| + k + 1)` fits into a word.

# Proof strategy

The witness is the compiled driver `vcf3Program`, the second of this
submission's two. Its IMP+ source `vcf3Com` reads the encoding into the
two arrays of the components driver and the budget into a scalar — the
Fibonacci driver's read phase, character for character — and then runs a
bounded search tree as a single loop on a mode scalar. What changed is
the descend phase. One pass over the target array asks whether some
unmarked vertex has **three** distinct unmarked neighbours; if it does,
the search branches on it, at a cost of one unit of budget for the
branch that takes it and at least three for the branch that takes its
neighbourhood, so the leaf count obeys
`branchCount b = branchCount (b−1) + branchCount (b−3)`. If none does,
the branch is not searched at all: every unmarked vertex then has at
most two distinct unmarked neighbours, the residual graph is a disjoint
union of paths and cycles, and a solver block decides the whole subtree
outright. `vcf3Com_run` is that run, end to end.

The solver is the campaign's one genuinely new theorem. For a graph of
maximum degree two, the cover number is `∑_C ⌈e_C / 2⌉` over the
connected components. The upper bound is an induction on edges whose
step deletes the *neighbour of a degree-one vertex* when one exists and
any endpoint of an edge otherwise — the naive rule "delete any
degree-two vertex" is false, since deleting the middle vertex of a path
with four edges buys nothing — and the case where no degree-one vertex
exists is handled by a per-component handshake, so every degree in an
edge-bearing component is two. The lower bound is the observation that
a cover vertex covers at most two of its component's edges. The machine
computes that sum with a breadth-first sweep in the shape of the
components driver: one component at a time, each residual edge counted
once at its smaller endpoint, and the halving done by a toggle, since
the machine has no division.

Correctness is the invariant `J3`, which is the Fibonacci driver's `J`
together with one clause: every frame still owing its second branch was
pushed at residual degree at least three. `J` itself is reused as
stated — a branch at degree three satisfies its degree-two health clause
on the nose — and the extra clause is what feeds `d ≥ 3` to the flip,
which is the one transition whose drop needs it and the one place where
the fact is no longer visible. The two leaves of the solver take
semantic guards, `Ok G (marked) bud` and its negation, which the solver
lemma supplies from the component sum.

The cost is one amortized argument. The potential of a configuration is
`fPot3 b = 4·branchCount b − 3` for the active subtree, plus
`fPot3 (b−3) + 2` for each frame whose second branch is still owed and
one unit for each frame already on it, and every one of the eight
transitions strictly decreases it, so the whole tree is paid for by a
single application of the loop rule rather than by a recursion. The push
is where the recurrence is discharged:
`fPot3 (b−1) + fPot3 (b−3) + 3 ≤ fPot3 b` holds with equality, including
at the two budgets where truncated subtraction bends the recurrence, and
that is exactly what the `−3` and the two units of slack per stored
frame are for. A turn of the outer loop costs at most
`1610 · (n + 2m + 1)` — the scan is one flat pass, the solver is one
clearing pass plus one breadth-first sweep in which each vertex is
enqueued once and each row scanned once, and the flip and the pop are
bounded by a row and by the trail. The factor `branchCount k` enters
exactly once, as the potential of the initial configuration:
`pot3 ⟨[], 0, k, 0⟩ = 4·branchCount k − 2`.

`computesInTime_of_solves` discharges the compiler, the layout invariant
and the machine in one step, charging `vcf3Layout.const = 49` machine
steps per unit of IMP+ cost — ten arrays, so one index computation is
twelve instructions. The array extents are chosen per input, as that
lemma allows: `vcf3Ext n m` declares `off ↦ n+1`, `tgt ↦ 2m`, and
`mark`, `vis`, `q ↦ n`, with the trail and the four stacks `↦ n+1`,
which is what frame health permits, since the frames mark disjoint
nonempty sets of vertices and so there are at most `n` of them. The
value bound the driver is proved under is `|x| + k`, exactly as one rung
down, with one unit more of room — `n + 2 < B` rather than `n + 1 < B`,
because the solver compares its accumulated cost, which is at most `n`,
against `bud + 1`. Nothing the program computes is the running time:
`branchCount k` counts leaves, is never held in a register, and there is
no multiplication anywhere in `vcf3Com`.

# What the program is allowed to help itself to

*The branch test compares targets; it does not count slots.* The
encoding may name a neighbour of a vertex several times, so three
unmarked slots in a block are no evidence of three residual neighbours.
The scan therefore keeps two registers `t1`, `t2` holding the first and
second *distinct* unmarked target of the current block and raises the
flag only on a third that differs from both. This is what makes the
bound `branchCount` rather than merely correct, and it is the same trap
the Fibonacci driver's `Repeats.lean` records at threshold two.

*The dedup is one definition, used twice.* The descend scan and the
solver's row scan share `dedupStep` literally; they differ only in the
three commands hung on the first, second and third distinct target —
`skip, skip, recordFound` in the scan, `countPush, countPush, skip` in
the solver. A third distinct target cannot occur in the solver, since it
runs only when the scan found none, and the Run proof shows that branch
unreachable; the program skips it rather than counting it, so the count
never exceeds the residual edge count even off the invariant.

*The halving is a toggle, not a division.* The machine has no division
instruction, and `⌈e/2⌉` is exactly what a flag flipped once per counted
edge, with the count taken only when the flag is down, accumulates. The
toggle is reset at the root of each component, which is what makes the
total a sum of ceilings rather than one ceiling of a sum — and the
difference is real: two paths of one edge each cost two, not one.

*Each edge is counted at its smaller endpoint.* Both endpoints of a
residual edge are dequeued during the drain, so the edge is seen twice;
counting it only when the dequeued vertex is the smaller of the two
counts it exactly once, with no auxiliary marking.

*The queue is not reset between components.* `vis` is set before the
enqueue, so each vertex is enqueued at most once per solver call and the
queue pointers stay below `n` across the whole root sweep; only `vis`
itself is cleared, once per call, at the start.

*Each frame stores its own budget, and the marks come off a trail.*
Both are the Fibonacci driver's, unchanged and for the same reasons: the
two children of a branch no longer cost the same, so the budget is not a
function of the stack depth and `stkB` records it; and a frame on its
second branch marks a whole neighbourhood, so `stkT` records the trail
height it found and the pop walks the trail back down to it.

*The mark array is never initialized.* Fresh memory is zero and `0` is
the marker for "unmarked". The solver's `vis` array is cleared on every
call because it is used on every call; `mark` is not, because it is not.

# Attribution

The bounded search tree for vertex cover branching on a vertex, and the
recurrence `T(b) ≤ T(b−1) + T(b−3)` from a branching vertex of degree at
least three, are standard parameterized algorithmics — Downey and
Fellows for the setting, and the analysis as it appears in Cygan et al.,
§3.1, where this is the first step of the sequence of refinements that
brings the base down further. The solver at the leaf — that a graph of
maximum degree two is a disjoint union of paths and cycles, each covered
by `⌈e/2⌉` vertices and no fewer — is folklore; the proof here is a
direct induction and borrows no argument. Nothing in this submission
competes with the refined analyses that go below `1.4656`; the statement
asks for what this branching rule gives and no more.
-/
theorem exists_branchTime_program_vertexCover :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k w : ℕ),
      ComputesInTime w p
        {x | EncodesParamInstance x n G k ∧ c * (x.length + k + 1) ≤ 2 ^ w}
        (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
        (fun x => c * Lax15.VertexCoverBranch.branchCount k * (x.length + 1)) := by
  refine ⟨vcf3Program, 318500, fun n G k w =>
    computesInTime_of_solves (vcf3Com_solves n G k w) ?_ ?_⟩
  · rintro x ⟨⟨g, rfl, hg⟩, hw⟩
    have hglen := hg.length_eq
    simp only [List.length_append, List.length_cons, List.length_nil] at hw ⊢
    exact fitsWords_of_max_le (by omega) (by simp [Layout.span, vcf3Layout]; omega)
  · rintro x -
    rw [const3_eq, branchCount_eq]
    exact le_of_eq (by ring)

/-- The theorem discharges the concept's axiom and not a variant of it:
the equation typechecks only if the two statements are the same
proposition. -/
example : @exists_branchTime_program_vertexCover =
    @Lax15.VertexCoverBranch.exists_branchTime_program_vertexCover := rfl

end Lax15Proofs.VC3Main
