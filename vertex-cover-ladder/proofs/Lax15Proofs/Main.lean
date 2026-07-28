import Lax15Proofs.Loop
import Lax11Proofs.CCSweep
import Lax13Proofs.Transfer
import Lax15.VertexCover

/-!
The loop, the assembly, and the theorem.

Three things are left. The outer loop is one application of the loop
rule: the invariant is "some configuration is represented and satisfies
`J`, and the tapes are untouched", the potential is the pure one read
back off the two stack arrays, and the body of `Loop.lean` pays for a
turn out of it. The assembly is the read phase — the components
driver's, one `read` longer, exactly as in the `2^k` driver — followed
by the loop and one `write`. And the theorem is the concept's, cashed
in through the transfer theorem.

The potential the loop rule sees is a function of the environment, and
it may not consult the pure configuration. `framesOf` reads the stored
budget–phase pairs off `stkB` and `stkP` below `top`, totally: on a
represented state it is the pure stack, and off one it is whatever the
arrays happen to hold, which the loop rule never asks about. This is
the only place where the choice of `Config.lean`'s potential pays off —
`potN` reads exactly those two arrays and nothing else, so the crossing
is one `List.ext_getElem`.

The eight arrays of the layout cost the machine `43` steps per unit of
IMP+ cost, and the run itself costs at most `2100 · fib (k+2)` per entry
of the input word. The product `90300` is the constant of the statement,
and no part of it was fought over.
-/

namespace Lax15Proofs.VC

open Lax13.Ram Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax11Proofs.CC

variable {g : List ℕ} {n m k B : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}

/-! ### The potential, read off the arrays

The loop rule's potential is a function of the environment alone. -/

/-- The stack's budget–phase list, read back off `stkB` and `stkP`
top-first. Total on every environment; meaningful on represented ones,
where it is the pure stack's. -/
def framesOf (τ : Env) : List (ℕ × Bool) :=
  (List.range (τ.vars "top")).map
    (fun i => ((τ.arrs "stkB").getD (τ.vars "top" - 1 - i) 0,
      (τ.arrs "stkP").getD (τ.vars "top" - 1 - i) 0 == 1))

/-- On a represented state the numeric stack is the pure one. -/
theorem framesOf_eq {C : Config n} {τ : Env} (hRep : Rep n m O T C τ)
    (hlen : C.frames.length ≤ n) :
    framesOf τ = C.frames.map (fun f => (f.b, f.phase)) := by
  obtain ⟨SV, SB, ST, SP, -, hstkB, -, hstkP, hstk⟩ := hRep.stk
  have htop := hRep.top
  refine List.ext_getElem (by simp [framesOf, htop]) fun i h₁ h₂ => ?_
  simp only [framesOf, List.getElem_map, List.getElem_range, List.length_map,
    List.length_range] at h₁ h₂ ⊢
  rw [htop] at h₁ ⊢
  have hil : C.frames.length - 1 - i < C.frames.length := by omega
  have hin : C.frames.length - 1 - i < n + 1 := by omega
  obtain ⟨-, hb, -, hp⟩ := hstk (C.frames.length - 1 - i) hil
  rw [hstkB, hstkP, getD_arrOf SB hin, getD_arrOf SP hin, hb, hp]
  have hrev : (C.frames.reverse[C.frames.length - 1 - i]'(by simpa using hil)) =
      C.frames[i]'h₂ := by
    rw [List.getElem_reverse]
    congr 1
    omega
  rw [hrev]
  cases hph : (C.frames[i]'h₂).phase <;> simp

/-- On a represented state the numeric potential is the pure one. -/
theorem potN_eq {C : Config n} {τ : Env} (hRep : Rep n m O T C τ)
    (hlen : C.frames.length ≤ n) :
    potN (τ.vars "mode") (τ.vars "bud") (framesOf τ) = pot C := by
  rw [hRep.mode, hRep.bud, framesOf_eq hRep hlen, ← pot_eq_potN]

/-! ### The loop

One application of `Run.while_potential`. A turn pays `1 + 3` for the test and
at most `510 · (n + 2m + 1)` for the body, and buys one unit of `pot`,
so the scale `514 · (n + 2m + 1)` covers it. The whole search is
therefore paid for by the potential of the configuration it starts
from — and that potential is where, and only where, `fib (k + 2)`
enters. -/

/-- **The search loop.** From a represented state satisfying the
invariant, the outer loop reaches a represented, invariant state in
mode `2`, in at most `514 · (n + 2m + 1) · pot C₀ + 4` steps. -/
theorem searchLoop_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ p < 2 * m, T p = target g p)
    (h2B : 2 < B) (hnB : n + 1 < B) (hmB : 2 * m < B) (hkB : k + 1 < B)
    {C₀ : Config n} {σ : Env} (hRep : Rep n m O T C₀ σ) (hJ : J G k C₀) :
    ∃ (C' : Config n) (τ' : Env) (K : ℕ),
      Run B (.while (.lt (.var "mode") (.lit 2)) outerBody) σ τ' K ∧
      Rep n m O T C' τ' ∧ J G k C' ∧ C'.mode = 2 ∧
      τ'.inp = σ.inp ∧ τ'.out = σ.out ∧
      K ≤ 514 * (n + 2 * m + 1) * pot C₀ + 4 := by
  -- the test always evaluates: the mode is at most `2`, and `2` is a word
  have hdef : ∀ τ : Env,
      (∃ C, Rep n m O T C τ ∧ J G k C ∧ τ.inp = σ.inp ∧ τ.out = σ.out) →
      ∃ v, (Cond.lt (.var "mode") (.lit 2)).evalB B τ = some v := by
    rintro τ ⟨C, hRepC, hJC, -, -⟩
    have hmd : τ.vars "mode" = C.mode := hRepC.mode
    have := hJC.1
    exact evalB_condLt_var_lit (by omega) (by omega)
  -- a turn: the body runs, the invariant survives, the potential pays
  have hstep : ∀ τ : Env,
      (∃ C, Rep n m O T C τ ∧ J G k C ∧ τ.inp = σ.inp ∧ τ.out = σ.out) →
      (Cond.lt (.var "mode") (.lit 2)).evalB B τ = some true →
      ∃ τ'' K, Run B outerBody τ τ'' K ∧
        (∃ C, Rep n m O T C τ'' ∧ J G k C ∧ τ''.inp = σ.inp ∧ τ''.out = σ.out) ∧
        1 + (Cond.lt (Expr.var "mode") (Expr.lit 2)).size + K +
            514 * (n + 2 * m + 1) *
              potN (τ''.vars "mode") (τ''.vars "bud") (framesOf τ'') ≤
          514 * (n + 2 * m + 1) *
            potN (τ.vars "mode") (τ.vars "bud") (framesOf τ) := by
    rintro τ ⟨C, hRepC, hJC, hinp, hout⟩ hc
    have hc' := Cond.eval_of_evalB hc
    have hmd : τ.vars "mode" = C.mode := hRepC.mode
    have hmode : C.mode < 2 := by
      simp only [Cond.eval, Expr.eval, Option.bind_some, Option.map_some,
        Option.some.injEq, decide_eq_true_eq, hmd] at hc'
      exact hc'
    obtain ⟨C', τ'', K, hrunb, hRep', hJ', hpot, hi, ho, hK⟩ :=
      outerBody_run hg hm hO hT h2B hnB hmB hkB hRepC hJC hmode
    refine ⟨τ'', K, hrunb, ⟨C', hRep', hJ', by rw [hi, hinp], by rw [ho, hout]⟩, ?_⟩
    have e1 := potN_eq hRep' hJ'.frames_length_le
    have e2 := potN_eq hRepC hJC.frames_length_le
    have hmul : 514 * (n + 2 * m + 1) * (pot C' + 1) ≤
        514 * (n + 2 * m + 1) * pot C := Nat.mul_le_mul_left _ hpot
    rw [Nat.mul_succ] at hmul
    rw [e1, e2]
    simp only [size_condLt, size_var, size_lit]
    omega
  obtain ⟨τ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := Cond.lt (.var "mode") (.lit 2)) (c := outerBody)
      (fun τ => ∃ C, Rep n m O T C τ ∧ J G k C ∧ τ.inp = σ.inp ∧ τ.out = σ.out)
      (fun τ => 514 * (n + 2 * m + 1) *
        potN (τ.vars "mode") (τ.vars "bud") (framesOf τ))
      hdef hstep ⟨C₀, hRep, hJ, rfl, rfl⟩
  -- exit: the test is false and `J` caps the mode, so the mode is `2`
  obtain ⟨C', hRep', hJ', hinp', hout'⟩ := hI'
  have hfalse' := Cond.eval_of_evalB hfalse
  have hmd' : τ'.vars "mode" = C'.mode := hRep'.mode
  have hmode' : C'.mode = 2 := by
    simp only [Cond.eval, Expr.eval, Option.bind_some, Option.map_some,
      Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt, hmd'] at hfalse'
    have := hJ'.1
    omega
  have hΦ₀ := potN_eq hRep hJ.frames_length_le
  refine ⟨C', τ', K, hrun, hRep', hJ', hmode', hinp', hout', ?_⟩
  simp only [size_condLt, size_var, size_lit, hΦ₀] at hpay
  omega

end Lax15Proofs.VC

namespace Lax15Proofs.VCMain

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding Lax11.VertexCover
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning Lax13Proofs.Transfer
open Lax11Proofs Lax15Proofs.VC

/-- The array extents the driver runs with: the two arrays of the
encoding at the lengths the header gives them, the mark array one per
vertex, and the trail and the four stacks one longer — frame health
makes both heights at most `n`, and a push writes at the height it
finds. -/
def vcfExt (n m : ℕ) (a : String) : ℕ :=
  if a = "tgt" then 2 * m else if a = "mark" then n else n + 1

/-- The machine pays forty-three steps per unit of IMP+ cost: eight
arrays make one index computation ten instructions long. -/
theorem const_eq : vcfLayout.const = 43 := by
  simp [Layout.const, Layout.idxLen, vcfLayout]

/-- Every entry of an instance word is below the length of the word
plus the parameter: the graph block's entries are smaller than the
block is long, and the one remaining entry is the parameter itself. -/
theorem mem_lt_length_add {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (hx : EncodesParamInstance x n G k) {v : ℕ} (hv : v ∈ x) : v < x.length + k := by
  obtain ⟨g, rfl, hg⟩ := hx
  rcases List.mem_append.1 hv with h | h
  · have := CC.mem_lt_length hg h
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- The whole run of the driver on an encoded instance: the answer comes
out, the cost is `fib (k + 2)` times linear in the length of the word,
and every value the run produces stays below any bound the length of the
word and the parameter together stay below. Every phase was bounded
loosely, and this is the sum of those bounds. -/
theorem vcfCom_run {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k m B : ℕ}
    (hx : EncodesParamInstance x n G k) (hm : edgeCount x = m) (hB : x.length + k ≤ B) :
    ∃ (σ' : Env) (K : ℕ), Run B vcfCom (initEnv (vcfExt n m) x) σ' K ∧
      σ'.out = [if G.vertexCoverNum ≤ (k : ℕ∞) then 1 else 0] ∧
      K ≤ 2100 * Nat.fib (k + 2) * (x.length + 1) := by
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
  have hk1B : k + 1 < B := by omega
  have hnB : n < B := by omega
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
  have e₁ : (initEnv (vcfExt n m) (n :: m :: rest ++ [k])).inp
      = n :: (m :: (rest ++ [k])) := rfl
  set σ₁ : Env := { (initEnv (vcfExt n m) (n :: m :: rest ++ [k])).setVar "n" n with
    inp := m :: (rest ++ [k]) } with hσ₁
  set σ₂ : Env := { σ₁.setVar "m" m with inp := rest ++ [k] } with hσ₂
  set σ₃ : Env := σ₂.setVar "len" (n + 1) with hσ₃
  have r₁ : Run B (.read "n") (initEnv (vcfExt n m) (n :: m :: rest ++ [k])) σ₁ 1 :=
    Run.read e₁
  have r₂ : Run B (.read "m") σ₁ σ₂ 1 := Run.read rfl
  have r₃ : Run B (.assign "len" (.add (.var "n") (.lit 1))) σ₂ σ₃ 4 :=
    (Run.assign (v := n + 1) (by simp [hσ₂, hσ₁, initEnv]; omega)).mono (by simp)
  -- the offsets
  obtain ⟨σ₄, O, r₄, hoff₄, hO₄, harr₄, hinp₄, hout₄, hvar₄⟩ :=
    CC.readLoop_run (B := B) (a := "off") (lim := "len") (by decide) (by decide) (σ := σ₃)
      (g := fun _ => 0) (k := n + 1) (ys := ys) (rest := zs ++ [k])
      (by simp [hσ₃, hσ₂, hσ₁, initEnv, vcfExt, replicate_eq_arrOf])
      (by simp [hσ₃]) hys (by simp [hσ₃, hσ₂, hsplit]) hn1B hysB
  have hO : ∀ i ≤ n, O i = offset (n :: m :: rest) i := fun i hi => by
    rw [hO₄ i (by omega), hyd i (by omega)]
  -- the targets
  set σ₅ : Env := σ₄.setVar "m2" (2 * m) with hσ₅
  have r₅ : Run B (.assign "m2" (.add (.var "m") (.var "m"))) σ₄ σ₅ 4 :=
    (Run.assign (v := 2 * m)
      (by simp [hvar₄ "m" (by decide) (by decide), hσ₃, hσ₂, hσ₁, initEnv, two_mul]
          omega)).mono (by simp)
  obtain ⟨σ₆, T, r₆, htgt₆, hT₆, harr₆, hinp₆, hout₆, hvar₆⟩ :=
    CC.readLoop_run (B := B) (a := "tgt") (lim := "m2") (by decide) (by decide) (σ := σ₅)
      (g := fun _ => 0) (k := 2 * m) (ys := zs) (rest := [k])
      (by rw [hσ₅, arrs_setVar, harr₄ "tgt" (by decide)]
          simp [hσ₃, hσ₂, hσ₁, initEnv, vcfExt, replicate_eq_arrOf])
      (by simp [hσ₅]) hzs (by simp [hσ₅, hinp₄]) hmB hzsB
  have hT : ∀ p < 2 * m, T p = target (n :: m :: rest) p := fun p hp => by
    rw [hT₆ p hp, hzd p hp]
  -- the budget
  set σ₇ : Env := { σ₆.setVar "bud" k with inp := [] } with hσ₇
  have r₇ : Run B (.read "bud") σ₆ σ₇ 1 := Run.read hinp₆
  -- what the search starts from
  have hm2₇ : σ₇.vars "m2" = 2 * m := by
    have h6 := hvar₆ "m2" (by decide) (by decide)
    simp [hσ₇, h6, hσ₅]
  have hbud₇ : σ₇.vars "bud" = k := by simp [hσ₇]
  have hzero : ∀ y : String, y ≠ "i" → y ≠ "t" → y ≠ "m2" → y ≠ "bud" → y ≠ "len" →
      y ≠ "n" → y ≠ "m" → σ₇.vars y = 0 := by
    intro y h1 h2 h3 h4 h5 h6 h7
    have e6 := hvar₆ y h1 h2
    have e4 := hvar₄ y h1 h2
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
    rw [harr₇, harr₆ "off" (by decide), hσ₅, arrs_setVar, hoff₄]
  have htgt₇ : σ₇.arrs "tgt" = arrOf (2 * m) T := by rw [harr₇, htgt₆]
  have hmark₇ : σ₇.arrs "mark" = arrOf n (fun _ => 0) := by
    rw [harr₇, harr₆ "mark" (by decide), hσ₅, arrs_setVar, harr₄ "mark" (by decide)]
    simp [hσ₃, hσ₂, hσ₁, initEnv, vcfExt, replicate_eq_arrOf]
  have hrest₇ : ∀ a : String, a ≠ "off" → a ≠ "tgt" → a ≠ "mark" →
      σ₇.arrs a = arrOf (n + 1) (fun _ => 0) := by
    intro a h1 h2 h3
    rw [harr₇, harr₆ a h2, hσ₅, arrs_setVar, harr₄ a h1]
    simp [hσ₃, hσ₂, hσ₁, initEnv, vcfExt, h2, h3, replicate_eq_arrOf]
  have hout₇ : σ₇.out = [] := by
    simp [hσ₇, hout₆, hσ₅, hout₄, hσ₃, hσ₂, hσ₁, initEnv]
  have hRep : Rep n m O T (⟨[], 0, k, 0⟩ : Config n) σ₇ := by
    refine ⟨hm2₇, hoff₇, htgt₇, hmode₇, hbud₇, hans₇, htop₇, htt₇,
      ⟨fun _ => 0, hmark₇, ?_⟩,
      ⟨fun _ => 0, hrest₇ "trail" (by decide) (by decide) (by decide), ?_⟩,
      fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
      hrest₇ "stkV" (by decide) (by decide) (by decide),
      hrest₇ "stkB" (by decide) (by decide) (by decide),
      hrest₇ "stkT" (by decide) (by decide) (by decide),
      hrest₇ "stkP" (by decide) (by decide) (by decide), ?_⟩
    · intro w hw; simp
    · intro i hi; simp at hi
    · intro i hi; simp at hi
  -- the search
  obtain ⟨C', τ', K, r₈, hRep', hJ', hmode', hinp', hout', hpay⟩ :=
    searchLoop_run hg hmg hO hT h2B hn1B hmB hk1B hRep (j_init G k)
  have hK8 : K ≤ 2056 * (Nat.fib (k + 2) * (5 + n + 2 * m)) + 4 := by
    refine hpay.trans ?_
    have ha : 514 * (n + 2 * m + 1) ≤ 514 * (5 + n + 2 * m) := by omega
    have hb : pot (⟨[], 0, k, 0⟩ : Config n) ≤ 4 * Nat.fib (k + 2) := pot_init_le k 0
    calc 514 * (n + 2 * m + 1) * pot (⟨[], 0, k, 0⟩ : Config n) + 4
        ≤ 514 * (5 + n + 2 * m) * (4 * Nat.fib (k + 2)) + 4 :=
          Nat.add_le_add_right (Nat.mul_le_mul ha hb) 4
      _ = 2056 * (Nat.fib (k + 2) * (5 + n + 2 * m)) + 4 := by ring
  -- the answer, written out
  have hansv : τ'.vars "ans" = C'.ans := hRep'.ans
  have hansle : C'.ans ≤ 1 := (hJ'.2.2.2.2.2 hmode').2
  have r₉ : Run B (.write (.var "ans")) τ' { τ' with out := τ'.out ++ [C'.ans] } 2 :=
    (Run.write (e := .var "ans") (v := C'.ans) (by simp [hansv]; omega)).mono (by simp)
  have hansC : C'.ans = if G.vertexCoverNum ≤ (k : ℕ∞) then 1 else 0 :=
    ans_eq hJ' hmode'
  have s₈ := Run.seq (r₈.mono hK8) r₉
  have s₇ := Run.seq r₇ s₈
  have s₆ := Run.seq r₆ s₇
  have s₅ := Run.seq r₅ s₆
  have s₄ := Run.seq r₄ s₅
  have s₃ := Run.seq r₃ s₄
  have s₂ := Run.seq r₂ s₃
  refine ⟨_, 2100 * Nat.fib (k + 2) * ((n :: m :: rest ++ [k]).length + 1),
    (Run.seq r₁ s₂).mono ?_, ?_, le_rfl⟩
  · have hlen2 : (n :: m :: rest ++ [k]).length + 1 = 5 + n + 2 * m := by
      simp; omega
    rw [hlen2, Nat.mul_assoc]
    have hQ : 5 + n + 2 * m ≤ Nat.fib (k + 2) * (5 + n + 2 * m) :=
      Nat.le_mul_of_pos_left _ (Nat.fib_pos.2 (by omega))
    generalize Nat.fib (k + 2) * (5 + n + 2 * m) = Q at hQ ⊢
    omega
  · simp [hout', hout₇, hansC]

/-- What the pipeline asks of the driver: on every admissible input it
decides the question, at a cost of `2100 · fib (k + 2)` per entry of the
input word, with every value it produces below the length of that word
plus the parameter. -/
theorem vcfCom_solves (n : ℕ) (G : SimpleGraph (Fin n)) (k w : ℕ) :
    Solves vcfLayout vcfCom
      {x | EncodesParamInstance x n G k ∧ 90300 * (x.length + k + 1) ≤ 2 ^ w}
      (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
      (fun x => x.length + k)
      (fun x => 2100 * Nat.fib (k + 2) * (x.length + 1)) where
  ok := vcfCom_ok
  inp := fun _ hx _ hv => mem_lt_length_add hx.1 hv
  run := fun x hx => by
    obtain ⟨σ', K, hrun, hout, hK⟩ := vcfCom_run hx.1 rfl le_rfl
    refine ⟨vcfExt n (edgeCount x), σ', hrun.mono hK, ?_⟩
    rw [hout]
    by_cases h : G.vertexCoverNum ≤ (k : ℕ∞) <;> simp [h]

/--
---
conclusion: Lax15.VertexCover.exists_fibTime_program_vertexCover
---
Vertex cover is decided in Fibonacci-of-`k` time: `vcfProgram` decides,
on every graph in compressed sparse row form followed by the parameter
`k`, whether the graph has a vertex cover of at most `k` vertices,
within `90300 * fib (k + 2) * (|x| + 1)` machine steps, at every word
length at which `90300 * (|x| + k + 1)` fits into a word.

# Proof strategy

The witness is the compiled driver `vcfProgram`. Its IMP+ source
`vcfCom` reads the encoding into the two arrays of the components driver
and the budget into a scalar, then runs a bounded search tree that
branches on a *vertex* rather than on an edge, as a single loop on a
mode scalar. Descend makes one pass over the target array and either
answers, gives up on the branch, or pushes a frame on a vertex `v` with
two or more residual neighbours, marking `v`; backtrack either answers
`0`, flips the top frame to its second branch — marking the whole
residual neighbourhood of its vertex, which costs at least two units of
budget — or pops it. `vcfCom_run` is that run, end to end.

Correctness is the invariant `J`, which splits the answer between the
active marking and the alternatives the frames still owe: in descend
mode `Ok ∅ k` holds exactly if the current marking extends to a cover
within the remaining budget or some stored alternative does, in
backtrack mode exactly if some stored alternative does. Eight
transitions preserve it, each resting on one of three graph lemmas —
that at most `b` residual edges admit a cover within `b`, that a
residual matching of more than `b` edges admits none, and that
branching on a vertex is exhaustive — and `ans_eq` reads the concept's
answer off the terminal state, the one place where mathlib's
`vertexCoverNum` is touched.

The cost is one amortized argument. The potential of a configuration is
`fPot b = 4·fib (b + 2) − 3` for the active subtree, plus `fPot (b−2) +
2` for each frame whose second branch is still owed and one unit for
each frame already on it, and every one of the eight transitions
strictly decreases it, so the whole tree is paid for by a single
application of the loop rule rather than by a recursion. The push is
where the recurrence is discharged: `fPot (b−1) + fPot (b−2) + 3 ≤
fPot b` holds with equality, and that is exactly what the Fibonacci
identity buys over the doubling one. A turn of the outer loop costs at
most `510 · (n + 2m + 1)` — the descend scan is flat, one pointer over
the target array with the block owner walking alongside, and the flip
and the pop are bounded by a row and by the trail. The factor
`fib (k + 2)` enters exactly once, as the potential of the initial
configuration: `pot ⟨[], 0, k, 0⟩ = 4·fib (k + 2) − 2`.

`computesInTime_of_solves` discharges the compiler, the layout
invariant and the machine in one step, charging `vcfLayout.const = 43`
machine steps per unit of IMP+ cost — eight arrays, so one index
computation is ten instructions. The array extents are chosen per input,
as that lemma allows: `vcfExt n m` declares `off ↦ n+1`, `tgt ↦ 2m`,
`mark ↦ n`, and the trail and the four stacks `↦ n+1`, which is what
frame health permits, since the frames mark disjoint nonempty sets of
vertices and so there are at most `n` of them.

# Where the word length is paid for

The machine truncates every value modulo `2 ^ w`, so the run on the
machine is the run in the unbounded semantics only as long as nothing
the program computes reaches `2 ^ w`. The bound the driver is proved
under is `|x| + k`: every entry of the graph block is smaller than the
block is long, every quantity the algorithm keeps of the graph — vertex
numbers, offsets, the scan pointers, the trail height and the stack
height — is bounded by `n` or by `2m`, hence again by the length, and
the two quantities that are not are the parameter itself and the
budgets stored in the frames, which lie between `0` and `k`. So the
whole run needs the single hypothesis `|x| + k ≤ B`, and the compiled
program needs in addition that the cells the layout addresses are
words, which is `30 + 8(|x| + k)`. The statement's hypothesis, that
`90300(|x| + k + 1)` is a word, gives both with room to spare.

What the hypothesis deliberately does *not* say is that the running
time fits into a word. `fib (k + 2)` counts the leaves of the search
tree; it is not a number the machine ever holds, and nothing in the
program ever computes a Fibonacci number — there is no multiplication
anywhere in `vcfCom`, and the budgets it manipulates are below `k`.
Asking for `fib (k + 2)` to be a word would make the claim vacuous
exactly where the algorithm is most interesting, and would be a weaker
theorem carrying the same bound. The admissible set is character for
character the one of the `2 ^ k` statement, so the improved bound is
claimed on exactly the same instances.

# What the program is allowed to help itself to

*Each frame stores its own budget.* Unlike the `2 ^ k` driver, the two
children of a branch do not cost the same: the first spends one unit,
the second spends the residual degree. So the budget is not a function
of the stack depth and cannot be recovered by counting frames; `stkB`
records it at the push and both the flip and the pop restore it from
there. Nothing is reconstructed on backtracking that was not written
down.

*The marks are undone by a trail, not by name.* A frame on its second
branch marks a whole neighbourhood, so unmarking it is not one store.
Each frame records the trail height it found in `stkT`, and a pop walks
the trail back down to that height, unmarking as it goes. The trail is
what makes the pop's cost linear in what the frame marked rather than in
the vertex set, and its total length is at most `n` because the frames'
marked sets are disjoint and nonempty.

*The mark array is never initialized.* Fresh memory is zero and `0` is
the marker for "unmarked", so the driver skips the clearing pass. The
bound is `fib (k + 2)` times linear and a clearing pass is linear, so
the pass would have been free; it is omitted because it is unnecessary,
not because it is expensive.

*The branch test does not count slots.* The encoding may name a
neighbour of a vertex several times, so two unmarked slots in a block
are no evidence of two residual neighbours, and the residual owner
count `ro` is capped at one per block for the same reason. Both are the
reason the bound is Fibonacci rather than merely correct: a slot-counting
test would branch on a matching whose blocks repeat, and search a
`2 ^ k` tree on an instance this program answers without a push.

# Attribution

The vertex-branching bounded search tree for vertex cover, with the
Fibonacci recurrence `T(k) ≤ T(k−1) + T(k−2)` and the matching leaf —
Downey and Fellows for the parameterized setting, and the analysis as it
appears in Cygan et al. The base `φ ≈ 1.618` is the point of the
statement: no reduction rules are applied, and nothing here competes
with the refined analyses that beat it.
-/
theorem exists_fibTime_program_vertexCover :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k w : ℕ),
      ComputesInTime w p
        {x | EncodesParamInstance x n G k ∧ c * (x.length + k + 1) ≤ 2 ^ w}
        (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
        (fun x => c * Nat.fib (k + 2) * (x.length + 1)) := by
  refine ⟨vcfProgram, 90300, fun n G k w =>
    computesInTime_of_solves (vcfCom_solves n G k w) ?_ ?_⟩
  · rintro x ⟨⟨g, rfl, hg⟩, hw⟩
    have hglen := hg.length_eq
    simp only [List.length_append, List.length_cons, List.length_nil] at hw ⊢
    exact fitsWords_of_max_le (by omega) (by simp [Layout.span, vcfLayout]; omega)
  · rintro x -
    rw [const_eq]
    exact le_of_eq (by ring)

/-- The theorem discharges the concept's axiom and not a variant of it:
the equation typechecks only if the two statements are the same
proposition. -/
example : @exists_fibTime_program_vertexCover =
    @Lax15.VertexCover.exists_fibTime_program_vertexCover := rfl

end Lax15Proofs.VCMain
