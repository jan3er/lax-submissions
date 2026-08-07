import Lax3Proofs.Refine.AugCompact

/-!
# ND-MC G2/E2 — the two preparation walks, discharged

`Refine/SymCompact.lean` §7 leaves `SymPreps` and `Refine/AugCompact.lean`
§9 leaves `AugPreps`: the two named obligations of the compacted-arena
engine family that say the preparation passes move the compact in-lists
into the engine's input arrays and zero what the engine asks zeroed —
over the **compact prefix**, at an arena-affine charge, keeping every
cell of the level's own arrays above the prefix.

Both parents wrote the discharger's kit into their headers
(`SymCompact` §7.0, `AugCompact` §9.0) and this file follows it: the two
obligations are three and eleven applications of
`RamDriverOrder.copyKeep_spec`/`fillKeep_spec` — the live-prefix half of
the flat-pass kit, whose postconditions carry the tail-kept clause the
live-prefix reading needs — at a single shared invariant.

## What this file adds beyond the kit

Three things, and they are what makes eleven applications readable:

* `PrepQ`, the one invariant every pass runs in (the two bound scalars
  `"mm"`/`"kd"` and the two source arrays `"ioff"`/`"itg"`). Every pass
  writes a *different* array — never a source — and only the kit's
  counter `"i"`, so the kit's frame side condition is discharged once
  (`prepQ_frame`) instead of eleven times.
* Four pass wrappers (`copyIoff_spec`, `copyItg_spec`, `zeroM1_spec`,
  `zeroM_spec`), one per bound shape the two programs use, each already
  charged at its closed cost: `14·mm + 22`, `12·kd + 6`, `13·mm + 21`,
  `11·mm + 6`.
* The prefix/suffix run trick for the frames. A composite of eleven
  passes needs, for each destination, that the later passes leave it
  alone and that the earlier passes leave its length alone. Chaining the
  eleven single-pass frames costs a quadratic number of rewrites; naming
  the *prefix* runs `σ → τₖ` and the *suffix* runs `τₖ → τ₁₁` and framing
  through those costs one rewrite apiece.

## The charge

`27·mm + 12·kd + 49` for the symmetrization's three passes and
`121·mm + 12·kd + 142` for the round's eleven — inside
`symPrepCost mm kd = 100·mm + 100·kd + 100` and
`augPrepCost mm kd = 1000·mm + 100·kd + 1000` with room. **No carrier
term appears**, which is the whole point of the E2 wave; §0 compiles that
on data, at two carriers eight times apart.

Nothing here is `sorry`, and neither theorem takes an antecedent beyond
the ones the parents' obligations already quantify.
-/

namespace Lax3Proofs.Refine.CompactPreps

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamDriver (copyUpto fillUpto)
open Lax3Proofs.TgtWidenProbe (PSt PRes execC pB pF star5doff star5dtg aug5doff aug5dtg)
open Lax3Proofs.Refine.SymCompact (symPrepCom symPrepCost SymPreps sSt
  notMem_symPrepCom_warrs notMem_symPrepCom_wvars)
open Lax3Proofs.Refine.AugCompact (augPrepCom augPrepCost AugPreps aSt
  notMem_augPrepCom_warrs notMem_augPrepCom_wvars)

/-! ## §0 Refute before prove

The parents compiled the *semantic* falsifications already, both in their
§2.3: without the relink the pass symmetrizes/augments the sentinel, and
without the nine fills the round has **no run at all** — the D4 stuck
mechanism at the sub-elimination's bucket read. Those are reused, not
re-derived. What is compiled here is the part of each obligation those
probes do **not** pin: the postcondition cell by cell on the preparation
*alone*, and the cost clause — the clause that was defective twice in
this file family (`CompactInstalls` charged the live slot count while its
walk crossed the raw row). The clock is `TgtWidenProbe.execC`,
`BigStepB`'s cost algebra rule for rule. -/

/-! ### §0.1 `SymPreps` on `SymCompact`'s five-member arena -/

/-- The three preparation passes alone, clocked, on the store `SymCompact`
§2 refutes and proves the composite on. -/
def symPrepClock (n W mm kd : ℕ) : PRes × ℕ := execC pB pF symPrepCom (sSt n W mm kd)

def symPrepRun (n W mm kd : ℕ) : PRes := (symPrepClock n W mm kd).1

#guard (symPrepRun 100 64 5 10).isOk
#guard (symPrepRun 800 64 5 10).isOk
#guard (symPrepRun 100 64 20 10).isOk

-- **the relink**: the compact in-lists, where the pass reads them
#guard (List.range 6).map ((symPrepRun 100 64 5 10).cell "doff") = aug5doff
#guard (List.range 10).map ((symPrepRun 100 64 5 10).cell "dtg") = aug5dtg
-- **the zero**: the counting sort's accumulator over the compact prefix
#guard (List.range 6).all fun i => (symPrepRun 100 64 5 10).cell "ooff" i == 0

-- **the tails, kept** — the sentinel `7` above each compact prefix comes
-- back, which is the live-prefix half of the obligation
#guard (List.range 95).all fun k => (symPrepRun 100 64 5 10).cell "doff" (6 + k) == 7
#guard (List.range 54).all fun k => (symPrepRun 100 64 5 10).cell "dtg" (10 + k) == 7
#guard (List.range 95).all fun k => (symPrepRun 100 64 5 10).cell "ooff" (6 + k) == 7

-- **the arrays the walk must not touch at all**, whole
#guard (List.range 101).all fun k => (symPrepRun 100 64 5 10).cell "off" k == 7
#guard (List.range 64).all fun k => (symPrepRun 100 64 5 10).cell "tgt" k == 7
#guard (List.range 100).all fun k => (symPrepRun 100 64 5 10).cell "ofl" k == 7
#guard (List.range 64).all fun k => (symPrepRun 100 64 5 10).cell "otg" k == 7

-- the two scalars the obligation hands back
#guard (symPrepRun 100 64 5 10).scalar "n" = 100
#guard (symPrepRun 100 64 5 10).scalar "mm" = 5

-- **the honesty direction**: the compact prefix really did change, so the
-- frame above is not bought by writing nothing
#guard ¬ ((List.range 6).all fun k => (symPrepRun 100 64 5 10).cell "doff" k == 7)

-- **the charge**, on data
#guard (symPrepClock 100 64 5 10).2 ≤ symPrepCost 5 10
-- **carrier-blind**: eight times the carrier, the very same clock
#guard (symPrepClock 800 64 5 10).2 = (symPrepClock 100 64 5 10).2
-- …and genuinely arena-affine, so the cost is not blind by being trivial
#guard (symPrepClock 100 64 5 10).2 < (symPrepClock 100 64 20 10).2

/-! ### §0.2 `AugPreps` on `AugCompact`'s five-member arena -/

/-- `AugCompact`'s store with the carrier already installed — the round's
preparation runs *after* `symSetCarrier`, so `"n"` is the arena's. -/
def aPrepSt (n W mm kd : ℕ) : PSt :=
  { aSt n W mm kd with vars := [("n", mm), ("m", 0), ("lw", W), ("mm", mm), ("kd", kd)] }

def augPrepClock (n W mm kd : ℕ) : PRes × ℕ := execC pB pF augPrepCom (aPrepSt n W mm kd)

def augPrepRun (n W mm kd : ℕ) : PRes := (augPrepClock n W mm kd).1

#guard (augPrepRun 100 200 5 4).isOk
#guard (augPrepRun 800 200 5 4).isOk
#guard (augPrepRun 100 200 20 4).isOk

-- **the relink**
#guard (List.range 6).map ((augPrepRun 100 200 5 4).cell "doff") = star5doff
#guard (List.range 4).map ((augPrepRun 100 200 5 4).cell "dtg") = star5dtg
-- **the nine fills**, over the compact prefix
#guard ["ooff", "off", "noff", "bh"].all fun a =>
  (List.range 6).all fun i => (augPrepRun 100 200 5 4).cell a i == 0
#guard ["elm", "stf", "sta", "std", "ste"].all fun a =>
  (List.range 5).all fun i => (augPrepRun 100 200 5 4).cell a i == 0

-- **the tails, kept**
#guard (List.range 95).all fun k => (augPrepRun 100 200 5 4).cell "doff" (6 + k) == 7
#guard (List.range 196).all fun k => (augPrepRun 100 200 5 4).cell "dtg" (4 + k) == 7
#guard ["ooff", "off", "noff", "bh"].all fun a =>
  (List.range 95).all fun k => (augPrepRun 100 200 5 4).cell a (6 + k) == 7
#guard ["elm", "stf", "sta", "std", "ste"].all fun a =>
  (List.range 95).all fun k => (augPrepRun 100 200 5 4).cell a (5 + k) == 7

-- **the arrays the walk must not touch**, including the two the
-- obligation hands back by name (`"mem"`, `"ork"`)
#guard ["otg", "ofl", "tgt", "ffl", "alv", "deg", "rnk", "idg", "ifl", "nfl", "ntg",
    "ork"].all fun a => (List.range 5).all fun k => (augPrepRun 100 200 5 4).cell a k == 7
#guard (List.range 5).map ((augPrepRun 100 200 5 4).cell "mem") = [1, 3, 5, 7, 9]
-- the two sources, unmoved
#guard (List.range 6).map ((augPrepRun 100 200 5 4).cell "ioff") = star5doff
#guard (List.range 4).map ((augPrepRun 100 200 5 4).cell "itg") = star5dtg

-- the scalar the obligation hands back, and the carrier it runs at
#guard (augPrepRun 100 200 5 4).scalar "mm" = 5
#guard (augPrepRun 100 200 5 4).scalar "n" = 5

-- **the honesty direction**
#guard ¬ ((List.range 6).all fun k => (augPrepRun 100 200 5 4).cell "doff" k == 7)

-- **the charge**, on data
#guard (augPrepClock 100 200 5 4).2 ≤ augPrepCost 5 4
-- **carrier-blind**
#guard (augPrepClock 800 200 5 4).2 = (augPrepClock 100 200 5 4).2
-- …and arena-affine
#guard (augPrepClock 100 200 5 4).2 < (augPrepClock 100 200 20 4).2

/-! ## §1 The shared invariant and the four pass shapes -/

/-- **The context every preparation pass runs in**: the two scalars its
bound reads and the two arrays it copies out of. A pass writes one array
— never a source — and only the kit's counter `"i"`, so the kit's frame
side condition is `prepQ_frame`, proved once. -/
def PrepQ (n W mm kd : ℕ) (IOg ITg : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "mm" = mm ∧ τ.vars "kd" = kd ∧
  τ.arrs "ioff" = arrOf (n + 1) IOg ∧ τ.arrs "itg" = arrOf W ITg

theorem prepQ_frame {n W mm kd : ℕ} {IOg ITg : ℕ → ℕ} {a : String}
    (h₁ : a ≠ "ioff") (h₂ : a ≠ "itg") :
    ∀ τ τ' : Env, PrepQ n W mm kd IOg ITg τ → (∀ y, y ≠ "i" → τ'.vars y = τ.vars y) →
      (∀ b, b ≠ a → τ'.arrs b = τ.arrs b) → PrepQ n W mm kd IOg ITg τ' := by
  rintro τ τ' ⟨hm, hk, hio, hit⟩ hv ha
  exact ⟨by rw [hv "mm" (by decide), hm], by rw [hv "kd" (by decide), hk],
    by rw [ha "ioff" (Ne.symm h₁), hio], by rw [ha "itg" (Ne.symm h₂), hit]⟩

/-! ### §1.1 The two bounds, evaluated -/

theorem evalB_mmAdd1 {B mm : ℕ} {τ : Env} (hmm : τ.vars "mm" = mm) (hB : mm + 1 < B) :
    (Expr.add (.var "mm") (.lit 1)).evalB B τ = some (mm + 1) := by
  have h := evalB_bin (op := .add) (B := B) (σ := τ)
    (evalB_var (x := "mm") (by rw [hmm]; omega)) (evalB_lit (B := B) (n := 1) (by omega))
    (by rw [Bop.apply_add, hmm]; omega)
  rwa [Bop.apply_add, hmm] at h

theorem evalB_scalar {B v : ℕ} {x : String} {τ : Env} (hx : τ.vars x = v) (hB : v < B) :
    (Expr.var x).evalB B τ = some v := by
  rw [← hx]; exact evalB_var (by rw [hx]; omega)

/-! ### §1.2 The frames of a single pass, off the syntax -/

theorem notMem_fill_warrs {a b : String} {bnd e : Expr} (h : b ≠ a) :
    b ∉ (fillUpto a bnd e).warrs := by
  simp [fillUpto, Fill.put, Com.warrs, h]

theorem notMem_copy_warrs {src dst b : String} {bnd : Expr} (h : b ≠ dst) :
    b ∉ (copyUpto src dst bnd).warrs := by
  simp [copyUpto, fillUpto, Fill.put, Com.warrs, h]

/-! ### §1.3 The four pass shapes

One wrapper per bound the two programs use, each already at its closed
cost. Every wrapper is `RamDriverOrder.copyKeep_spec`/`fillKeep_spec`
with `PrepQ` for the context — nothing is re-proved. -/

/-- **A prefix copy out of `"ioff"`**, `mm + 1` cells into a
carrier-length array, the tail kept. `14·mm + 22` ticks. -/
theorem copyIoff_spec (B n W mm kd Nd : ℕ) (IOg ITg : ℕ → ℕ) (dst : String)
    (h₁ : dst ≠ "ioff") (h₂ : dst ≠ "itg") (hB : mm + 1 < B) (hNd : mm + 1 ≤ Nd)
    (hmn : mm ≤ n) (hIOgB : ∀ k < mm + 1, IOg k < B) :
    Spec B (fun σ => (∃ g, σ.arrs dst = arrOf Nd g) ∧ PrepQ n W mm kd IOg ITg σ)
      (copyUpto "ioff" dst (.add (.var "mm") (.lit 1)))
      (fun σ σ' => (∃ h, σ'.arrs dst = arrOf Nd h ∧ (∀ k < mm + 1, h k = IOg k) ∧
          (∀ k, mm + 1 ≤ k → k < Nd → h k = (σ.arrs dst).getD k 0)) ∧
        σ'.vars "i" = mm + 1 ∧ PrepQ n W mm kd IOg ITg σ')
      (14 * mm + 22) :=
  (Lax3Proofs.RamDriverOrder.copyKeep_spec (B := B) (mm + 1) Nd (n + 1) "ioff" dst
    (.add (.var "mm") (.lit 1)) IOg (PrepQ n W mm kd IOg ITg) (by omega) hB hNd (by omega)
    (prepQ_frame h₁ h₂) (fun _ hQ => evalB_mmAdd1 hQ.1 hB) (fun _ hQ => hQ.2.2.1)
    hIOgB).mono (by simp only [size_add, size_var, size_lit]; omega)

/-- **A prefix copy out of `"itg"`**, `kd` cells into a width-length
array, the tail kept. `12·kd + 6` ticks. -/
theorem copyItg_spec (B n W mm kd Nd : ℕ) (IOg ITg : ℕ → ℕ) (dst : String)
    (h₁ : dst ≠ "ioff") (h₂ : dst ≠ "itg") (hB : kd < B) (hNd : kd ≤ Nd)
    (hkW : kd ≤ W) (hITgB : ∀ k < kd, ITg k < B) :
    Spec B (fun σ => (∃ g, σ.arrs dst = arrOf Nd g) ∧ PrepQ n W mm kd IOg ITg σ)
      (copyUpto "itg" dst (.var "kd"))
      (fun σ σ' => (∃ h, σ'.arrs dst = arrOf Nd h ∧ (∀ k < kd, h k = ITg k) ∧
          (∀ k, kd ≤ k → k < Nd → h k = (σ.arrs dst).getD k 0)) ∧
        σ'.vars "i" = kd ∧ PrepQ n W mm kd IOg ITg σ')
      (12 * kd + 6) :=
  (Lax3Proofs.RamDriverOrder.copyKeep_spec (B := B) kd Nd W "itg" dst (.var "kd") ITg
    (PrepQ n W mm kd IOg ITg) (by omega) hB hNd hkW (prepQ_frame h₁ h₂)
    (fun _ hQ => evalB_scalar hQ.2.1 hB) (fun _ hQ => hQ.2.2.2) hITgB).mono
    (by simp only [size_var]; omega)

/-- **A zero fill over `[0, mm + 1)`** of a carrier-length array, the tail
kept. `13·mm + 21` ticks. -/
theorem zeroM1_spec (B n W mm kd Nd : ℕ) (IOg ITg : ℕ → ℕ) (a : String)
    (h₁ : a ≠ "ioff") (h₂ : a ≠ "itg") (hB : mm + 1 < B) (hNd : mm + 1 ≤ Nd) :
    Spec B (fun σ => (∃ g, σ.arrs a = arrOf Nd g) ∧ PrepQ n W mm kd IOg ITg σ)
      (fillUpto a (.add (.var "mm") (.lit 1)) (.lit 0))
      (fun σ σ' => (∃ h, σ'.arrs a = arrOf Nd h ∧ (∀ k < mm + 1, h k = 0) ∧
          (∀ k, mm + 1 ≤ k → k < Nd → h k = (σ.arrs a).getD k 0)) ∧
        σ'.vars "i" = mm + 1 ∧ PrepQ n W mm kd IOg ITg σ')
      (13 * mm + 21) :=
  (Lax3Proofs.RamDriverOrder.fillKeep_spec (B := B) (mm + 1) Nd a
    (.add (.var "mm") (.lit 1)) (.lit 0) (fun _ => 0) (PrepQ n W mm kd IOg ITg)
    (by omega) hB hNd (prepQ_frame h₁ h₂) (fun _ hQ => evalB_mmAdd1 hQ.1 hB)
    (fun _ _ _ => evalB_lit (by omega))).mono
    (by simp only [size_add, size_var, size_lit]; omega)

/-- **A zero fill over `[0, mm)`** of a carrier-length array, the tail
kept. `11·mm + 6` ticks. -/
theorem zeroM_spec (B n W mm kd Nd : ℕ) (IOg ITg : ℕ → ℕ) (a : String)
    (h₁ : a ≠ "ioff") (h₂ : a ≠ "itg") (hB : mm + 1 < B) (hNd : mm ≤ Nd) :
    Spec B (fun σ => (∃ g, σ.arrs a = arrOf Nd g) ∧ PrepQ n W mm kd IOg ITg σ)
      (fillUpto a (.var "mm") (.lit 0))
      (fun σ σ' => (∃ h, σ'.arrs a = arrOf Nd h ∧ (∀ k < mm, h k = 0) ∧
          (∀ k, mm ≤ k → k < Nd → h k = (σ.arrs a).getD k 0)) ∧
        σ'.vars "i" = mm ∧ PrepQ n W mm kd IOg ITg σ')
      (11 * mm + 6) :=
  (Lax3Proofs.RamDriverOrder.fillKeep_spec (B := B) mm Nd a (.var "mm") (.lit 0)
    (fun _ => 0) (PrepQ n W mm kd IOg ITg) (by omega) (by omega) hNd (prepQ_frame h₁ h₂)
    (fun _ hQ => evalB_scalar hQ.1 (by omega)) (fun _ _ _ => evalB_lit (by omega))).mono
    (by simp only [size_var, size_lit]; omega)

/-! ## §2 `SymCompact.SymPreps`, discharged

Three passes, at `27·mm + 12·kd + 49` ticks. -/

theorem symPreps (B n mm nt W kd : ℕ) : SymPreps B n mm nt W kd := by
  classical
  intro IO IT T₀ σ hmB hkB hIOB hITB hent
  obtain ⟨hn, hmm, hkd, hmn, hkW, ⟨IOg, hioff, hIOg⟩, ⟨ITg, hitg, hITg⟩, ⟨d₀, hd₀⟩,
    ⟨t₀, ht₀⟩, ⟨o₀, ho₀⟩, ⟨fl₀, hfl₀⟩, ⟨ot₀, hot₀⟩, ⟨of₀, hof₀⟩, htgt⟩ := hent
  have hQ₀ : PrepQ n W mm kd IOg ITg σ := ⟨hmm, hkd, hioff, hitg⟩
  have hIOgB : ∀ k < mm + 1, IOg k < B := fun k hk => by
    rw [hIOg k (by omega)]; exact hIOB k (by omega)
  have hITgB : ∀ k < kd, ITg k < B := fun k hk => by rw [hITg k hk]; exact hITB k hk
  -- **the compact offsets**, into the pass's input array
  obtain ⟨τ₁, r₁, ⟨D₁, hD₁, hD₁lo, -⟩, -, hQ₁⟩ :=
    copyIoff_spec B n W mm kd (n + 1) IOg ITg "doff" (by decide) (by decide) hmB
      (by omega) hmn hIOgB σ ⟨⟨d₀, hd₀⟩, hQ₀⟩
  -- **the compact targets**, over the compact slot count and no further
  obtain ⟨τ₂, r₂, ⟨D₂, hD₂, hD₂lo, -⟩, -, hQ₂⟩ :=
    copyItg_spec B n W mm kd W IOg ITg "dtg" (by decide) (by decide) hkB hkW hkW hITgB
      τ₁ ⟨⟨t₀, by rw [r₁.frame_arr "dtg" (notMem_copy_warrs (by decide)), ht₀]⟩, hQ₁⟩
  -- **the counting sort's accumulator**, zeroed over the compact prefix
  obtain ⟨τ₃, r₃, ⟨O₃, hO₃, hO₃lo, -⟩, -, hQ₃⟩ :=
    zeroM1_spec B n W mm kd (n + 1) IOg ITg "ooff" (by decide) (by decide) hmB (by omega)
      τ₂ ⟨⟨o₀, by rw [((r₁.seq r₂).frame_arr "ooff"
        (by simp [copyUpto, fillUpto, Fill.put, Com.warrs])), ho₀]⟩, hQ₂⟩
  -- the composite, and its frame
  have rAll : Run B symPrepCom σ τ₃ (14 * mm + 22 + (12 * kd + 6) + (13 * mm + 21)) :=
    (r₁.seq r₂).seq r₃
  have fA : ∀ a : String, a ≠ "doff" → a ≠ "dtg" → a ≠ "ooff" → τ₃.arrs a = σ.arrs a :=
    fun a h₁ h₂ h₃ => rAll.frame_arr a (notMem_symPrepCom_warrs h₁ h₂ h₃)
  have hdoff₃ : τ₃.arrs "doff" = τ₁.arrs "doff" :=
    (r₂.seq r₃).frame_arr "doff" (by simp [copyUpto, fillUpto, Fill.put, Com.warrs])
  have hdtg₃ : τ₃.arrs "dtg" = τ₂.arrs "dtg" :=
    r₃.frame_arr "dtg" (notMem_fill_warrs (by decide))
  refine ⟨τ₃, D₂, rAll.mono (by rw [symPrepCost]; omega), ?_, hQ₃.1, ?_,
    fun j hj => by rw [hD₂lo j hj, hITg j hj], ⟨D₁, ?_, ?_⟩, ⟨O₃, hO₃, ?_⟩,
    ⟨fl₀, ?_⟩, ⟨ot₀, ?_⟩, ⟨of₀, ?_⟩, ?_⟩
  · rw [rAll.frame_var "n" (notMem_symPrepCom_wvars (by decide)), hn]
  · rw [hdtg₃, hD₂]
  · rw [hdoff₃, hD₁]
  · exact fun i hi => by rw [hD₁lo i (by omega), hIOg i hi]
  · exact fun i hi => hO₃lo i (by omega)
  · rw [fA "ofl" (by decide) (by decide) (by decide), hfl₀]
  · rw [fA "otg" (by decide) (by decide) (by decide), hot₀]
  · rw [fA "off" (by decide) (by decide) (by decide), hof₀]
  · rw [fA "tgt" (by decide) (by decide) (by decide), htgt]

/-! ## §3 `AugCompact.AugPreps`, discharged

Eleven passes, at `121·mm + 12·kd + 142` ticks: the two relinks, the four
`mm+1`-bounded zeroes (`ooff`, `off`, `noff`, `bh`) and the five
`mm`-bounded ones (`elm` and the four stamps). -/

theorem augPreps (B n mm nt W kd : ℕ) : AugPreps B n mm nt W kd := by
  classical
  intro IO IT σ hmB hkB hIOB hITB hn hmm hkd hmn hkW hent
  obtain ⟨⟨IOg, hioff, hIOg⟩, ⟨ITg, hitg, hITg⟩, ⟨d₀, hd₀⟩, ⟨t₀, ht₀⟩, ⟨oo₀, hoo₀⟩,
    ⟨ot₀, hot₀⟩, ⟨fl₀, hfl₀⟩, ⟨of₀, hof₀⟩, ⟨tg₀, htg₀⟩, ⟨ff₀, hff₀⟩, ⟨al₀, hal₀⟩,
    ⟨dg₀, hdg₀⟩, ⟨el₀, hel₀⟩, ⟨rk₀, hrk₀⟩, ⟨ig₀, hig₀⟩, ⟨bh₀, hbh₀⟩, ⟨bv₀, hbv₀⟩,
    ⟨bn₀, hbn₀⟩, ⟨if₀, hif₀⟩, ⟨no₀, hno₀⟩, ⟨nf₀, hnf₀⟩, ⟨nt₀, hnt₀⟩, ⟨sf₀, hsf₀⟩,
    ⟨sa₀, hsa₀⟩, ⟨sd₀, hsd₀⟩, ⟨se₀, hse₀⟩, ⟨ok₀, hok₀⟩⟩ := hent
  have hQ₀ : PrepQ n W mm kd IOg ITg σ := ⟨hmm, hkd, hioff, hitg⟩
  have hIOgB : ∀ k < mm + 1, IOg k < B := fun k hk => by
    rw [hIOg k (by omega)]; exact hIOB k (by omega)
  have hITgB : ∀ k < kd, ITg k < B := fun k hk => by rw [hITg k hk]; exact hITB k hk
  -- **the two relinks**
  obtain ⟨τ₁, r₁, ⟨D₁, hD₁, hD₁lo, -⟩, -, hQ₁⟩ :=
    copyIoff_spec B n W mm kd (n + 1) IOg ITg "doff" (by decide) (by decide) hmB
      (by omega) hmn hIOgB σ ⟨⟨d₀, hd₀⟩, hQ₀⟩
  obtain ⟨τ₂, r₂, ⟨D₂, hD₂, hD₂lo, -⟩, -, hQ₂⟩ :=
    copyItg_spec B n W mm kd W IOg ITg "dtg" (by decide) (by decide) hkB hkW hkW hITgB
      τ₁ ⟨⟨t₀, by rw [r₁.frame_arr "dtg" (notMem_copy_warrs (by decide)), ht₀]⟩, hQ₁⟩
  -- the prefix runs, so that each precondition is one rewrite
  have p₂ := r₁.seq r₂
  -- **the four `mm+1`-bounded zeroes**
  obtain ⟨τ₃, r₃, ⟨Z₃, hZ₃, hZ₃lo, -⟩, -, hQ₃⟩ :=
    zeroM1_spec B n W mm kd (n + 1) IOg ITg "ooff" (by decide) (by decide) hmB (by omega)
      τ₂ ⟨⟨oo₀, by rw [p₂.frame_arr "ooff"
        (by simp [copyUpto, fillUpto, Fill.put, Com.warrs]), hoo₀]⟩, hQ₂⟩
  have p₃ := p₂.seq r₃
  obtain ⟨τ₄, r₄, ⟨Z₄, hZ₄, hZ₄lo, -⟩, -, hQ₄⟩ :=
    zeroM1_spec B n W mm kd (n + 1) IOg ITg "off" (by decide) (by decide) hmB (by omega)
      τ₃ ⟨⟨of₀, by rw [p₃.frame_arr "off"
        (by simp [copyUpto, fillUpto, Fill.put, Com.warrs]), hof₀]⟩, hQ₃⟩
  have p₄ := p₃.seq r₄
  obtain ⟨τ₅, r₅, ⟨Z₅, hZ₅, hZ₅lo, -⟩, -, hQ₅⟩ :=
    zeroM1_spec B n W mm kd (n + 1) IOg ITg "noff" (by decide) (by decide) hmB (by omega)
      τ₄ ⟨⟨no₀, by rw [p₄.frame_arr "noff"
        (by simp [copyUpto, fillUpto, Fill.put, Com.warrs]), hno₀]⟩, hQ₄⟩
  have p₅ := p₄.seq r₅
  obtain ⟨τ₆, r₆, ⟨Z₆, hZ₆, hZ₆lo, -⟩, -, hQ₆⟩ :=
    zeroM1_spec B n W mm kd (n + 1) IOg ITg "bh" (by decide) (by decide) hmB (by omega)
      τ₅ ⟨⟨bh₀, by rw [p₅.frame_arr "bh"
        (by simp [copyUpto, fillUpto, Fill.put, Com.warrs]), hbh₀]⟩, hQ₅⟩
  have p₆ := p₅.seq r₆
  -- **the five `mm`-bounded zeroes**
  obtain ⟨τ₇, r₇, ⟨Z₇, hZ₇, hZ₇lo, -⟩, -, hQ₇⟩ :=
    zeroM_spec B n W mm kd n IOg ITg "elm" (by decide) (by decide) hmB hmn
      τ₆ ⟨⟨el₀, by rw [p₆.frame_arr "elm"
        (by simp [copyUpto, fillUpto, Fill.put, Com.warrs]), hel₀]⟩, hQ₆⟩
  have p₇ := p₆.seq r₇
  obtain ⟨τ₈, r₈, ⟨Z₈, hZ₈, hZ₈lo, -⟩, -, hQ₈⟩ :=
    zeroM_spec B n W mm kd n IOg ITg "stf" (by decide) (by decide) hmB hmn
      τ₇ ⟨⟨sf₀, by rw [p₇.frame_arr "stf"
        (by simp [copyUpto, fillUpto, Fill.put, Com.warrs]), hsf₀]⟩, hQ₇⟩
  have p₈ := p₇.seq r₈
  obtain ⟨τ₉, r₉, ⟨Z₉, hZ₉, hZ₉lo, -⟩, -, hQ₉⟩ :=
    zeroM_spec B n W mm kd n IOg ITg "sta" (by decide) (by decide) hmB hmn
      τ₈ ⟨⟨sa₀, by rw [p₈.frame_arr "sta"
        (by simp [copyUpto, fillUpto, Fill.put, Com.warrs]), hsa₀]⟩, hQ₈⟩
  have p₉ := p₈.seq r₉
  obtain ⟨τ₁₀, r₁₀, ⟨Z₁₀, hZ₁₀, hZ₁₀lo, -⟩, -, hQ₁₀⟩ :=
    zeroM_spec B n W mm kd n IOg ITg "std" (by decide) (by decide) hmB hmn
      τ₉ ⟨⟨sd₀, by rw [p₉.frame_arr "std"
        (by simp [copyUpto, fillUpto, Fill.put, Com.warrs]), hsd₀]⟩, hQ₉⟩
  have p₁₀ := p₉.seq r₁₀
  obtain ⟨τ₁₁, r₁₁, ⟨Z₁₁, hZ₁₁, hZ₁₁lo, -⟩, -, hQ₁₁⟩ :=
    zeroM_spec B n W mm kd n IOg ITg "ste" (by decide) (by decide) hmB hmn
      τ₁₀ ⟨⟨se₀, by rw [p₁₀.frame_arr "ste"
        (by simp [copyUpto, fillUpto, Fill.put, Com.warrs]), hse₀]⟩, hQ₁₀⟩
  -- the suffix runs, so that each destination survives in one rewrite
  have t₁₀ := r₁₁
  have t₉ := r₁₀.seq t₁₀
  have t₈ := r₉.seq t₉
  have t₇ := r₈.seq t₈
  have t₆ := r₇.seq t₇
  have t₅ := r₆.seq t₆
  have t₄ := r₅.seq t₅
  have t₃ := r₄.seq t₄
  have t₂ := r₃.seq t₃
  have t₁ := r₂.seq t₂
  have rAll : Run B augPrepCom σ τ₁₁
      (14 * mm + 22 + (12 * kd + 6) +
        (13 * mm + 21 + (13 * mm + 21 + (13 * mm + 21 + (13 * mm + 21 +
          (11 * mm + 6 + (11 * mm + 6 + (11 * mm + 6 + (11 * mm + 6 + (11 * mm + 6)))))))))) :=
    (r₁.seq r₂).seq t₂
  have fA : ∀ a : String, a ≠ "doff" → a ≠ "dtg" → a ≠ "ooff" → a ≠ "off" → a ≠ "noff" →
      a ≠ "bh" → a ≠ "elm" → a ≠ "stf" → a ≠ "sta" → a ≠ "std" → a ≠ "ste" →
      τ₁₁.arrs a = σ.arrs a :=
    fun a h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ =>
      rAll.frame_arr a (notMem_augPrepCom_warrs h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀)
  have hdoff : τ₁₁.arrs "doff" = τ₁.arrs "doff" :=
    t₁.frame_arr "doff" (by simp [copyUpto, fillUpto, Fill.put, Com.warrs])
  have hdtg : τ₁₁.arrs "dtg" = τ₂.arrs "dtg" :=
    t₂.frame_arr "dtg" (by simp [fillUpto, Fill.put, Com.warrs])
  have hooff : τ₁₁.arrs "ooff" = τ₃.arrs "ooff" :=
    t₃.frame_arr "ooff" (by simp [fillUpto, Fill.put, Com.warrs])
  have hoff : τ₁₁.arrs "off" = τ₄.arrs "off" :=
    t₄.frame_arr "off" (by simp [fillUpto, Fill.put, Com.warrs])
  have hnoff : τ₁₁.arrs "noff" = τ₅.arrs "noff" :=
    t₅.frame_arr "noff" (by simp [fillUpto, Fill.put, Com.warrs])
  have hbh : τ₁₁.arrs "bh" = τ₆.arrs "bh" :=
    t₆.frame_arr "bh" (by simp [fillUpto, Fill.put, Com.warrs])
  have helm : τ₁₁.arrs "elm" = τ₇.arrs "elm" :=
    t₇.frame_arr "elm" (by simp [fillUpto, Fill.put, Com.warrs])
  have hstf : τ₁₁.arrs "stf" = τ₈.arrs "stf" :=
    t₈.frame_arr "stf" (by simp [fillUpto, Fill.put, Com.warrs])
  have hsta : τ₁₁.arrs "sta" = τ₉.arrs "sta" :=
    t₉.frame_arr "sta" (by simp [fillUpto, Fill.put, Com.warrs])
  have hstd : τ₁₁.arrs "std" = τ₁₀.arrs "std" :=
    t₁₀.frame_arr "std" (notMem_fill_warrs (by decide))
  refine ⟨τ₁₁, D₂, rAll.mono (by rw [augPrepCost]; omega), hQ₁₁.1,
    fun j hj => by rw [hD₂lo j hj, hITg j hj],
    ⟨?_, hmn, ⟨D₁, ?_, ?_⟩, ?_, ⟨Z₃, ?_, ?_⟩, ⟨ot₀, ?_⟩, ⟨fl₀, ?_⟩, ⟨Z₄, ?_, ?_⟩,
      ⟨tg₀, ?_⟩, ⟨ff₀, ?_⟩, ⟨al₀, ?_⟩, ⟨dg₀, ?_⟩, ⟨Z₇, ?_, ?_⟩, ⟨rk₀, ?_⟩, ⟨ig₀, ?_⟩,
      ⟨Z₆, ?_, ?_⟩, ⟨bv₀, ?_⟩, ⟨bn₀, ?_⟩, ⟨IOg, ?_⟩, ⟨if₀, ?_⟩, ⟨ITg, ?_⟩, ⟨Z₅, ?_, ?_⟩,
      ⟨nf₀, ?_⟩, ⟨nt₀, ?_⟩, ⟨Z₈, ?_, ?_⟩, ⟨Z₉, ?_, ?_⟩, ⟨Z₁₀, ?_, ?_⟩, ⟨Z₁₁, ?_, ?_⟩⟩,
    ?_, ⟨ok₀, ?_⟩⟩
  · rw [rAll.frame_var "n" (notMem_augPrepCom_wvars (by decide)), hn]
  · rw [hdoff, hD₁]
  · exact fun i hi => by rw [hD₁lo i (by omega), hIOg i hi]
  · rw [hdtg, hD₂]
  · rw [hooff, hZ₃]
  · exact fun i hi => hZ₃lo i (by omega)
  · rw [fA "otg" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hot₀]
  · rw [fA "ofl" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hfl₀]
  · rw [hoff, hZ₄]
  · exact fun i hi => hZ₄lo i (by omega)
  · rw [fA "tgt" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), htg₀]
  · rw [fA "ffl" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hff₀]
  · rw [fA "alv" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hal₀]
  · rw [fA "deg" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hdg₀]
  · rw [helm, hZ₇]
  · exact fun i hi => hZ₇lo i hi
  · rw [fA "rnk" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hrk₀]
  · rw [fA "idg" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hig₀]
  · rw [hbh, hZ₆]
  · exact fun i hi => hZ₆lo i (by omega)
  · rw [fA "bv" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hbv₀]
  · rw [fA "bn" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hbn₀]
  · exact hQ₁₁.2.2.1
  · rw [fA "ifl" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hif₀]
  · exact hQ₁₁.2.2.2
  · rw [hnoff, hZ₅]
  · exact fun i hi => hZ₅lo i (by omega)
  · rw [fA "nfl" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hnf₀]
  · rw [fA "ntg" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hnt₀]
  · rw [hstf, hZ₈]
  · exact fun i hi => hZ₈lo i hi
  · rw [hsta, hZ₉]
  · exact fun i hi => hZ₉lo i hi
  · rw [hstd, hZ₁₀]
  · exact fun i hi => hZ₁₀lo i hi
  · exact hZ₁₁
  · exact fun i hi => hZ₁₁lo i hi
  · exact fA "mem" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [fA "ork" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hok₀]

/-! ## §4 What the two theorems rest on

Neither takes an antecedent beyond the ones its obligation already
quantifies — in particular no extra word bound had to be added, because
the four the parents state (`mm + 1 < B`, `kd < B`, and the two on the
in-lists, which `SymCompact.prep_bounds_of_inCsr` supplies from the block
structure at `kd = m`) are exactly the ones a copy needs and the fills
need none. So `SymCompact.symCompact_spec` now stands on walks alone, and
`AugCompact.augCompact_spec` on `ElimCompact.ScatterBacks` alone. -/

#print axioms symPreps
#print axioms augPreps

end Lax3Proofs.Refine.CompactPreps
