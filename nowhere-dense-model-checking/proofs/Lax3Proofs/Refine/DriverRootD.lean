import Lax3Proofs.RamDriverRoot
import Lax3Proofs.RamDriverDedup
import Lax3Proofs.Refine.BridgeSeamProbe
import Lax3Proofs.Refine.SlotSweep

/-!
**The root, restated at the composed dedup'd decode** — ND-MC rebase,
B7 re-run leaf S2/S3.

The slot sweep (`Refine.SlotSweep`) left the landed root with six
blocking slots in three groups. This file kills the first two groups at
a *restated* root — `driverRootD`, whose decode phase is the composed
`decodeCom ; lwCom ; dedupCom` — and leaves the cost group
(#20/#22/#23/#27) exactly where the landed root has it: the restated
root keeps the landed cost hypothesis shapes, read at the compacted
slot count.

* **S2, the `"lw"` repair (finding 4).** `BridgeSeamProbe` §2–§4 proved
  the landed root's precondition `initEnv`-satisfiable iff the input
  word has no edges: `RamDriver.OrderMem`'s live-width clause reads
  `ns ≤ 0` at a fresh environment, no driver pass assigns `"lw"`, and a
  prologue cannot compute the value without consuming the tape
  (`read_breaks_inp`). The repair witness was landed there
  (`lwCom`/`lwCom_spec`, one assignment, cost `4`); what was missing is
  the phase that carries it. `decodeComD` splices `lwCom` between the
  decode and the dedup guard — right after `.read "m"`, where the slot
  count is live — and `DecodeImplementsDL` is the composed obligation
  whose *pre*condition asks `OrderMem B n 0 W` (satisfiable at
  `initEnv`) and whose *post*condition delivers
  `OrderMem B n (dedupNs x) W`. The anti-witness
  (`restated_pre_initEnv_where_landed_is_not`) is the exact converse of
  `rootPre_initEnv_iff_ns_zero`: at an edgeful word the restated
  precondition holds at a fresh environment while the landed one holds
  at none.

  **One consequence of the weakened entry, recorded.** The landed
  decode Specs (`RamDriverIO.decodeImplements`,
  `RamDriverDedup.decodeImplementsD`) demand `OrderMem B n ns W` —
  hence `ns ≤ lw` — *before* the decode, so neither can be entered from
  the repaired precondition at all: the brief's route
  "`decodeImplementsD` composed with `lwCom_spec`" does not typecheck
  at `lw = 0`. The decode walk is therefore replayed here once
  (`decode_spec_lw0`) with the live-width clause at `0` on both sides —
  the walk never reads `"lw"`, so the proof is the landed one with the
  index weakened; nothing else moves.

* **S3a, `driverRootD`.** `driverRootD_decides_sentence` (at `R = 0`)
  and `driverRootD_decides_sentenceR` (general `R`) restate
  `RamDriverRoot.driverRoot_decides_sentence` at the composed decode.
  The root's data triple becomes `dedupNs x / dedupOffset x /
  dedupTarget x`; **`hcsr` disappears** — its producer is
  `RamDriverDedup.csrSimple_dedup` (slot #6's kill, `slot06_dead_at_D`);
  `hO`/`hT`/`hpad0` die with it (the compacted triple is definitionally
  the data the phase leaves, and its tail is `dedupTarget_eq_zero`);
  `hKdec` covers `decodeCost n ns + dedupCost n ns + 4`; `ns ≤ W`
  becomes the explicit hypothesis `hnsW`, because the landed root read
  it off the precondition's `OrderMem ns` clause and the restated
  precondition carries `OrderMem 0`. Every other slot is byte-identical
  to the landed root's, read at the compacted count.

* **S3b, `levelAtR`.** The level assembly restated at general `R` with
  the ordering slot carrying the phase's degree export, so the root's
  every-permutation `hdeg` — the slot `SlotSweep` §C refutes at the
  stars — is **gone**.

  **A type-level finding first**: the brief's slot value
  `P := RamDriverCompose.OrderP R G M` cannot inhabit the frozen
  interface. `RamDriverCluster.levelImplements` binds `P` *before* the
  mask and reads `P π ord` at every `M`; `OrderP` names the mask. The
  admissible value is the mask-uniform degree bound
  `DegOrder n G cap Kmass` — the `R = R*` value
  `RamDriver.OrderImplements`' own docstring promises — which implies
  the per-arena bound at every mask (`wreach_masked_subset`, what
  `hmass` consumes) and which the per-π producer
  (`exists_wreachDeg_of_orderP`, at `OrderP`) closes at the all-alive
  root arena (`degOrder_of_orderP_alive`). Three named residuals are
  hypotheses, none dischargeable from today's capital at `R > 0`:

  * `horder`, the phase walk at the `DegOrder` slot value — the
    residual `RamDriverRoot`'s own `hdeg` section names, at the shape
    the frozen slot admits. **The landed `R`-round walk cannot feed
    even the per-obligation shape** (`no_guard_instance`): the E2b walk
    discharges `OrderImplementsRL`, whose precondition carries
    `chainWidthE … ≤ σ.vars "lw"`, and the slot holds only `LevelPre`,
    whose `OrderMem` pins no more than `ns ≤ lw` — while
    `chainWidthE > ns` always (`ns_lt_chainWidthE`). The `.pre` bridge
    is compiled anyway (`orderSlot_of_RL`) so the gap is a theorem and
    not prose: closing it means threading the width guard through
    `LevelPre` (or re-walking the phase), a landed-file wave this leaf
    does not own.
  * `hfr : RFrames …`, the nested driver's write-set facts at round
    `R` — `Lax3Proofs.RamDriverWrites` proves them at `R = 0` only
    (`rFrames_zero` is that plug), and the general-`R` write-set
    recursion is its own mechanical wave.
  * `hptr`/`hexit`, the arena-pointer word readings, in the frozen
    slots' own every-ordering shape: `levelAt` discharges them from
    the *unconditional* `hdeg`, and the conditional form cannot reach
    them, because `RamDriverCluster.levelImplements` hands the slots
    `RamCover.OrdersBy` alone — the `P π ord` witness is in scope at
    their one use site but not passed. F-c-3 threaded `P` into `hmass`
    and not into W2's pointer slots; carrying it there is a one-line
    landed-file change this leaf does not own.

* **The compiled kills** (§6): `slot06_dead_at_D` (#6),
  `slot26_dead_at_R` with its control `not_orderP_starLast_id` (#26),
  `slot12_hB_nondegenerate` (#12), and
  `restated_pre_initEnv_where_landed_is_not` (finding 4). The landed
  sweep theorems (`slot06_hcsr_blocked`, `slot26_hdeg_blocked`,
  `wordBound_of_deg_slot`, `rootPre_initEnv_iff_ns_zero`) are untouched
  and remain true of the landed root.
-/

namespace Lax3Proofs.Refine.DriverRootD

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax11.GraphEncoding
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked CsrGraph csrGraph_of_encodesGraph)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverDedup (dedupCom dedupNs dedupOffset dedupTarget dedupCost DedupMem
  padTarget)
open Lax3Proofs.RamDriverIO (decodeCost readLoop_spec readLoop_specW fill_spec
  wvars_readLoop warrs_readLoop noWrite_readLoop wvars_fillCom warrs_fillCom noWrite_fillCom
  getD_take getD_drop getD_cons_cons)
open Lax3Proofs.Refine.BridgeSeamProbe (lwCom lwCom_spec extOf RootPre)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## §0 Two small readings of landed facts -/

/-- `RamDriver.WordBoundK` only ever *adds* the slot count, so a smaller
slot count weakens it — the compacted triple inherits the input word's
value bound. -/
theorem wordBoundK_anti {B n K ns' ns cap mb : ℕ} (h : ns' ≤ ns)
    (hB : WordBoundK B n K ns cap mb) : WordBoundK B n K ns' cap mb := by
  obtain ⟨h1, h2⟩ := hB
  exact ⟨by omega, h2⟩

/-- `RamDriver.DecodeMem`'s only slot-count clause is the zero tail, and
a tail zero from `0` is zero from anywhere. -/
theorem decodeMem_of_zero {n ns W : ℕ} {σ : Env} (h : DecodeMem n 0 W σ) :
    DecodeMem n ns W σ :=
  ⟨h.1, h.2.1, fun j _ hj => h.2.2.1 j (Nat.zero_le j) hj, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2⟩

/-! ## §1 The decode at the free live width

`RamDriverIO.decodeImplements` — and with it
`RamDriverDedup.decodeImplementsD` — carries `RamDriver.OrderMem B n ns W`
in its *pre*condition, whose live-width clause `ns ≤ σ.vars "lw"` is
exactly what `BridgeSeamProbe` proved unreachable from `initEnv`. The
walk itself never reads the scalar: the landed proof consumes the clause
only to hand it back across the run's frame. `decode_spec_lw0` is that
walk with the clause weakened to the satisfiable index `0` on both
sides. It is the landed proof of `decodeImplements`, instantiated at
`O := offset x`, `T := padTarget x ns`, with the live-width index
dropped to `0` — no step is new. -/

set_option maxHeartbeats 1000000 in
/-- **The decode, entered at `OrderMem B n 0 W`.** -/
theorem decode_spec_lw0 {B n ns W : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hxB : ∀ v ∈ x, v < B) (hnB : n + 1 < B) (hnsB : ns < B) (_hWB : W < B) (hnsW : ns ≤ W) :
    Spec B (fun σ => DecodeMem n ns W σ ∧ OrderMem B n 0 W σ ∧ σ.inp = x ∧ σ.out = [])
      RamDriver.decodeCom
      (fun _ σ' => σ'.out = [] ∧ CsrGraph G ns (offset x) (padTarget x ns) ∧
        σ'.vars "n" = n ∧ σ'.arrs "off" = arrOf (n + 1) (offset x) ∧
        σ'.arrs "tgt" = arrOf W (padTarget x ns) ∧
        σ'.vars "m" = edgeCount x ∧ OrderMem B n 0 W σ' ∧
        (∃ M, σ'.arrs (alvName 0) = arrOf n M ∧ ∀ v < n, M v = 1) ∧
        (∃ Gm, σ'.arrs (gamName 0) = arrOf n Gm ∧ ∀ v < n, Gm v = 1) ∧
        (∃ Mem, σ'.arrs (memName 0) = arrOf n Mem ∧ (∀ v < n, Mem v = v) ∧
          σ'.vars (mnumName 0) = n))
      (decodeCost n ns) := by
  subst hns
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hoffL, htgtL, htgtZ, halvL, hgamL, hmemL⟩,
    ⟨hOle, hOlw, hOsz, hz₁, hz₂, hz₃, hz₄, hz₅, hz₆, hz₇, hz₈, hw₁, hw₂⟩,
    hinp, hout⟩ := hσ
  -- the word: the two header entries, the offsets, the targets
  have hlen := hx.length_eq
  obtain ⟨rest, hxr⟩ : ∃ rest, x = n :: edgeCount x :: rest := by
    rcases x with _ | ⟨p, _ | ⟨q, rest⟩⟩
    · exact absurd hlen (by simp; omega)
    · exact absurd hlen (by simp; omega)
    · have hp : p = n := by
        have h := hx.vertexCount_eq
        rwa [Lax3Proofs.RamDriverIO.vertexCount_eq, List.getD_cons_zero] at h
      have hq : edgeCount (p :: q :: rest) = q := by
        rw [Lax3Proofs.RamDriverIO.edgeCount_eq, List.getD_cons_succ, List.getD_cons_zero]
      exact ⟨rest, by rw [hq, hp]⟩
  have hxlen : x.length = rest.length + 2 := by rw [hxr]; simp
  have hrest : rest.length = 1 + n + 2 * edgeCount x := by omega
  have hmemx : ∀ v ∈ rest, v < B := fun v hv =>
    hxB v (by rw [hxr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv))
  have hecB : edgeCount x < B :=
    hxB _ (by rw [hxr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
  obtain ⟨ys, zs, hys, hzs, hsplit, hyd, hzd⟩ :
      ∃ ys zs, ys.length = n + 1 ∧ zs.length = 2 * edgeCount x ∧ rest = ys ++ zs ∧
        (∀ i < n + 1, ys.getD i 0 = offset x i) ∧
        (∀ j < 2 * edgeCount x, zs.getD j 0 = target x j) := by
    refine ⟨rest.take (n + 1), rest.drop (n + 1), by simp; omega, by simp; omega,
      (List.take_append_drop _ _).symm, fun i hi => ?_, fun j _ => ?_⟩
    · rw [getD_take hi, Lax3Proofs.RamDriverIO.offset_eq, hxr, getD_cons_cons]
    · rw [getD_drop, Lax3Proofs.RamDriverIO.target_eq, hx.vertexCount_eq, hxr,
        show 3 + n + j = 2 + (n + 1 + j) by omega, getD_cons_cons]
  have hysB : ∀ v ∈ ys, v < B :=
    fun v hv => hmemx v (by rw [hsplit]; exact List.mem_append_left _ hv)
  have hzsB : ∀ v ∈ zs, v < B :=
    fun v hv => hmemx v (by rw [hsplit]; exact List.mem_append_right _ hv)
  -- the two counts
  obtain ⟨σ₁, hσ₁⟩ : ∃ τ : Env, τ = { σ.setVar "n" n with inp := edgeCount x :: rest } :=
    ⟨_, rfl⟩
  have r₁ : Run B (.read "n") σ σ₁ 1 := hσ₁ ▸ Run.read (by rw [hinp]; exact hxr)
  obtain ⟨σ₂, hσ₂⟩ : ∃ τ : Env, τ = { σ₁.setVar "m" (edgeCount x) with inp := rest } :=
    ⟨_, rfl⟩
  have r₂ : Run B (.read "m") σ₁ σ₂ 1 := hσ₂ ▸ Run.read (by simp [hσ₁])
  have hn₂ : σ₂.vars "n" = n := by simp [hσ₂, hσ₁]
  have hm₂ : σ₂.vars "m" = edgeCount x := by simp [hσ₂]
  have ha₂ : σ₂.arrs = σ.arrs := by simp [hσ₂, hσ₁]
  have hi₂ : σ₂.inp = rest := by simp [hσ₂]
  have ho₂ : σ₂.out = [] := by simp [hσ₂, hσ₁, hout]
  -- the offsets
  obtain ⟨σ₃, hσ₃⟩ : ∃ τ : Env, τ = σ₂.setVar "len" (n + 1) := ⟨_, rfl⟩
  have r₃ : Run B (.assign "len" (.add (.var "n") (.lit 1))) σ₂ σ₃ 4 :=
    hσ₃ ▸ (Run.assign (v := n + 1) (by
      rw [evalB_bin (evalB_var (by rw [hn₂]; omega)) (evalB_lit (by omega))
        (by simp only [Bop.apply_add]; rw [hn₂]; omega)]
      simp only [Bop.apply_add]; rw [hn₂])).mono (by norm_num)
  obtain ⟨σ₄, r₄, ⟨O', hoff₄, hO₄⟩, hinp₄⟩ :=
    (readLoop_spec (a := "off") (lim := "len") (ys := ys) (rest := zs) (by decide) (by decide)
      hys (by omega) hysB).run (σ := σ₃)
      ⟨by simpa [hσ₃, ha₂] using hoffL, by simp [hσ₃],
        by simp [hσ₃, hi₂, hsplit]⟩
  have hfv₄ : ∀ y, y ≠ "i" → y ≠ "t" → σ₄.vars y = σ₃.vars y := fun y h1 h2 =>
    r₄.frame_var y (by rw [wvars_readLoop]; simp [h1, h2])
  have hfa₄ : ∀ a, a ≠ "off" → σ₄.arrs a = σ₃.arrs a := fun a ha =>
    r₄.frame_arr a (by rw [warrs_readLoop]; simpa using ha)
  have hn₄ : σ₄.vars "n" = n := by
    rw [hfv₄ "n" (by decide) (by decide), hσ₃]; simpa using hn₂
  have hm₄ : σ₄.vars "m" = edgeCount x := by
    rw [hfv₄ "m" (by decide) (by decide), hσ₃]; simpa using hm₂
  have ho₄ : σ₄.out = [] := by
    rw [r₄.out_eq (noWrite_readLoop ..), hσ₃]; simpa using ho₂
  -- the targets
  obtain ⟨σ₅, hσ₅⟩ : ∃ τ : Env, τ = σ₄.setVar "len" (2 * edgeCount x) := ⟨_, rfl⟩
  have r₅ : Run B (.assign "len" (.add (.var "m") (.var "m"))) σ₄ σ₅ 4 :=
    hσ₅ ▸ (Run.assign (v := 2 * edgeCount x) (by
      rw [evalB_bin (evalB_var (by rw [hm₄]; omega)) (evalB_var (by rw [hm₄]; omega))
        (by simp only [Bop.apply_add]; rw [hm₄]; omega)]
      simp only [Bop.apply_add]
      rw [hm₄, show edgeCount x + edgeCount x = 2 * edgeCount x by omega])).mono (by norm_num)
  obtain ⟨σ₆, r₆, ⟨T', htgt₆, hT₆, hT₆pad⟩, -⟩ :=
    (readLoop_specW (a := "tgt") (lim := "len") (ys := zs) (rest := []) (by decide) (by decide)
      hzs hnsB hnsW hzsB).run (σ := σ₅)
      ⟨by simpa [hσ₅, hfa₄ "tgt" (by decide), hσ₃, ha₂] using htgtL,
        by
          intro j hj₁ hj₂
          rw [show σ₅.arrs "tgt" = σ.arrs "tgt" by
            rw [hσ₅]; simp only [arrs_setVar]; rw [hfa₄ "tgt" (by decide), hσ₃]
            simp only [arrs_setVar]; rw [ha₂]]
          exact htgtZ j hj₁ hj₂,
        by simp [hσ₅], by simpa [hσ₅] using hinp₄⟩
  have hfv₆ : ∀ y, y ≠ "i" → y ≠ "t" → σ₆.vars y = σ₅.vars y := fun y h1 h2 =>
    r₆.frame_var y (by rw [wvars_readLoop]; simp [h1, h2])
  have hfa₆ : ∀ a, a ≠ "tgt" → σ₆.arrs a = σ₅.arrs a := fun a ha =>
    r₆.frame_arr a (by rw [warrs_readLoop]; simpa using ha)
  have hn₆ : σ₆.vars "n" = n := by
    rw [hfv₆ "n" (by decide) (by decide), hσ₅]; simpa using hn₄
  have ho₆ : σ₆.out = [] := by rw [r₆.out_eq (noWrite_readLoop ..), hσ₅]; simpa using ho₄
  -- the two masks
  have hall : ∀ a, a ≠ "off" → a ≠ "tgt" → σ₆.arrs a = σ.arrs a := by
    intro a h1 h2
    rw [hfa₆ a h2, hσ₅]
    simp only [arrs_setVar]
    rw [hfa₄ a h1, hσ₃]
    simp only [arrs_setVar]
    rw [ha₂]
  obtain ⟨σ₇, r₇, M, halv₇, hM₇⟩ :=
    (fill_spec (B := B) (n := n) (a := RamDriver.alvName 0) (c := 1) (by omega)
      (by omega)).run (σ := σ₆)
      ⟨by rw [hall _ (by decide) (by decide)]; exact halvL, hn₆⟩
  have hfa₇ : ∀ a, a ≠ RamDriver.alvName 0 → σ₇.arrs a = σ₆.arrs a := fun a ha =>
    r₇.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  have hn₇ : σ₇.vars "n" = n := by
    rw [r₇.frame_var "n" (by rw [wvars_fillCom]; decide)]; exact hn₆
  obtain ⟨σ₈, r₈, Gm, hgam₈, hGm₈⟩ :=
    (fill_spec (B := B) (n := n) (a := RamDriver.gamName 0) (c := 1) (by omega)
      (by omega)).run (σ := σ₇)
      ⟨by rw [hfa₇ _ (by decide), hall _ (by decide) (by decide)]; exact hgamL, hn₇⟩
  have hfa₈ : ∀ a, a ≠ RamDriver.gamName 0 → σ₈.arrs a = σ₇.arrs a := fun a ha =>
    r₈.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  have hn₈ : σ₈.vars "n" = n := by
    rw [r₈.frame_var "n" (by rw [wvars_fillCom]; decide)]; exact hn₇
  -- the root's member list: the identity enumeration (rebase E-mem)
  obtain ⟨σ₉, r₉, Mem, hmem₉, hMem₉⟩ :=
    (RamDriverIO.fillIdent_spec (B := B) (n := n) (a := RamDriver.memName 0)
      (by omega)).run (σ := σ₈)
      ⟨(by rw [hfa₈ _ (by decide), hfa₇ _ (by decide),
          hall _ (by decide) (by decide)]; exact hmemL), hn₈⟩
  have hfa₉ : ∀ a, a ≠ RamDriver.memName 0 → σ₉.arrs a = σ₈.arrs a := fun a ha =>
    r₉.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  have hn₉ : σ₉.vars "n" = n := by
    rw [r₉.frame_var "n" (by rw [wvars_fillCom]; decide)]; exact hn₈
  -- and its count
  set σ₁₀ := σ₉.setVar (RamDriver.mnumName 0) n with hσ₁₀
  have r₁₀ : Run B (.assign (RamDriver.mnumName 0) (.var "n")) σ₉ σ₁₀ (1 + 1) := by
    have h := Run.assign (B := B) (σ := σ₉) (x := RamDriver.mnumName 0) (e := .var "n")
      (evalB_var (by rw [hn₉]; omega))
    rw [hn₉] at h
    simpa [Expr.size] using h
  have hfa₁₀ : ∀ a, σ₁₀.arrs a = σ₉.arrs a := fun a => by rw [hσ₁₀, arrs_setVar]
  have hfv₁₀ : ∀ y, y ≠ RamDriver.mnumName 0 → σ₁₀.vars y = σ₉.vars y := fun y hy => by
    rw [hσ₁₀, vars_setVar, if_neg hy]
  -- everything but the five arrays the phase writes comes back untouched
  have hall₈ : ∀ a, a ≠ "off" → a ≠ "tgt" → a ≠ RamDriver.alvName 0 →
      a ≠ RamDriver.gamName 0 → a ≠ RamDriver.memName 0 → σ₁₀.arrs a = σ.arrs a := by
    intro a h1 h2 h3 h4 h5
    rw [hfa₁₀ a, hfa₉ a h5, hfa₈ a h4, hfa₇ a h3, hall a h1 h2]
  have hm₈ : σ₁₀.vars "m" = edgeCount x := by
    rw [hfv₁₀ "m" (by simp [RamDriver.mnumName, String.ext_iff]),
      r₉.frame_var "m" (by rw [wvars_fillCom]; decide),
      r₈.frame_var "m" (by rw [wvars_fillCom]; decide),
      r₇.frame_var "m" (by rw [wvars_fillCom]; decide),
      hfv₆ "m" (by decide) (by decide), hσ₅]
    simpa using hm₄
  have rall : Run B RamDriver.decodeCom σ σ₁₀ _ :=
    r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq (r₇.seq (r₈.seq (r₉.seq r₁₀))))))))
  refine ⟨σ₁₀, _, rall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [decodeCost]; omega
  · rw [hσ₁₀, out_setVar, r₉.out_eq (noWrite_fillCom ..), r₈.out_eq (noWrite_fillCom ..),
      r₇.out_eq (noWrite_fillCom ..)]
    exact ho₆
  · exact csrGraph_of_encodesGraph hx (fun _ _ => rfl)
      (fun j hj => Lax3Proofs.RamDriverDedup.padTarget_lt hj)
  · rw [hfv₁₀ "n" (by simp [RamDriver.mnumName, String.ext_iff])]; exact hn₉
  · rw [hfa₁₀ _, hfa₉ _ (by simp [RamDriver.memName, String.ext_iff]), hfa₈ _ (by decide),
      hfa₇ _ (by decide), hfa₆ _ (by decide), hσ₅]
    simp only [arrs_setVar]
    rw [hoff₄]
    exact arrOf_congr fun i hi => by rw [hO₄ i hi, hyd i hi]
  · rw [hfa₁₀ _, hfa₉ _ (by simp [RamDriver.memName, String.ext_iff]), hfa₈ _ (by decide),
      hfa₇ _ (by decide), htgt₆]
    refine arrOf_congr fun j hj => ?_
    rcases lt_or_ge j (2 * edgeCount x) with hjs | hjs
    · rw [hT₆ j hjs, hzd j hjs, Lax3Proofs.RamDriverDedup.padTarget_lt hjs]
    · rw [hT₆pad j hjs hj, Lax3Proofs.RamDriverDedup.padTarget_ge hjs]
  · exact hm₈
  · exact ⟨Nat.zero_le _, by rw [rall.frame_var "lw" (by decide)]; exact hOlw, hOsz.run rall,
      by rw [hall₈ "elm" (by decide) (by decide) (by decide) (by decide)
        (by simp [RamDriver.memName, String.ext_iff])]; exact hz₁,
      by rw [hall₈ "bh" (by decide) (by decide) (by decide) (by decide)
        (by simp [RamDriver.memName, String.ext_iff])]; exact hz₂,
      by rw [hall₈ "ooff" (by decide) (by decide) (by decide) (by decide)
        (by simp [RamDriver.memName, String.ext_iff])]; exact hz₃,
      by rw [hall₈ "noff" (by decide) (by decide) (by decide) (by decide)
        (by simp [RamDriver.memName, String.ext_iff])]; exact hz₄,
      by rw [hall₈ "stf" (by decide) (by decide) (by decide) (by decide)
        (by simp [RamDriver.memName, String.ext_iff])]; exact hz₅,
      by rw [hall₈ "sta" (by decide) (by decide) (by decide) (by decide)
        (by simp [RamDriver.memName, String.ext_iff])]; exact hz₆,
      by rw [hall₈ "std" (by decide) (by decide) (by decide) (by decide)
        (by simp [RamDriver.memName, String.ext_iff])]; exact hz₇,
      by rw [hall₈ "ste" (by decide) (by decide) (by decide) (by decide)
        (by simp [RamDriver.memName, String.ext_iff])]; exact hz₈,
      run_mem_arrs_lt rall "itg" hw₁, run_mem_arrs_lt rall "ntg" hw₂⟩
  · exact ⟨M, (by rw [hfa₁₀ _,
      hfa₉ _ (by simp [RamDriver.memName, RamDriver.alvName, String.ext_iff]),
      hfa₈ _ (by decide)]; exact halv₇), hM₇⟩
  · refine ⟨Gm, ?_, hGm₈⟩
    rw [hfa₁₀ _, hfa₉ _ (by simp [RamDriver.memName, RamDriver.gamName, String.ext_iff])]
    exact hgam₈
  · exact ⟨Mem, (by rw [hfa₁₀ _]; exact hmem₉), hMem₉,
      by rw [hσ₁₀, vars_setVar, if_pos rfl]⟩

/-! ## §2 The composed decode: `decodeCom ; lwCom ; dedupCom` -/

/-- The dedup guard with the live-width repair spliced in front: the
`"lw"` assignment sits beside the identical `"dq"` assignment that opens
`dedupCom`, right where `"m"` is live. `dedupCom` itself is untouched. -/
def dedupComL : Com := .seq lwCom dedupCom

/-- **The composed dedup'd decode**: the landed decode, the one-line
live-width repair, and the landed dedup guard. -/
def decodeComD : Com := .seq RamDriver.decodeCom dedupComL

/-- What the composed phase costs: the decode, the repair's `4`, the
guard. -/
def decodeDLCost (n ns : ℕ) : ℕ := decodeCost n ns + dedupCost n ns + 4

/-- Frame of the repair: it assigns exactly `"lw"`. -/
theorem wvars_lwCom : lwCom.wvars = ["lw"] := rfl

theorem warrs_lwCom : lwCom.warrs = [] := rfl

theorem noWrite_lwCom : lwCom.NoWrite := by
  simp [Lax3Proofs.Refine.BridgeSeamProbe.lwCom, Com.NoWrite]

/-- **The composed obligation** — `RamDriverDedup.DecodeImplementsD`
with the entry live-width clause at the satisfiable index `0`: the
precondition asks `OrderMem B n 0 W` and the postcondition delivers
`OrderMem B n (dedupNs x) W`, with the width scalar *produced* by the
phase itself. Everything else is `DecodeImplementsD`'s list (its
vestigial `T` parameter and pad hypothesis are dropped — the composed
phase pins its own target function). -/
def DecodeImplementsDL (B : ℕ) (x : List ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (ns W K : ℕ) : Prop :=
  (∀ v ∈ x, v < B) → n + 1 < B → ns < B → W < B → ns ≤ W →
    Spec B (fun σ => DecodeMem n ns W σ ∧ OrderMem B n 0 W σ ∧ DedupMem n σ ∧
        σ.inp = x ∧ σ.out = [])
      decodeComD
      (fun _ σ' => σ'.out = [] ∧
        CsrGraph G (dedupNs x) (dedupOffset x) (dedupTarget x) ∧
        RamElim.CsrSimple G (dedupNs x) (dedupOffset x) (dedupTarget x) ∧
        dedupNs x ≤ ns ∧
        (∀ z, dedupNs x ≤ z → z < W → dedupTarget x z = 0) ∧
        σ'.vars "n" = n ∧
        σ'.arrs "off" = arrOf (n + 1) (dedupOffset x) ∧
        σ'.arrs "tgt" = arrOf W (dedupTarget x) ∧
        σ'.vars "m" + σ'.vars "m" = dedupNs x ∧
        OrderMem B n (dedupNs x) W σ' ∧
        DedupMem n σ' ∧
        (∃ M, σ'.arrs (alvName 0) = arrOf n M ∧ ∀ v < n, M v = 1) ∧
        (∃ Gm, σ'.arrs (gamName 0) = arrOf n Gm ∧ ∀ v < n, Gm v = 1) ∧
        (∃ Mem, σ'.arrs (memName 0) = arrOf n Mem ∧ (∀ v < n, Mem v = v) ∧
          σ'.vars (mnumName 0) = n)) K

set_option maxHeartbeats 1000000 in
/-- **The composed obligation, discharged**: the replayed decode
(`decode_spec_lw0`), the landed repair (`lwCom_spec` — the assignment
upgrades `OrderMem` from index `0` to the input's slot count), and the
landed guard (`dedup_spec`, with `orderMem_dedup` carrying the scratch
across at the *compacted* count). -/
theorem decodeImplementsDL {B n ns W K : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hK : decodeDLCost n ns ≤ K) :
    DecodeImplementsDL B x G ns W K := by
  classical
  intro hxB hnB hnsB hWB hnsW
  have hnsle : dedupNs x ≤ ns := by
    rw [hns]
    exact Lax3Proofs.RamDriverDedup.dedupNs_le hx.vertexCount_eq hx.offset_zero
      hx.offset_last hx.offset_mono
  have hTlo : ∀ j < ns, padTarget x ns j = target x j :=
    fun _ hj => Lax3Proofs.RamDriverDedup.padTarget_lt hj
  have hThi : ∀ z, ns ≤ z → z < W → padTarget x ns z = 0 :=
    fun _ h₁ _ => Lax3Proofs.RamDriverDedup.padTarget_ge h₁
  have hdec := decode_spec_lw0 (B := B) (W := W) hx hns hxB hnB hnsB hWB hnsW
  have hlw := lwCom_spec (B := B) (n := n) (ns := ns) (W := W) (e := edgeCount x)
    (by omega)
  have hpass := Lax3Proofs.RamDriverDedup.dedup_spec (B := B) (T := padTarget x ns)
    hx hns hTlo hThi hnB hnsB hWB hnsW
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hmem, hord, hdmem, hinp, hout⟩ := hσ
  -- the decode, from the fresh-satisfiable entry
  obtain ⟨σ₁, r₁, ho₁, hcsr₁, hn₁, hoff₁, htgt₁, hm₁, hord₁, hM, hGm, hMem⟩ :=
    hdec.run (σ := σ) ⟨hmem, hord, hinp, hout⟩
  -- the repair: one assignment, and the live width is the slot count
  obtain ⟨σ₂, r₂, hord₂⟩ :=
    hlw.run (σ := σ₁) ⟨hm₁, hord₁, by omega, by omega⟩
  have hfv₂ : ∀ y, y ≠ "lw" → σ₂.vars y = σ₁.vars y := fun y hy =>
    r₂.frame_var y (by rw [wvars_lwCom]; simpa using hy)
  have hfa₂ : ∀ a, σ₂.arrs a = σ₁.arrs a := fun a =>
    r₂.frame_arr a (by rw [warrs_lwCom]; simp)
  -- the guard, on the state the repair left
  have hfr₁ : σ₁.arrs "dmk" = σ.arrs "dmk" := r₁.frame_arr "dmk" (by decide)
  have hdmem₂ : DedupMem n σ₂ :=
    ⟨by rw [hfa₂, hfr₁]; exact hdmem.1, by rw [hfa₂, hfr₁]; exact hdmem.2⟩
  obtain ⟨σ₃, r₃, hn₃, hm₃, hoff₃, htgt₃, hdmem₃⟩ :=
    hpass.run (σ := σ₂)
      ⟨by rw [hfv₂ "n" (by decide)]; exact hn₁,
        by rw [hfv₂ "m" (by decide), hm₁]; omega,
        by rw [hfa₂]; exact hoff₁, by rw [hfa₂]; exact htgt₁, hdmem₂⟩
  refine ⟨σ₃, _, r₁.seq (r₂.seq r₃), by rw [decodeDLCost] at hK; omega, ?_,
    Lax3Proofs.RamDriverDedup.csrGraph_dedup hx,
    Lax3Proofs.RamDriverDedup.csrSimple_dedup hx, hnsle,
    fun z hz _ => Lax3Proofs.RamDriverDedup.dedupTarget_eq_zero hz,
    hn₃, hoff₃, htgt₃, hm₃,
    Lax3Proofs.RamDriverDedup.orderMem_dedup hord₂ r₃ hnsle, hdmem₃, ?_, ?_, ?_⟩
  · rw [r₃.out_eq Lax3Proofs.RamDriverDedup.noWrite_dedupCom, r₂.out_eq noWrite_lwCom]
    exact ho₁
  · obtain ⟨M, hMa, hMv⟩ := hM
    refine ⟨M, ?_, hMv⟩
    rw [Lax3Proofs.RamDriverDedup.frame_arr_dedupCom r₃ (RamDriver.alvName 0)
      (by decide) (by decide) (by decide), hfa₂]
    exact hMa
  · obtain ⟨Gm, hGa, hGv⟩ := hGm
    refine ⟨Gm, ?_, hGv⟩
    rw [Lax3Proofs.RamDriverDedup.frame_arr_dedupCom r₃ (RamDriver.gamName 0)
      (by decide) (by decide) (by decide), hfa₂]
    exact hGa
  · obtain ⟨Mem, hMa, hMv, hMc⟩ := hMem
    refine ⟨Mem, ?_, hMv, ?_⟩
    · rw [Lax3Proofs.RamDriverDedup.frame_arr_dedupCom r₃ (RamDriver.memName 0)
        (by simp [RamDriver.memName, String.ext_iff])
        (by simp [RamDriver.memName, String.ext_iff])
        (by simp [RamDriver.memName, String.ext_iff]), hfa₂]
      exact hMa
    · rw [Lax3Proofs.RamDriverDedup.frame_var_dedupCom r₃ (RamDriver.mnumName 0)
        (by simp [RamDriver.mnumName, String.ext_iff])
        (by simp [RamDriver.mnumName, String.ext_iff])
        (by simp [RamDriver.mnumName, String.ext_iff])
        (by simp [RamDriver.mnumName, String.ext_iff])
        (by simp [RamDriver.mnumName, String.ext_iff])
        (by simp [RamDriver.mnumName, String.ext_iff])
        (by simp [RamDriver.mnumName, String.ext_iff])
        (by simp [RamDriver.mnumName, String.ext_iff])
        (by simp [RamDriver.mnumName, String.ext_iff]),
        hfv₂ _ (by simp [RamDriver.mnumName, String.ext_iff])]
      exact hMc

/-! ## §3 The restated precondition, and the `initEnv` anti-witness

The restated root's precondition is the landed `RootPre` with the
live-width index at `0` and the guard's mark array added. Finding 4's
kill is the pair below: at an *edgeful* word the restated precondition
transfers to a fresh environment exactly as the landed one's seven free
conjuncts always did — the eighth conjunct, the unreachable one, is no
longer asked — while the landed precondition holds at no fresh
environment at all (`BridgeSeamProbe.not_rootPre_initEnv`, untouched). -/

/-- The conjuncts a caller must produce to enter `driverRootD`. Beside
`RootPre`: `OrderMem` at index `0`, plus `DedupMem`. -/
def RootPreD (B n ns W q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) (x : List ℕ)
    (σ : Env) : Prop :=
  DecodeMem n ns W σ ∧ LevelMem B n cap mb σ ∧ DepthMem n cap mb σ ∧
    OrderMem B n 0 W σ ∧ DedupMem n σ ∧ TablesSized q_top cap mb φ n σ ∧
    BaseArrs B q_top cap mb ℓ φ σ ∧ σ.inp = x ∧ σ.out = []

section InitEnv

variable {B n ns W q_top cap mb ℓ : ℕ} {φ : Lax3.FirstOrder.FO 0} {x : List ℕ} {σ : Env}

open Lax3Proofs.Refine.BridgeSeamProbe in
/-- Every conjunct of the restated precondition transfers to the fresh
environment on the same word — including, now, the live-width clause,
which at index `0` is what a fresh scalar bank already satisfies. -/
theorem rootPreD_initEnv (hB : 0 < B)
    (hsat : RootPreD B n ns W q_top cap mb ℓ φ x σ) :
    RootPreD B n ns W q_top cap mb ℓ φ x (initEnv (extOf σ) x) := by
  obtain ⟨hdm, hmem, hdep, hord, hdd, htsz, hbarr, -, -⟩ := hsat
  exact ⟨decodeMem_of_zero (decodeMem_initEnv hdm), levelMem_initEnv hB hmem,
    depthMem_initEnv hdep, orderMem_initEnv_of hB hord, dedupMem_initEnv hdd,
    tablesSized_initEnv htsz, baseArrs_initEnv hbarr, rfl, rfl⟩

/-- **Finding 4, killed at the restated root — the anti-witness.** At an
edgeful word (`0 < ns`) the restated precondition is satisfiable at a
fresh environment while the landed one is not: the exact converse of
`BridgeSeamProbe.rootPre_initEnv_iff_ns_zero`, at the same
transfer. (No prologue could have done this: the value `ns` lives on
the tape and `BridgeSeamProbe.read_breaks_inp` locks it — which is why
the repair is inside the composed decode and the *pre*condition index
is `0`.) -/
theorem restated_pre_initEnv_where_landed_is_not (hB : 0 < B) (hns : 0 < ns)
    (hsat : RootPreD B n ns W q_top cap mb ℓ φ x σ) :
    (∃ ext, RootPreD B n ns W q_top cap mb ℓ φ x (initEnv ext x)) ∧
      ∀ ext, ¬ RootPre B n ns W q_top cap mb ℓ φ x (initEnv ext x) :=
  ⟨⟨extOf σ, rootPreD_initEnv hB hsat⟩,
    fun _ => Lax3Proofs.Refine.BridgeSeamProbe.not_rootPre_initEnv hns⟩

end InitEnv

/-! ## §4 The level assembly at general `R`

`RamDriverRoot.levelAt` instantiates
`RamDriverCluster.levelImplements` at `R = 0` with the ordering slot at
`True`. `levelAtR` is the same instantiation at general `R` with the
slot at `RamDriverCompose.OrderP R G M`, so the cover-degree hypothesis
`hdeg` is consumed in its per-π conditional form — the shape
`RamDriverRoot.exists_wreachDeg_of_orderP` produces on a nowhere dense
class. Two residuals become hypotheses; each is a fact about landed
program text, each has its `R = 0` plug check here, and neither has a
general-`R` producer today (see the module header). -/

section LevelR

/-- **The nested driver's write-set facts at round `R`** — everything
the turn and its frames read off `Lax3Proofs.RamDriverWrites`, which
proves them at `R = 0` only. A hypothesis of `levelAtR`, so that the
general-`R` write-set recursion (a mechanical wave on the landed
recursion) lands without touching the assembly again. -/
def RFrames (q_top cap mb R ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) : Prop :=
  ∀ j : ℕ,
    (∀ a, RamDriverFrames.TurnFrozen j a →
      a ∉ (driverAt q_top cap mb R ℓ φ (j + 1)).warrs) ∧
    (∀ a, a ≤ j → ctrName a ∉ (driverAt q_top cap mb R ℓ φ (j + 1)).wvars) ∧
    xpName j ∉ (driverAt q_top cap mb R ℓ φ (j + 1)).wvars ∧
    curName j ∉ (driverAt q_top cap mb R ℓ φ (j + 1)).wvars ∧
    (∀ i, tabName j i ∉ (driverAt q_top cap mb R ℓ φ (j + 1)).warrs) ∧
    cpsName j ∉ (driverAt q_top cap mb R ℓ φ (j + 1)).warrs ∧
    cnumName j ∉ (driverAt q_top cap mb R ℓ φ (j + 1)).wvars ∧
    cixName j ∉ (driverAt q_top cap mb R ℓ φ (j + 1)).wvars ∧
    (∀ a, a ≤ j → mnumName a ∉ (driverAt q_top cap mb R ℓ φ (j + 1)).wvars)

/-- The plug check: at `R = 0` the residual is the landed capital. -/
theorem rFrames_zero (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    RFrames q_top cap mb 0 ℓ φ := fun _j =>
  ⟨fun _ ha => Lax3Proofs.RamDriverRoot.turnFrozen_notMem_warrs_driverAt ha,
    fun _ ha => Lax3Proofs.RamDriverRoot.ctrName_notMem_wvars_driverAt ha,
    Lax3Proofs.RamDriverRoot.xpName_notMem_wvars_driverAt,
    Lax3Proofs.RamDriverRoot.curName_notMem_wvars_driverAt,
    fun i => Lax3Proofs.RamDriverRoot.tabName_notMem_warrs_driverAt i,
    Lax3Proofs.RamDriverRoot.cpsName_notMem_warrs_driverAt,
    Lax3Proofs.RamDriverRoot.cnumName_notMem_wvars_driverAt,
    Lax3Proofs.RamDriverRoot.cixName_notMem_wvars_driverAt,
    fun _ ha => Lax3Proofs.RamDriverRoot.mnumName_notMem_wvars_driverAt ha⟩

/-- The arena is a subgraph of the level's graph. -/
theorem masked_le {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) : masked G M ≤ G := by
  intro u v h
  exact (RamBfs.masked_adj.mp h).1

/-- Weak reachability only shrinks under the mask: a walk of the arena
is a walk of the graph, with the same support. -/
theorem wreach_masked_subset {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (r : ℕ) (v : Fin n) :
    Lax12.ColoringNumbers.wreach (masked G M) π r v ⊆
      Lax12.ColoringNumbers.wreach G π r v := by
  rintro u ⟨w, hlen, hmin⟩
  refine ⟨w.mapLe (masked_le G M), ?_, fun y hy => ?_⟩
  · exact (SimpleGraph.Walk.length_map _ w).le.trans hlen
  · exact hmin y ((SimpleGraph.Walk.support_mapLe_eq_support (masked_le G M) w) ▸ hy)

/-- **The `R*` ordering-property slot value, in the mask-uniform shape
the frozen interface admits**: the exported ordering has weak
`2·cap`-reachability degree at most `Kmass` on the level's graph — the
value `RamDriver.OrderImplements`' own docstring promises for `R = R*`.

`RamDriverCompose.OrderP R G M` itself **cannot** be the slot value:
`RamDriverCluster.levelImplements` binds its slot `P` *before* the mask
it quantifies (`horder`/`hmass` read `P π ord` at every `M`), and
`OrderP` names the mask. That is the compiled shape of the F-c-3
threading gap — the per-mask bundle fits the per-obligation
`OrderImplementsR`, and does not fit the level induction's slot. On the
graph the bound *implies* the per-arena bound at every mask
(`wreach_masked_subset`), which is what `hmass` consumes; and the
`OrderP` producer closes this value at the all-alive arena
(`degOrder_of_orderP_alive`), which is where the root instantiates
it. -/
def DegOrder (n : ℕ) (G : SimpleGraph (Fin n)) (cap Kmass : ℕ)
    (π : Equiv.Perm (Fin n)) (_ord : ℕ → ℕ) : Prop :=
  ∀ v : Fin n, (Lax12.ColoringNumbers.wreach G π (2 * cap) v).ncard ≤ Kmass

/-- **The per-π producer reaches the slot value at the root arena**:
where the mask keeps everything alive, the `OrderP`-conditional degree
bound — `exists_wreachDeg_of_orderP`'s shape — is the slot value
itself. -/
theorem degOrder_of_orderP_alive {n cap Kmass R : ℕ} {G : SimpleGraph (Fin n)} {M : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {ord : ℕ → ℕ} (hall : ∀ v < n, M v ≠ 0)
    (hdeg : RamDriverCompose.OrderP R G M π ord →
      ∀ v : Fin n, (Lax12.ColoringNumbers.wreach (masked G M) π (2 * cap) v).ncard ≤ Kmass)
    (hP : RamDriverCompose.OrderP R G M π ord) : DegOrder n G cap Kmass π ord := by
  intro v
  have h := hdeg hP v
  rwa [RamElim.masked_of_all_alive G hall] at h

variable {n : ℕ} {B q_top cap mb ns W ℓ R j Kmass : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
  {ord Xoff Xmem asg : ℕ → ℕ} {mm k : ℕ} {Kb Ki Ksc Ks : ℕ} {Kin : ℕ → ℕ}

open Lax3Proofs.Refine.MassWeight (arenaWeight blockWeight) in
open Classical in
/-- `RamDriverRoot.clusterStepAt` with the nested driver at round `R`
and the write-set facts read off the `RFrames` residual. -/
theorem clusterStepAtR (hfr : RFrames q_top cap mb R ℓ φ)
    (hcap : cap = rhoMinus 0 q_top) (hmb : mb = ℓ * (2 * cap + 1)) (hjl : j < ℓ)
    (hB : WordBoundK B n Kmass ns cap mb) (hcsr : CsrGraph G ns O T)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n ns σs.t ≤ Kb)
    (hcostI : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hKsc : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc)
    (hmono : Monotone Kin)
    (hK : Lax3Proofs.RamDriverRoot.turnCostSize n ns cap mb q_top j φ Ksc
      (blockWeight n G Xoff Xmem k) (Kin (blockWeight n G Xoff Xmem k)) ≤ Ks) :
    ClusterStepImplements B q_top cap mb ns W ℓ j φ G O T M Gm C π ord Xoff Xmem asg mm k
      (arenaWeight n G) (driverAt q_top cap mb R ℓ φ (j + 1)) Kin Ks :=
  RamDriverCluster.clusterStepImplements hcap
    (RamDriverDescend.descendStep hmb hjl le_rfl)
    (fun _ _ _ _ => RamDriverDescend.enumStep hB le_rfl)
    (fun _ _ _ _ _ => RamDriverDescend.colourStep le_rfl)
    (fun hinner _ _ _ _ _ _ => RamDriverFrames.innerFrames hinner
      (fun _ ha => (hfr j).1 _ ha)
      (fun _ ha => (hfr j).2.1 _ ha)
      (hfr j).2.2.1 (hfr j).2.2.2.1
      (fun _ ha => (hfr j).2.2.2.2.2.2.2.2 _ ha))
    (fun _ _ _ _ _ _ =>
      RamDriverFrames.scatterStep hcsr hB hbnd hcostI hKsc)
    (fun _ _ _ _ _ _ => RamDriverBase.readbackStep hB.one_lt hB.n_lt le_rfl)
    hmono
    (fun _ hkn hout hsub =>
      Refine.MassWeight.arenaWeight_le_blockWeight G hout hkn hsub)
    hK

open Lax3Proofs.Refine.MassWeight (arenaWeight blockWeight) in
open Classical in
/-- `RamDriverRoot.clusterFramesAt` at round `R`, off the residual. -/
theorem clusterFramesAtR (hfr : RFrames q_top cap mb R ℓ φ)
    (hmb : mb = ℓ * (2 * cap + 1)) (hjl : j < ℓ)
    (hB : WordBoundK B n Kmass ns cap mb) (hcsr : CsrGraph G ns O T)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n ns σs.t ≤ Kb)
    (hcostI : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hKsc : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc)
    (hmono : Monotone Kin)
    (hK : Lax3Proofs.RamDriverRoot.turnCostSize n ns cap mb q_top j φ Ksc
      (blockWeight n G Xoff Xmem k) (Kin (blockWeight n G Xoff Xmem k)) ≤ Ks) :
    RamDriverCluster.ClusterFrames B q_top cap mb ns W ℓ j φ G O T M Gm C π ord
      Xoff Xmem asg mm k (arenaWeight n G)
      (driverAt q_top cap mb R ℓ φ (j + 1)) Kin Ks :=
  RamDriverFrames.clusterFrames hcsr hB
    (RamDriverDescend.descendStep hmb hjl le_rfl)
    (fun _ _ _ _ => RamDriverDescend.enumStep hB le_rfl)
    (fun _ _ _ _ _ => RamDriverDescend.colourStep le_rfl)
    (fun _ ha => (hfr j).1 _ ha)
    (fun _ ha => (hfr j).2.1 _ ha)
    (hfr j).2.2.1 (hfr j).2.2.2.1
    (fun _ ha => (hfr j).2.2.2.2.2.2.2.2 _ ha)
    (fun _ _ _ _ _ _ =>
      RamDriverFrames.scatterStep hcsr hB hbnd hcostI hKsc)
    (fun _ _ _ _ _ _ => RamDriverBase.readbackStep hB.one_lt hB.n_lt le_rfl)
    (fun i => (hfr j).2.2.2.2.1 i)
    hmono
    (fun _ hkn hout hsub =>
      Refine.MassWeight.arenaWeight_le_blockWeight G hout hkn hsub)
    hK

open Classical in
/-- `RamDriverRoot.loopFrames` at round `R`, off the residual. -/
theorem loopFramesR (hfr : RFrames q_top cap mb R ℓ φ) :
    cpsName j ∉ (clusterCom q_top cap mb φ j
        (driverAt q_top cap mb R ℓ φ (j + 1))).warrs ∧
      cnumName j ∉ (clusterCom q_top cap mb φ j
        (driverAt q_top cap mb R ℓ φ (j + 1))).wvars ∧
      cixName j ∉ (clusterCom q_top cap mb φ j
        (driverAt q_top cap mb R ℓ φ (j + 1))).wvars :=
  ⟨RamDriverWrites.cpsName_notMem_warrs_clusterCom q_top cap mb j φ (hfr j).2.2.2.2.2.1,
    RamDriverWrites.cnumName_notMem_wvars_clusterCom q_top cap mb j φ (hfr j).2.2.2.2.2.2.1,
    RamDriverWrites.cixName_notMem_wvars_clusterCom q_top cap mb j φ (hfr j).2.2.2.2.2.2.2.1⟩

open Lax3Proofs.Refine.MassWeight (arenaWeight blockWeight) in
open Classical in
/-- **Every level of the driver at general `R`** — `RamDriverRoot.levelAt`
with the ordering slot at `RamDriverCompose.OrderP R G M`.

Deltas from `levelAt`, and nothing else moves: the ordering slot is
`DegOrder n G cap Kmass` — the mask-uniform `R*` slot value (see its
docstring: `OrderP R G M` cannot inhabit the slot, whose `P` binds
before the mask) — so the every-permutation `hdeg` hypothesis is
**gone**, subsumed by the slot: `hmass` reads the degree off the
phase's own export, through `wreach_masked_subset` at the level's
mask. `horder` is the `R`-round phase walk at that slot value (the
named residual — see the module header for why the landed
`OrderImplementsRL` walk cannot feed the slot's bare-`LevelPre` shape);
`hfr` is the round-`R` write-set residual; `hKo` reads the phase budget
at `orderPhaseCostR`. The hypothesis list is otherwise byte-identical
to `levelAt`'s — except for one more residual this restatement
*exposes*:

**`hptr`/`hexit`, the arena-pointer word slots, resurface as
hypotheses.** `levelAt` discharges them from the unconditional `hdeg`
(`ArenaPointer.ptrWords_of_mass`/`massWords_of_mass`). The frozen
`RamDriverCluster.levelImplements` quantifies both slots over *every*
ordering with only `RamCover.OrdersBy` in hand — its own proof uses
them exactly at the phase-produced ordering, where the `P π ord`
witness is in scope one line earlier, but the slot does not pass it —
so no slot-conditional degree can feed them. F-c-3 threaded `P` through
`hmass` and not through W2's two pointer slots; until the cluster file
carries `P π ord` beside `OrdersBy` there (a landed-file wave), the
readings stay hypotheses here, in the frozen slots' own shape. -/
theorem levelAtR {N : ℕ → ℕ} {s : ℕ} {Kb : ℕ} {Ki Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}
    (hcap : cap = rhoMinus 0 q_top) (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBoundK B n Kmass ns cap mb) (hWB : n + W + 1 < B) (hpow : 2 ^ sigL cap mb ℓ < B)
    (hcsr : RamElim.CsrSimple G ns O T)
    (hptr : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ),
      RamCover.OrdersBy n π ord → RamDriver.PtrWords B G M π ord cap)
    (hexit : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ),
      RamCover.OrdersBy n π ord → RamDriver.MassWords B G M π ord cap)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n ns σs.t ≤ Kb)
    (hcostI : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j)
    (hKsc : ∀ j < ℓ, Ki j * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc j)
    (hKmono : ∀ j, Monotone (Kl j))
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      Lax3Proofs.RamDriverRoot.turnCostSize n ns cap mb q_top j φ (Ksc j) t (Kl (j + 1) t)
        ≤ Ks j t)
    (hKbase : ∀ m, RamDriverBot.baseCost q_top cap mb ℓ n φ ≤ Kl ℓ m)
    (hKo : ∀ j m, RamDriverCompose.orderPhaseCostR n ns W R ≤ Ko j m)
    (hKc : ∀ j m, RamDriverCompose.coverPhaseCost n ns ≤ Kc j m)
    (hKd : ∀ j m, Refine.DeadSweep.sweepCost q_top cap mb j n φ ≤ Kd j m)
    (hbinj : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (mm : ℕ),
      RamCover.CoverOut G M π ord cap mm Xoff Xmem asg → Refine.MassMath.BlockInj n Xoff Xmem)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m)
    (horder : ∀ j < ℓ, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      OrderImplements B n R W cap mb ns j G O T M Gm C (DegOrder n G cap Kmass)
        (RamDriverCompose.orderPhaseCostR n ns W R))
    (hfr : RFrames q_top cap mb R ℓ φ) :
    ∀ j ≤ ℓ, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      LevelImplements B q_top cap mb R ℓ W ns j φ G O T M Gm C
        (Kl j (arenaWeight n G M)) :=
  RamDriverCluster.levelImplements hB hWB hcsr
    (fun _ _ _ _ _ _ => RamElim.implements)
    (fun _ _ _ _ _ _ _ => RamDriverAugment.implements)
    (fun A₀ ord π => RamDriverOrder.coverTurnImplements B n ns G A₀ O T ord π cap)
    hptr hexit
    hQ hℓ
    (fun M Gm C hbot hbit => by
      rw [driverAt_bot]
      exact ((RamDriverCompose.baseImplements hB hpow hbot hbit).pre
        (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)).mono (hKbase _))
    (fun j hj M Gm C _d h₁ h₂ h₃ h₄ h₅ =>
      ((horder j hj M Gm C) h₁ h₂ h₃ h₄ h₅).mono
        (hKo j (arenaWeight n G M)))
    (fun j _ M _ _ _ _ _d h₁ h₂ h₃ h₄ h₅ h₆ =>
      (RamDriverCompose.coverImplements h₁ h₂ h₃ h₄ h₅ h₆).mono (hKc j (arenaWeight n G M)))
    (fun j hj _ _ _ _ _ _ _ _ _ _ =>
      clusterStepAtR hfr hcap hmb hj hB hcsr.csr (hbnd j hj) (hcostI j hj) (hKsc j hj)
        (hKmono (j + 1)) (hKs j hj _))
    (fun j hj _ _ _ _ _ _ _ _ _ _ =>
      clusterFramesAtR hfr hmb hj hB hcsr.csr (hbnd j hj) (hcostI j hj) (hKsc j hj)
        (hKmono (j + 1)) (hKs j hj _))
    (fun _ _ => loopFramesR hfr)
    (fun j _ M _ _ =>
      (Refine.DeadSweep.sweepImplements (jd := j) hB).mono
        (hKd j (arenaWeight n G M)))
    (fun M π ord Xoff Xmem asg cps mm cnum hordby hP hout hcomp =>
      Refine.MassWeight.mass_of_alive_compaction_weight G hordby hout
        (hbinj M π ord Xoff Xmem asg mm hout)
        (fun v => le_trans
          (Set.ncard_le_ncard (wreach_masked_subset G M π (2 * cap) v) (Set.toFinite _))
          (hP v))
        hcomp)
    hKl

end LevelR

/-! ### The RL bridge, and why it is vacuous today

The route from the landed `R`-round walk
(`RamDriverCompose.orderImplementsR`, which discharges
`OrderImplementsRL`) to any bare-`LevelPre` phase obligation — the
per-obligation `OrderImplementsR` below, and `levelAtR`'s `horder`
alike — is a `.pre` step: the RL Spec carries the extra precondition
conjunct `chainWidthE n ns d D₁ R ≤ σ.vars "lw"`, and the bare
precondition must imply it. `LevelPre`'s `OrderMem` pins exactly
`ns ≤ lw ≤ W`, so the only bridging hypothesis expressible there is
`chainWidthE … ≤ ns` — and that is **false at every instance**
(`ns_lt_chainWidthE`): `chainWidthE` is `n·(budget+1)² + ns + 1`. The
bridge is compiled (`orderSlot_of_RL`) so the fit is checkable, and its
hypothesis's unsatisfiability is compiled beside it
(`no_guard_instance`) so the residual is a theorem: feeding the landed
`R`-walk through the frozen slot shape needs the width guard *inside*
`LevelPre` (or a re-walked phase), not a weakening. -/

section Bridge

variable {n : ℕ} {B cap mb ns W j R d D₁ : ℕ} {G : SimpleGraph (Fin n)}
  {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}

/-- The `.pre` bridge from the landed RL walk to the level's slot shape,
at the only guard `LevelPre` can supply. -/
theorem orderSlot_of_RL
    (h : RamDriverCompose.OrderImplementsRL B n R W cap mb ns j d D₁ G O T M Gm C)
    (hguard : Lax3Proofs.TgtCoupling.chainWidthE n ns d D₁ R ≤ ns) :
    RamDriverCompose.OrderImplementsR B n R W cap mb ns j G O T M Gm C := by
  intro dK hB hcsr hWB he ha
  refine (h hB hcsr hWB he ha).pre ?_
  intro σ hσ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hord, -, -⟩ := id hσ
  exact ⟨hσ, le_trans hguard hord.2.1.1⟩

/-- …and the guard is unsatisfiable: the chain's width budget always
exceeds the slot count it would have to fit under. -/
theorem ns_lt_chainWidthE (n ns d D₁ R : ℕ) :
    ns < Lax3Proofs.TgtCoupling.chainWidthE n ns d D₁ R := by
  rw [Lax3Proofs.TgtCoupling.chainWidthE]
  omega

/-- The compiled residual: no instance feeds `orderSlot_of_RL`. -/
theorem no_guard_instance (n ns d D₁ R : ℕ) :
    ¬ Lax3Proofs.TgtCoupling.chainWidthE n ns d D₁ R ≤ ns :=
  fun h => absurd h (Nat.not_le.mpr (ns_lt_chainWidthE n ns d D₁ R))

end Bridge

/-! ## §5 The root, restated -/

open Classical in
/-- **The whole program at the composed decode**: dedup'd decode with
the live-width repair, drive, decide. -/
noncomputable def driverRootD (q_top cap mb R ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) : Com :=
  .seq decodeComD (.seq (driverAt q_top cap mb R ℓ φ 0) (sentenceCom q_top cap mb φ))

section Correct

variable {n ns : ℕ} {B q_top cap mb R ℓ W Kd Kl Ks Kmass : ℕ} {G : SimpleGraph (Fin n)}
  {x : List ℕ} {φ : Lax3.FirstOrder.FO 0}

open Classical in
/-- **The composition at the composed decode** —
`RamDriver.driver_correct` with the decode leg replaced by
`DecodeImplementsDL` and the level and sentence legs read at the
compacted triple. The precondition is `RootPreD`'s conjunction; the
proof is `driver_correct`'s, with the dedup postcondition's extra
conjuncts consumed where the raw word's data hypotheses used to be. -/
theorem driverD_correct (hrank : Lax3.FirstOrder.rank φ ≤ q_top)
    (hB : WordBoundK B n Kmass ns cap mb) (hxB : ∀ v ∈ x, v < B) (hWB : W < B)
    (hnsW : ns ≤ W)
    (hdec : DecodeImplementsDL B x G ns W Kd)
    (hlev : ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ), (∀ v < n, M v ≠ 0) →
      LevelImplements B q_top cap mb R ℓ W (dedupNs x) 0 φ G (dedupOffset x) (dedupTarget x)
        M Gm C Kl)
    (hsent : ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      SentenceImplements B q_top cap mb (dedupNs x) W φ G (dedupOffset x) (dedupTarget x)
        M Gm C Ks) :
    Spec B (fun σ => DecodeMem n ns W σ ∧ LevelMem B n cap mb σ ∧ DepthMem n cap mb σ ∧
        OrderMem B n 0 W σ ∧ DedupMem n σ ∧ TablesSized q_top cap mb φ n σ ∧
        BaseArrs B q_top cap mb ℓ φ σ ∧ σ.inp = x ∧ σ.out = [])
      (driverRootD q_top cap mb R ℓ φ)
      (fun _ σ' => σ'.out = [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
      (Kd + (Kl + Ks)) := by
  classical
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hdm, hmem, hdep, hord0, hdmem, htsz, hbarr, hinp, hout⟩ := hσ
  -- the composed decode
  obtain ⟨σ₁, hrun₁, hout₁, hcsrD, hsimpD, hnsle, hpadD, hn₁, hoff₁, htgt₁, hm₁, hordmem₁,
      hdmem₁, ⟨M, hM₁, hMone⟩, ⟨Gm, hGm₁, hGmone⟩, ⟨Mem, hMem₁, hMemid, hMnum₁⟩⟩ :=
    (hdec hxB hB.succ_lt hB.ns_lt hWB hnsW).run ⟨hdm, hord0, hdmem, hinp, hout⟩
  have hBD : WordBoundK B n Kmass (dedupNs x) cap mb := wordBoundK_anti hnsle hB
  -- the level's word clause on the compacted targets
  have hTB : ∀ z < W, dedupTarget x z < B := fun z hz => by
    rcases lt_or_ge z (dedupNs x) with h | h
    · exact lt_trans (hcsrD.target_lt z h) hBD.n_lt
    · rw [Lax3Proofs.RamDriverDedup.dedupTarget_eq_zero h]
      have := hB.one_lt; omega
  -- the memory the decode was handed is the memory the level is handed
  have hmem₁ : LevelMem B n cap mb σ₁ := levelMem_run hrun₁ hmem
  have hdep₁ : DepthMem n cap mb σ₁ := hdep.run hrun₁
  have htsz₁ : TablesSized q_top cap mb φ n σ₁ := htsz.run hrun₁
  have hbarr₁ : BaseArrs B q_top cap mb ℓ φ σ₁ := hbarr.run hrun₁
  -- the masks the root opens are the constant one
  have hMpos : ∀ v < n, M v ≠ 0 := fun v hv => by rw [hMone v hv]; omega
  have hMB : ∀ z < n, M z < B := fun z hz => by rw [hMone z hz]; exact hB.one_lt
  have hGmB : ∀ z < n, Gm z < B := fun z hz => by rw [hGmone z hz]; exact hB.one_lt
  -- the level, at the colouring the root has: the empty palette
  have hcolempty : ∀ c < sigL cap mb 0, σ₁.arrs (colName 0 c) = arrOf n (fun _ => 0) := by
    intro c hc
    exact absurd hc (by rw [sigL_zero]; omega)
  have hcolbit : ∀ c < sigL cap mb 0, ∀ z < n, (fun _ _ => 0 : ℕ → ℕ → ℕ) c z ≤ 1 := by
    intro c hc
    exact absurd hc (by rw [sigL_zero]; omega)
  -- the game invariant at the root: nothing has been played
  have hMG : masked G M = G := RamElim.masked_of_all_alive G hMpos
  have hGmG : masked G Gm = G :=
    RamElim.masked_of_all_alive G (fun v hv => by rw [hGmone v hv]; omega)
  have hplay₀ : PlayRec B cap G 0 M Gm σ₁ := playRec_zero cap G hMG hGmG
  have hpadD' : ∀ z, dedupNs x ≤ z → z < W → dedupTarget x z = 0 :=
    fun z hz _ => Lax3Proofs.RamDriverDedup.dedupTarget_eq_zero hz
  -- the root's member clause: the identity enumeration of the all-alive mask
  have hmemcl₀ : ∃ Mem' mmj, σ₁.arrs (memName 0) = arrOf n Mem' ∧
      σ₁.vars (mnumName 0) = mmj ∧ MemEnum n mmj Mem' M ∧ ∀ z < mmj, Mem' z < B := by
    refine ⟨Mem, n, hMem₁, hMnum₁, ⟨fun k hk => by rw [hMemid k hk]; exact hk,
      fun i k hik hk => by
        rw [hMemid i (by omega), hMemid k hk]; exact hik,
      fun k hk => by rw [hMemid k hk]; exact hMpos k hk,
      fun a ha _ => ⟨a, ha, hMemid a ha⟩⟩, fun z hz => by
        rw [hMemid z hz]; exact lt_trans hz hB.n_lt⟩
  obtain ⟨σ₂, hrun₂, ⟨hpre₂, -, htab₂⟩, hout₂⟩ :=
    (hlev M Gm (fun _ _ => 0) hMpos hcolbit).run
      (σ := σ₁) ⟨⟨hn₁, hoff₁, htgt₁, hM₁, hGm₁, hcolempty, hMB, hGmB, hcolbit, hmem₁, hdep₁,
        hm₁, hordmem₁, hpadD', hTB, hmemcl₀⟩, htsz₁, hbarr₁, hplay₀⟩
  -- the sentence readback
  obtain ⟨σ₃, hrun₃, hcond, hout₃⟩ :=
    (hsent M Gm (fun _ _ => 0) hBD hMpos).run (σ := σ₂)
      ⟨hpre₂, htab₂, by rw [hout₂, hout₁]⟩
  refine ⟨σ₃, _, (hrun₁.seq (hrun₂.seq hrun₃)).mono le_rfl, le_rfl, ?_⟩
  rw [hout₃]
  congr 1
  refine if_congr ?_ rfl rfl
  have hglue := sat_iff_eval_sentence (mb := mb) (cap := cap) hrank (masked G M)
    (colRead n (fun _ _ => 0) (sigL cap mb 0)) hcond
  exact hglue.symm.trans (by rw [hMG])

end Correct

section Main

variable {n : ℕ} {B q_top cap mb ns W ℓ s R Kmass : ℕ} {N : ℕ → ℕ}
  {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)} {x : List ℕ}
  {Kb Kb₀ Kdec Ksent : ℕ} {Ki Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}

open Classical in
/-- **The restated root at `R = 0`** —
`RamDriverRoot.driverRoot_decides_sentence` at the composed decode,
fully discharged from landed capital (the level leg is `levelAt` at the
compacted triple).

Diff from the landed root, slot for slot: the precondition's `OrderMem`
index is `0` and `DedupMem` is added (finding 4); **`hcsr` is gone** —
produced by `csrSimple_dedup`; `hO`/`hT`/`hpad0` are gone — the
compacted triple is the phase's own data and `dedupTarget_eq_zero` its
tail; `hnsW : ns ≤ W` is explicit (the landed root read it off the
precondition's `OrderMem ns`); `hKdec` covers the composed phase; the
level-facing slots read the compacted count `dedupNs x` where the
landed root's read `ns`, and are otherwise byte-identical in shape and
order; the cost is `Kdec + (Kl 0 (n + dedupNs x) + Ksent)`. The
program is `driverRootD` in place of `driverRoot`. `hdeg` stays in the
landed unconditional form — at `R = 0` the ordering slot is `True` and
slot #26 blocks exactly as the sweep records; its kill is the
general-`R` sibling below. -/
theorem driverRootD_decides_sentence
    -- the input word
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hxB : ∀ v ∈ x, v < B)
    -- the parameters
    (hrank : Lax3.FirstOrder.rank φ ≤ q_top) (hcap : cap = rhoMinus 0 q_top)
    (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBoundK B n Kmass ns cap mb) (hWB : n + W + 1 < B) (hnsW : ns ≤ W)
    (hpow : 2 ^ sigL cap mb ℓ < B)
    -- the mathematics of the campaign
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    -- the value bounds and the costs, at the compacted count
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n (dedupNs x) σs.t ≤ Kb)
    (hcostI : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j)
    (hKsc : ∀ j < ℓ, Ki j * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc j)
    (hKmono : ∀ j, Monotone (Kl j))
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      Lax3Proofs.RamDriverRoot.turnCostSize n (dedupNs x) cap mb q_top j φ (Ksc j) t
        (Kl (j + 1) t) ≤ Ks j t)
    (hKbase : ∀ m, RamDriverBot.baseCost q_top cap mb ℓ n φ ≤ Kl ℓ m)
    (hKo : ∀ j m, RamDriverCompose.orderPhaseCost n (dedupNs x) W ≤ Ko j m)
    (hKc : ∀ j m, RamDriverCompose.coverPhaseCost n (dedupNs x) ≤ Kc j m)
    (hKd : ∀ j m, Refine.DeadSweep.sweepCost q_top cap mb j n φ ≤ Kd j m)
    (hbinj : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (mm : ℕ),
      RamCover.CoverOut G M π ord cap mm Xoff Xmem asg → Refine.MassMath.BlockInj n Xoff Xmem)
    (hdeg : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n),
      (Lax12.ColoringNumbers.wreach (RamBfs.masked G M) π (2 * cap) v).ncard ≤ Kmass)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m)
    (hKdec : decodeCost n ns + dedupCost n ns + 4 ≤ Kdec)
    (hatoms : ∀ s ∈ (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2,
      s.r + 1 < B ∧ s.t < B ∧ RamDriverIO.atomCost n (dedupNs x) s.t ≤ Kb₀)
    (hKsent : Kb₀ * (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2.length + 1 +
      (1 + (RamDriverIO.sentenceExpr q_top cap mb φ).size) ≤ Ksent) :
    Spec B (fun σ => DecodeMem n ns W σ ∧ LevelMem B n cap mb σ ∧ DepthMem n cap mb σ ∧
        OrderMem B n 0 W σ ∧ DedupMem n σ ∧ TablesSized q_top cap mb φ n σ ∧
        BaseArrs B q_top cap mb ℓ φ σ ∧ σ.inp = x ∧ σ.out = [])
      (driverRootD q_top cap mb 0 ℓ φ)
      (fun _ σ' => σ'.out = [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
      (Kdec + (Kl 0 (n + dedupNs x) + Ksent)) := by
  have hnsle : dedupNs x ≤ ns := by
    rw [hns]
    exact Lax3Proofs.RamDriverDedup.dedupNs_le hx.vertexCount_eq hx.offset_zero
      hx.offset_last hx.offset_mono
  have hBD : WordBoundK B n Kmass (dedupNs x) cap mb := wordBoundK_anti hnsle hB
  refine driverD_correct hrank hB hxB (by omega) hnsW
    (decodeImplementsDL hx hns (by rw [decodeDLCost]; omega))
    (fun M Gm C hall => ?_)
    (fun M Gm C => RamDriverIO.sentenceImplements hrank
      (Lax3Proofs.RamDriverDedup.csrGraph_dedup hx) hatoms hKsent)
  have h := Lax3Proofs.RamDriverRoot.levelAt (ns := dedupNs x) (O := dedupOffset x)
    (T := dedupTarget x) hcap hmb hℓ hBD hWB hpow
    (Lax3Proofs.RamDriverDedup.csrSimple_dedup hx) hQ hbnd hcostI hKsc hKmono hKs hKbase
    hKo hKc hKd hbinj hdeg hKl 0 (Nat.zero_le ℓ) M Gm C
  rwa [Refine.MassWeight.arenaWeight_root (Lax3Proofs.RamDriverDedup.csrSimple_dedup hx)
    hall] at h

open Classical in
/-- **The restated root at general `R`** — the same statement with the
level leg from `levelAtR`. The every-permutation `hdeg` slot is
**gone**: the degree enters through the ordering slot's value
`DegOrder n G cap Kmass`, which the per-π producer chain
(`exists_wreachDeg_of_orderP` → `degOrder_of_orderP_alive`, with
`Kmass := ⌈c·n^δ⌉₊` and the `3·t ≤ R` round shape chosen at the
producer) closes at the root's all-alive arena. The named residuals of
the assembly — `horder`, `hfr`, `hptr`/`hexit` — are hypotheses (see
`levelAtR`); every other slot is the `R = 0` sibling's. -/
theorem driverRootD_decides_sentenceR
    -- the input word
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hxB : ∀ v ∈ x, v < B)
    -- the parameters
    (hrank : Lax3.FirstOrder.rank φ ≤ q_top) (hcap : cap = rhoMinus 0 q_top)
    (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBoundK B n Kmass ns cap mb) (hWB : n + W + 1 < B) (hnsW : ns ≤ W)
    (hpow : 2 ^ sigL cap mb ℓ < B)
    -- the mathematics of the campaign
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    -- the value bounds and the costs, at the compacted count
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n (dedupNs x) σs.t ≤ Kb)
    (hcostI : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j)
    (hKsc : ∀ j < ℓ, Ki j * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc j)
    (hKmono : ∀ j, Monotone (Kl j))
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      Lax3Proofs.RamDriverRoot.turnCostSize n (dedupNs x) cap mb q_top j φ (Ksc j) t
        (Kl (j + 1) t) ≤ Ks j t)
    (hKbase : ∀ m, RamDriverBot.baseCost q_top cap mb ℓ n φ ≤ Kl ℓ m)
    (hKo : ∀ j m, RamDriverCompose.orderPhaseCostR n (dedupNs x) W R ≤ Ko j m)
    (hKc : ∀ j m, RamDriverCompose.coverPhaseCost n (dedupNs x) ≤ Kc j m)
    (hKd : ∀ j m, Refine.DeadSweep.sweepCost q_top cap mb j n φ ≤ Kd j m)
    (hbinj : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (mm : ℕ),
      RamCover.CoverOut G M π ord cap mm Xoff Xmem asg → Refine.MassMath.BlockInj n Xoff Xmem)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m)
    (hKdec : decodeCost n ns + dedupCost n ns + 4 ≤ Kdec)
    (hatoms : ∀ s ∈ (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2,
      s.r + 1 < B ∧ s.t < B ∧ RamDriverIO.atomCost n (dedupNs x) s.t ≤ Kb₀)
    (hKsent : Kb₀ * (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2.length + 1 +
      (1 + (RamDriverIO.sentenceExpr q_top cap mb φ).size) ≤ Ksent)
    -- the named residuals of the general-`R` assembly (see `levelAtR`)
    (horder : ∀ j < ℓ, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      OrderImplements B n R W cap mb (dedupNs x) j G (dedupOffset x)
        (dedupTarget x) M Gm C (DegOrder n G cap Kmass)
        (RamDriverCompose.orderPhaseCostR n (dedupNs x) W R))
    (hfr : RFrames q_top cap mb R ℓ φ)
    (hptr : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ),
      RamCover.OrdersBy n π ord → RamDriver.PtrWords B G M π ord cap)
    (hexit : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ),
      RamCover.OrdersBy n π ord → RamDriver.MassWords B G M π ord cap) :
    Spec B (fun σ => DecodeMem n ns W σ ∧ LevelMem B n cap mb σ ∧ DepthMem n cap mb σ ∧
        OrderMem B n 0 W σ ∧ DedupMem n σ ∧ TablesSized q_top cap mb φ n σ ∧
        BaseArrs B q_top cap mb ℓ φ σ ∧ σ.inp = x ∧ σ.out = [])
      (driverRootD q_top cap mb R ℓ φ)
      (fun _ σ' => σ'.out = [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
      (Kdec + (Kl 0 (n + dedupNs x) + Ksent)) := by
  have hnsle : dedupNs x ≤ ns := by
    rw [hns]
    exact Lax3Proofs.RamDriverDedup.dedupNs_le hx.vertexCount_eq hx.offset_zero
      hx.offset_last hx.offset_mono
  have hBD : WordBoundK B n Kmass (dedupNs x) cap mb := wordBoundK_anti hnsle hB
  refine driverD_correct hrank hB hxB (by omega) hnsW
    (decodeImplementsDL hx hns (by rw [decodeDLCost]; omega))
    (fun M Gm C hall => ?_)
    (fun M Gm C => RamDriverIO.sentenceImplements hrank
      (Lax3Proofs.RamDriverDedup.csrGraph_dedup hx) hatoms hKsent)
  have h := levelAtR (ns := dedupNs x) (O := dedupOffset x)
    (T := dedupTarget x) hcap hmb hℓ hBD hWB hpow
    (Lax3Proofs.RamDriverDedup.csrSimple_dedup hx) hptr hexit hQ hbnd hcostI hKsc hKmono hKs
    hKbase hKo hKc hKd hbinj hKl horder hfr 0 (Nat.zero_le ℓ) M Gm C
  rwa [Refine.MassWeight.arenaWeight_root (Lax3Proofs.RamDriverDedup.csrSimple_dedup hx)
    hall] at h

open Classical in
/-- The plug check for the restated precondition: `RootPreD` is the
`R = 0` root's precondition verbatim. -/
theorem driverRootD_decides_sentence_pre
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hxB : ∀ v ∈ x, v < B)
    (hrank : Lax3.FirstOrder.rank φ ≤ q_top) (hcap : cap = rhoMinus 0 q_top)
    (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBoundK B n Kmass ns cap mb) (hWB : n + W + 1 < B) (hnsW : ns ≤ W)
    (hpow : 2 ^ sigL cap mb ℓ < B)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n (dedupNs x) σs.t ≤ Kb)
    (hcostI : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j)
    (hKsc : ∀ j < ℓ, Ki j * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc j)
    (hKmono : ∀ j, Monotone (Kl j))
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      Lax3Proofs.RamDriverRoot.turnCostSize n (dedupNs x) cap mb q_top j φ (Ksc j) t
        (Kl (j + 1) t) ≤ Ks j t)
    (hKbase : ∀ m, RamDriverBot.baseCost q_top cap mb ℓ n φ ≤ Kl ℓ m)
    (hKo : ∀ j m, RamDriverCompose.orderPhaseCost n (dedupNs x) W ≤ Ko j m)
    (hKc : ∀ j m, RamDriverCompose.coverPhaseCost n (dedupNs x) ≤ Kc j m)
    (hKd : ∀ j m, Refine.DeadSweep.sweepCost q_top cap mb j n φ ≤ Kd j m)
    (hbinj : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (mm : ℕ),
      RamCover.CoverOut G M π ord cap mm Xoff Xmem asg → Refine.MassMath.BlockInj n Xoff Xmem)
    (hdeg : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n),
      (Lax12.ColoringNumbers.wreach (RamBfs.masked G M) π (2 * cap) v).ncard ≤ Kmass)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m)
    (hKdec : decodeCost n ns + dedupCost n ns + 4 ≤ Kdec)
    (hatoms : ∀ s ∈ (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2,
      s.r + 1 < B ∧ s.t < B ∧ RamDriverIO.atomCost n (dedupNs x) s.t ≤ Kb₀)
    (hKsent : Kb₀ * (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2.length + 1 +
      (1 + (RamDriverIO.sentenceExpr q_top cap mb φ).size) ≤ Ksent) :
    Spec B (RootPreD B n ns W q_top cap mb ℓ φ x)
      (driverRootD q_top cap mb 0 ℓ φ)
      (fun _ σ' => σ'.out = [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
      (Kdec + (Kl 0 (n + dedupNs x) + Ksent)) :=
  driverRootD_decides_sentence hx hns hxB hrank hcap hmb hℓ hB hWB hnsW hpow hQ hbnd
    hcostI hKsc hKmono hKs hKbase hKo hKc hKd hbinj hdeg hKl hKdec hatoms hKsent

end Main

/-! ## §6 The kills, compiled -/

/-! ### #6 `hcsr` is dead at the restated root

Structurally: `driverRootD_decides_sentence` *has no* `CsrSimple`
hypothesis — the slot's producer is `csrSimple_dedup`, consumed inside
the proof. The sweep's obstruction and the restated root's data meet at
one witness below: the very word at which the landed slot is refuted
carries the compacted triple's `CsrSimple`. -/

/-- **Slot #6, killed.** At the sweep's own witness the landed root's
`hcsr` reading is false and the restated root's reading holds — the same
graph, the two triples. -/
theorem slot06_dead_at_D :
    ∃ (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)),
      EncodesGraph x n G ∧
        ¬ RamElim.CsrSimple G (2 * edgeCount x) (offset x) (target x) ∧
        RamElim.CsrSimple G (dedupNs x) (dedupOffset x) (dedupTarget x) := by
  obtain ⟨x, n, G, hx, hnot⟩ := Lax3Proofs.C0Probe.encodesGraph_not_csrSimple
  exact ⟨x, n, G, hx, hnot, Lax3Proofs.RamDriverDedup.csrSimple_dedup hx⟩

/-! ### #26 `hdeg` is dead at the restated slot shape

`SlotSweep` §C: the landed slot quantifies over *every* permutation,
and at `starLast n` with the centre ordered last it forces
`n ≤ Kmass` — so no constant chosen before the instance serves
(`slot26_hdeg_blocked`, untouched). The restated slot demands the bound
only at orderings carrying `RamDriverCompose.OrderP`, and the chain
bundle *excludes* the adversarial ordering: at `R = 0` the bundle
degenerates to the two elimination bounds
(`CoverDegree.augChainData_zero`), the sub-star's elimination form of
degeneracy is `1` (`lowDegreeVertices_substar`), so any `OrderP`-carrying
ordering has back-degree `1` at every vertex — and then every weakly
reachable set has at most three elements, at **every** radius. The flip
is `slot26_dead_at_R`: a constant (`3`) chosen before `n` satisfies the
restated slot shape on the whole star family, the C0 quantifier order
the sweep's `¬∃` refutes for the landed shape. The negative control
`not_orderP_starLast_id` checks the guard is doing the work: the
sweep's own refuting tuple — the identity ordering — carries no
`OrderP`. -/

section Star

open Lax12.ColoringNumbers (wreach)
open Lax3Proofs.Refine.SlotSweep (starLast centre centre_val le_centre adj_centre)
open Lax3Proofs.Augmentation

variable {n : ℕ}

/-- An orientation's graph is the graph it orients. -/
theorem toGraph_eq_of_orients {D : Orientation n} {G' : SimpleGraph (Fin n)}
    (h : D.Orients G') : D.toGraph = G' := by
  ext u v
  rw [Orientation.toGraph_adj]
  exact (h u v).symm

/-- Every edge of a masked star touches the centre. -/
theorem masked_star_touches_centre {M : ℕ → ℕ} {u v : Fin n} (hn : 0 < n)
    (h : (masked (starLast n) M).Adj u v) : u = centre n hn ∨ v = centre n hn := by
  obtain ⟨⟨-, hor⟩, -, -⟩ := RamBfs.masked_adj.mp h
  rcases hor with hu | hv
  · exact Or.inl (Fin.ext (by have := centre_val hn; omega))
  · exact Or.inr (Fin.ext (by have := centre_val hn; omega))

/-- **A masked star's elimination form of degeneracy is `1`**: every
nonempty vertex set carries a vertex with at most one neighbour inside
it — a non-centre if there is one, whose only possible neighbour is the
centre, and the centre alone otherwise. -/
theorem lowDegreeVertices_substar (M : ℕ → ℕ) :
    LowDegreeVertices (masked (starLast n) M) 1 := by
  intro S hS
  obtain ⟨v₀, hv₀⟩ := hS
  have hn : 0 < n := v₀.pos
  by_cases hex : ∃ u ∈ S, u ≠ centre n hn
  · obtain ⟨u, huS, huc⟩ := hex
    refine ⟨u, huS, ?_⟩
    have hsub : nbrsIn (masked (starLast n) M) S u ⊆ {centre n hn} := by
      intro w hw
      obtain ⟨-, hadj⟩ := mem_nbrsIn.mp hw
      rcases masked_star_touches_centre hn hadj with hwc | huc'
      · simpa using hwc
      · exact absurd huc' huc
    simpa using Finset.card_le_card hsub
  · have hex' : ∀ u ∈ S, u = centre n hn := by
      intro u hu
      by_contra hne
      exact hex ⟨u, hu, hne⟩
    refine ⟨v₀, hv₀, ?_⟩
    have hsub : nbrsIn (masked (starLast n) M) S v₀ ⊆ ∅ := by
      intro w hw
      obtain ⟨hwS, hadj⟩ := mem_nbrsIn.mp hw
      rw [hex' w hwS, hex' v₀ hv₀] at hadj
      exact absurd hadj (masked (starLast n) M).irrefl
    calc (nbrsIn (masked (starLast n) M) S v₀).card
        ≤ (∅ : Finset (Fin n)).card := Finset.card_le_card hsub
      _ ≤ 1 := by simp

/-- **The chain bundle forces back-degree `1` on a masked star.** At
`R = 0` the bundle's final graph is the arena itself, its back-degree
witness `k` is squeezed under the elimination form of degeneracy, and
the sub-star's is `1`. -/
theorem backDegLE_of_orderP_star {M : ℕ → ℕ} {π : Equiv.Perm (Fin n)} {ord : ℕ → ℕ}
    (h : RamDriverCompose.OrderP 0 (starLast n) M π ord) :
    BackDegLE (masked (starLast n) M) (fun v => ((π v : Fin n) : ℕ)) 1 := by
  obtain ⟨D, d₀, k, hchain, -, -, -, hback, hkmin⟩ := h
  have htg : (D 0).toGraph = masked (starLast n) M := toGraph_eq_of_orients hchain.1
  have hk1 : k ≤ 1 := hkmin 1 (by rw [htg]; exact lowDegreeVertices_substar M)
  intro v
  have hb := hback v
  rw [htg] at hb
  exact le_trans hb hk1

/-- **Weak reachability under a back-degree-`1` star ordering is at most
three, at every radius**: the vertex itself, the centre, and the at most
one leaf below the centre — every walk of a star crosses the centre with
its first step, so nothing else can be `π`-minimal on a walk's
support. -/
theorem wreach_le_of_backDegLE_star {M : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    (hb : BackDegLE (masked (starLast n) M) (fun v => ((π v : Fin n) : ℕ)) 1)
    (r : ℕ) (v : Fin n) :
    (wreach (masked (starLast n) M) π r v).ncard ≤ 3 := by
  classical
  have hn : 0 < n := v.pos
  set c := centre n hn with hc
  have hsub : wreach (masked (starLast n) M) π r v ⊆
      insert v (insert c {u | (masked (starLast n) M).Adj u c ∧
        ((π u : Fin n) : ℕ) < ((π c : Fin n) : ℕ)}) := by
    rintro u ⟨w, -, hmin⟩
    by_cases huv : u = v
    · exact Or.inl huv
    by_cases huc : u = c
    · exact Or.inr (Or.inl huc)
    right; right
    -- the reversed walk leaves `u` along an edge, and every edge
    -- touches the centre
    cases hw : w.reverse with
    | nil => exact absurd rfl huv
    | cons hadj p =>
        rename_i y
        have hyc : y = c := by
          rcases masked_star_touches_centre hn hadj with h | h
          · exact absurd h huc
          · exact h
        subst hyc
        have hcs : c ∈ w.support := by
          have hcr : c ∈ w.reverse.support := by
            rw [hw]
            exact List.mem_cons_of_mem _ p.start_mem_support
          rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hcr
        have hle : (π u : ℕ) ≤ (π c : ℕ) := Fin.le_def.mp (hmin c hcs)
        have hne : (π u : ℕ) ≠ (π c : ℕ) := fun hh => huc (π.injective (Fin.ext hh))
        exact ⟨hadj, by omega⟩
  have hbc : ({u | (masked (starLast n) M).Adj u c ∧
      ((π u : Fin n) : ℕ) < ((π c : Fin n) : ℕ)} : Set (Fin n)).ncard ≤ 1 := hb c
  calc (wreach (masked (starLast n) M) π r v).ncard
      ≤ (insert v (insert c {u | (masked (starLast n) M).Adj u c ∧
          ((π u : Fin n) : ℕ) < ((π c : Fin n) : ℕ)})).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (insert c {u | (masked (starLast n) M).Adj u c ∧
          ((π u : Fin n) : ℕ) < ((π c : Fin n) : ℕ)}).ncard + 1 :=
        Set.ncard_insert_le _ _
    _ ≤ ({u | (masked (starLast n) M).Adj u c ∧
          ((π u : Fin n) : ℕ) < ((π c : Fin n) : ℕ)}).ncard + 1 + 1 :=
        Nat.add_le_add_right (Set.ncard_insert_le _ _) 1
    _ ≤ 3 := by omega

/-- **Slot #26, killed at the restated shape.** A constant chosen before
the instance satisfies the conditional slot on the sweep's whole
refuting family, at every mask, every radius and every vertex — the
exact quantifier order whose landed (unconditional) form
`slot26_hdeg_blocked` refutes. -/
theorem slot26_dead_at_R :
    ∃ Kmass : ℕ, ∀ (n r : ℕ) (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ),
      RamDriverCompose.OrderP 0 (starLast n) M π ord →
      ∀ v : Fin n, (wreach (masked (starLast n) M) π r v).ncard ≤ Kmass :=
  ⟨3, fun _n r _M _π _ord hP v =>
    wreach_le_of_backDegLE_star (backDegLE_of_orderP_star hP) r v⟩

/-- **The negative control — the guard does the work.** The sweep's own
refuting tuple (the identity ordering, everything alive) carries no
`OrderP`: the centre sits last, so its back-degree is `n - 1`, over the
bundle's forced `1` as soon as `n ≥ 3`. This is why
`deg_slot_at_starLast`'s forcing cannot arise at the restated slot: the
instantiation it needs is outside the guard. -/
theorem not_orderP_starLast_id (hn : 3 ≤ n) (ord : ℕ → ℕ) :
    ¬ RamDriverCompose.OrderP 0 (starLast n) (fun _ => 1) 1 ord := by
  intro h
  have hn0 : 0 < n := by omega
  have hcv := centre_val hn0
  have hb : ({u | (masked (starLast n) (fun _ => 1)).Adj u (centre n hn0) ∧
      (((1 : Equiv.Perm (Fin n)) u : Fin n) : ℕ) <
        (((1 : Equiv.Perm (Fin n)) (centre n hn0) : Fin n) : ℕ)} : Set (Fin n)).ncard ≤ 1 :=
    backDegLE_of_orderP_star h (centre n hn0)
  have hmem : ∀ u : Fin n, u ≠ centre n hn0 →
      u ∈ {u | (masked (starLast n) (fun _ => 1)).Adj u (centre n hn0) ∧
        (((1 : Equiv.Perm (Fin n)) u : Fin n) : ℕ) <
          (((1 : Equiv.Perm (Fin n)) (centre n hn0) : Fin n) : ℕ)} := by
    intro u huc
    refine ⟨(adj_centre hn0 (fun _ => one_ne_zero) huc).symm, ?_⟩
    simp only [Equiv.Perm.coe_one, id_eq]
    have h1 : (u : ℕ) ≤ ((centre n hn0 : Fin n) : ℕ) := Fin.le_def.mp (le_centre hn0 u)
    have h2 : (u : ℕ) ≠ ((centre n hn0 : Fin n) : ℕ) := fun hh => huc (Fin.ext hh)
    omega
  have hu₀ : (⟨0, hn0⟩ : Fin n) ≠ centre n hn0 := by
    intro hh
    simp only [centre, Fin.mk.injEq] at hh
    omega
  have hu₁ : (⟨1, by omega⟩ : Fin n) ≠ centre n hn0 := by
    intro hh
    simp only [centre, Fin.mk.injEq] at hh
    omega
  have htwo : ({(⟨0, hn0⟩ : Fin n), (⟨1, by omega⟩ : Fin n)} : Set (Fin n)) ⊆
      {u | (masked (starLast n) (fun _ => 1)).Adj u (centre n hn0) ∧
        (((1 : Equiv.Perm (Fin n)) u : Fin n) : ℕ) <
          (((1 : Equiv.Perm (Fin n)) (centre n hn0) : Fin n) : ℕ)} := by
    rintro u (rfl | rfl)
    · exact hmem _ hu₀
    · exact hmem _ hu₁
  have h2 : ({(⟨0, hn0⟩ : Fin n), (⟨1, by omega⟩ : Fin n)} : Set (Fin n)).ncard = 2 :=
    Set.ncard_pair (Fin.ne_of_val_ne (by norm_num))
  have hcard : 2 ≤ ({u | (masked (starLast n) (fun _ => 1)).Adj u (centre n hn0) ∧
      (((1 : Equiv.Perm (Fin n)) u : Fin n) : ℕ) <
        (((1 : Equiv.Perm (Fin n)) (centre n hn0) : Fin n) : ℕ)} : Set (Fin n)).ncard := by
    rw [← h2]
    exact Set.ncard_le_ncard htwo (Set.toFinite _)
  omega

end Star

/-! ### #12 `hB` follows: the word bound no longer degenerates

`SlotSweep.wordBound_of_deg_slot` (untouched, still true): where the
degree slot forces `n ≤ Kmass`, `WordBoundK` collapses to the retired
carrier bound and `BridgeSeamProbe.no_word_size_for_sparse` kills the
bridge again. At the restated slot the producer's constant is
`⌈c · n^δ⌉₊` with `c` and `δ < 1` chosen before `n` — and past a
threshold of the two, that is *below* `n`, so the collapse's hypothesis
fails at every large instance and `WordBoundK` stays the almost-linear
bound `Refine.BridgeCrossing` crossed. -/

section Sublinear

open Filter

/-- A sub-linear ceiling: `⌈c · n^δ⌉₊ < n` for every large `n`, at every
constant `c` and every exponent `δ < 1` — both chosen first, as C0
chooses them. -/
theorem kmass_sublinear (c δ : ℝ) (hδ : δ < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ⌈c * (n : ℝ) ^ δ⌉₊ < n := by
  have h0 : Tendsto (fun x : ℝ => x ^ (δ - 1)) atTop (nhds 0) := by
    have := tendsto_rpow_neg_atTop (y := 1 - δ) (by linarith)
    simpa [neg_sub] using this
  have h1 : Tendsto (fun x : ℝ => c * x ^ (δ - 1)) atTop (nhds 0) := by
    simpa using h0.const_mul c
  have h2 : ∀ᶠ x : ℝ in atTop, c * x ^ (δ - 1) < 1 / 2 :=
    h1.eventually_lt_const (by norm_num)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp h2
  refine ⟨max ⌈x₀⌉₊ 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hxn : x₀ ≤ (n : ℝ) := by
    calc x₀ ≤ (⌈x₀⌉₊ : ℝ) := Nat.le_ceil x₀
      _ ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hn
  have hlt : c * (n : ℝ) ^ (δ - 1) < 1 / 2 := hx₀ (n : ℝ) hxn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hpow : c * (n : ℝ) ^ δ = c * (n : ℝ) ^ (δ - 1) * (n : ℝ) := by
    rw [mul_assoc, ← Real.rpow_add_one (ne_of_gt hnpos) (δ - 1)]
    norm_num
  have hmul : c * (n : ℝ) ^ δ < (n : ℝ) / 2 := by
    rw [hpow]
    have := mul_lt_mul_of_pos_right hlt hnpos
    linarith
  have hle : c * (n : ℝ) ^ δ ≤ ((n - 1 : ℕ) : ℝ) := by
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcast]
    have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    nlinarith
  have hceil : ⌈c * (n : ℝ) ^ δ⌉₊ ≤ n - 1 := Nat.ceil_le.mpr hle
  omega

/-- **Slot #12, non-degenerate at the restated slot.** With the
producer's constant `⌈c · n^δ⌉₊` (`δ < 1`, both chosen before `n`),
`wordBound_of_deg_slot`'s collapse hypothesis `n ≤ Kmass` fails at every
large instance: the route from the restated root's `hB` back to the
retired carrier bound is closed. -/
theorem slot12_hB_nondegenerate (c δ : ℝ) (hδ : δ < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ (n ≤ ⌈c * (n : ℝ) ^ δ⌉₊) := by
  obtain ⟨N, hN⟩ := kmass_sublinear c δ hδ
  exact ⟨N, fun n hn h => absurd h (Nat.not_le.mpr (hN n hn))⟩

end Sublinear

/-! ## §7 The axiom check -/

#print axioms decode_spec_lw0
#print axioms decodeImplementsDL
#print axioms restated_pre_initEnv_where_landed_is_not
#print axioms levelAtR
#print axioms no_guard_instance
#print axioms driverRootD_decides_sentence
#print axioms driverRootD_decides_sentenceR
#print axioms slot06_dead_at_D
#print axioms slot26_dead_at_R
#print axioms not_orderP_starLast_id
#print axioms slot12_hB_nondegenerate

end Lax3Proofs.Refine.DriverRootD
