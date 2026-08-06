import Lax3Proofs.Refine.OrderBlockProbe
import Lax3Proofs.Refine.G2ExistsRevalidation
import Lax3Proofs.Refine.CoverBlock

/-!
# E-mem-design — the member-list clause of `LevelPre`, compiled both ways

R1.6, the road's last design gate before the order/cover re-synthesis:
thread a per-depth member list into the driver's level state, so the
member-driven engine family (`OrderSigProbeM`'s measured `68·m + 12`
phase, `ScatterBlock`'s block engines) has something to drive it. This
file is the design's compiled half; the design document is
`plans/nowhere-dense-model-checking/e-mem-design.md`. **Nothing here
edits a landed declaration** — `LevelPreM` is a standalone `Prop` of
this namespace that *references* `RamDriver.LevelPre`, and every
program is a probe shape.

What is compiled, in the two directions the standing rule asks for:

* **Existence** (§3). The proposed clause is inhabited by driver-shaped
  machines: a root-shaped `Env` (all-alive mask, identity member list)
  satisfies `LevelPreM` at depth 0, and the SAME `Env` after a
  descend-like update — the child masks, the child member list, the
  child count, written with `Env.setArr`/`Env.setVar` exactly as
  `descendCom`'s stores would — satisfies it at depth 1
  (`levelPreM_root`, `levelPreM_child`). The `n = 0` control
  (`memClause_zero_carrier`) is the flip-gate hazard check: the clause
  stays satisfiable on the empty input word, which is why it carries
  **no** tail-content conjunct (a zero-tail would also force producers
  to clear junk tails — a touched-only violation).
* **The `∃`-packaging is lossless** (§2): `memList_unique` — two member
  lists of the same mask agree in count and content on the live
  prefix — so the clause can be carried existentially (the `DepthMem`
  idiom), leaving `LevelPre`'s *signature* unchanged and the blast
  radius at destructurings + frame lemmas only.
* **Producer cost, positive** (§4): the member-emission add-on on the
  landed `clusterLoad` shape (`clusterLoadM` — one store and one
  counter bump inside the existing block scan) and the child filter
  pass (`memFilterCom` — the block list against the child mask, in
  place) are both charged at the BLOCK: their clocks on
  `TgtWidenProbe.execC` are pinned equal at carriers 100 and 200 and
  linear in the block size. The emission preserves the block order and
  the filter is stable, so sortedness flows down from the parent's
  emission order (`emitLoop` walks the carrier in index order — the
  supply of `MemList.smono`, see the design doc §3).
* **Producer cost, negative** (§4): `memFromMaskCom` — building the
  list from the mask alone — is a carrier scan: its clock GROWS by
  `9` per carrier vertex between the same two carriers at a fixed
  two-member arena. This is `OrderBlockProbe`'s prose claim ("building
  it from the mask is itself a carrier scan"), made compiled. And
  `unsorted_emission_refuted`: a BFS-ordered (unsorted) block emission
  cannot feed the clause — `MemList.smono` fails on data — which pins
  the E3 interaction recorded in the design doc.
* **Consumer direction** (§5): the copy-into-fixed-name convention at
  the LIVE PREFIX — `copyUpto (memName j) "mem" (.var "mm")`, the
  `CoverBlock.memCopy_spec` leaf shape at `memCopyK mm = 12·mm + 6` —
  composed with the landed member-driven engine
  `ScatterBlock.clearMem`, runs carrier-blind: equal clocks at
  carriers 100 and 200, exactly the member cells moved. NOT
  `copyCom`'s carrier-width copy: the fixed-`n` copy is one of the
  walks G2 kills.
* **Floor-death** (§6): with the member clause available, the §1
  order-text floor of `OrderBlockProbe` is escapable — the measured
  member-driven phase clock `phaseClockK` fits `orderCostA` read at
  the arena weight where the landed text's clock refutes it
  (`memPhase_escapes_floor`), the nested empty-charge floor is defused
  at the measured constant `12` (`#guard` at the `10¹¹` numerals of
  `emptyCharge_route_dead`), and the whole interface arithmetic closes
  at the measured constants by `G2ExistsRevalidation.g2m_exists`,
  cited and instantiated, not re-derived
  (`memPhase_interface_closes`).
-/

namespace Lax3Proofs.Refine.MemThreadProbe

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamDriver (alvName gamName cluName resName balName balAltName batName
  ordName xofName xmmName asgName cpsName colName curName exists_arrOf Sized DepthMem
  LevelMem OrderMem LevelPre clusterLoad fillCom copyUpto)
open Lax3Proofs.RamDriverCluster (markSet mem_markSet)
open Lax3Proofs.Refine.ScatterBlock (MemList MemOf)
open Lax3Proofs.TgtWidenProbe (execC pB pF PSt)

/-! ## §1 The two proposed names

The `cpsName`/`cnumName` precedent (`RamDriver.lean:807/811`) at the
`alvName → "alv"` copy pattern: the per-depth name is the fixed engine
name plus the depth's numeral. -/

/-- The member list of the arena at depth `j`: the alive vertices of
`alvName j`, in strictly increasing order, in the first `mnumName j`
cells; the tail is junk. Fixed physical length `n` (E29: pre-allocated
once with the rest of `DepthMem`, never re-allocated). -/
def memName (j : ℕ) : String := "mem" ++ toString j

/-- The member count of depth `j`: the length of the live prefix. -/
def mnumName (j : ℕ) : String := "mm" ++ toString j

-- freshness against the copy targets: the per-depth names are not the
-- fixed engine names they copy into
example : memName 0 ≠ "mem" := by decide
example : mnumName 0 ≠ "mm" := by decide
example (j : ℕ) : memName j ≠ "mem" := by
  simp [memName, String.ext_iff]
example (j : ℕ) : mnumName j ≠ "mm" := by
  simp [mnumName, String.ext_iff]
-- and against the nearest existing names
example (j k : ℕ) : memName j ≠ xmmName k := by
  simp [memName, xmmName, String.ext_iff]
example (j : ℕ) : memName j ≠ "xmem" := by
  simp [memName, String.ext_iff]

/-! ## §2 The proposed clause, and why the `∃`-form loses nothing -/

/-- **The `DepthMem` delta**: the member array of every depth is there
at length `n`. In the real threading this is a 13th entry
`(memName j, n)` in `DepthMem`'s `Sized` list; stated standalone here
so no landed `Prop` is touched. -/
def DepthMemM (n : ℕ) (σ : Env) : Prop :=
  ∀ j : ℕ, ∃ g : ℕ → ℕ, σ.arrs (memName j) = arrOf n g

/-- **The proposed 16th clause of `LevelPre`** (appended, so the
positional `⟨h1, …⟩` destructurings repair by one added component): the
depth's member list enumerates the depth's own mask, existentially.

The four conjuncts: the array at its fixed length `n`, the count
scalar, `MemList` against `markSet n M` (sound, complete, strictly
increasing — `Refine/ScatterBlockProg.lean`'s contract), and the word
clause on the whole physical array (the live prefix is already below
`n < B`; the junk tail needs its own bound to survive re-statement, and
carries NO content clause — see `memClause_zero_carrier`). -/
def MemClause (B n j : ℕ) (M : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ (Mem : ℕ → ℕ) (mmj : ℕ),
    σ.arrs (memName j) = arrOf n Mem ∧ σ.vars (mnumName j) = mmj ∧
    MemList n mmj Mem (markSet n M) ∧ ∀ z, z < n → Mem z < B

/-- **`LevelPre` with the member clause** — the proposed shape, stated
over the landed `LevelPre` without editing it. The real threading
appends `MemClause`'s body as clause 16 and puts `(memName j, n)` into
`DepthMem`'s list; `levelPre_run` gains `memName j ∉ c.warrs` and
`mnumName j ∉ c.wvars`. -/
def LevelPreM (B n cap mb ns W : ℕ) (O T : ℕ → ℕ) (j : ℕ) (M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (σ : Env) : Prop :=
  LevelPre B n cap mb ns W O T j M Gm C σ ∧ DepthMemM n σ ∧ MemClause B n j M σ

/-- **The `∃`-packaging is lossless.** Two member lists of the same set
agree in count and, cell for cell, on the live prefix: a strictly
increasing sound-and-complete enumeration is unique. This is what lets
the clause ride inside `LevelPre` without new `LevelPre` parameters —
consumers that destructure the `∃` at two program points always
extract the same list. -/
theorem memList_unique {n mm mm' : ℕ} {Mem Mem' : ℕ → ℕ} {X : Set (Fin n)}
    (h : MemList n mm Mem X) (h' : MemList n mm' Mem' X) :
    mm = mm' ∧ ∀ k, k < mm → Mem k = Mem' k := by
  have key : ∀ k, k < mm → k < mm' → Mem k = Mem' k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hk'
      have h1 : Mem k ≤ Mem' k := by
        obtain ⟨i, hi, hMi⟩ := h.complete _ (h'.sound k hk')
        rcases Nat.lt_or_ge i k with hik | hik
        · exact absurd (by rw [← ih i hik (by omega) (by omega), hMi] :
            Mem' i = Mem' k) (Nat.ne_of_lt (h'.smono i k hik hk'))
        · calc Mem k ≤ Mem i := h.mono hik hi
            _ = Mem' k := hMi
      have h2 : Mem' k ≤ Mem k := by
        obtain ⟨i, hi, hMi⟩ := h'.complete _ (h.sound k hk)
        rcases Nat.lt_or_ge i k with hik | hik
        · exact absurd (by rw [ih i hik (by omega) (by omega), hMi] :
            Mem i = Mem k) (Nat.ne_of_lt (h.smono i k hik hk))
        · calc Mem' k ≤ Mem' i := h'.mono hik hi
            _ = Mem k := hMi
      omega
  have hcount : mm = mm' := by
    by_contra hne
    rcases Nat.lt_or_ge mm mm' with hlt | hge
    · obtain ⟨i, hi, hMi⟩ := h.complete _ (h'.sound mm hlt)
      exact absurd (by rw [← key i hi (by omega), hMi] : Mem' i = Mem' mm)
        (Nat.ne_of_lt (h'.smono i mm hi hlt))
    · have hlt : mm' < mm := by omega
      obtain ⟨i, hi, hMi⟩ := h'.complete _ (h.sound mm' hlt)
      exact absurd (by rw [key i (by omega) hi, hMi] : Mem i = Mem mm')
        (Nat.ne_of_lt (h.smono i mm' hi hlt))
  exact ⟨hcount, fun k hk => key k hk (hcount ▸ hk)⟩

/-- **The flip-gate control**: the clause is satisfiable at `n = 0`
(the empty input word, which the driver's value bound admits). This is
the check the F-c-4 padding episode institutionalized: an empty-count
list over the empty mask, with a vacuous word clause — no tail-content
conjunct anywhere to refute. -/
theorem memClause_zero_carrier (M : ℕ → ℕ) :
    MemList 0 0 (fun _ => 0) (markSet 0 M) :=
  ⟨fun j hj => by omega, fun i j _ hj => by omega, fun j hj => by omega,
    fun a ha => absurd ha.1 (by omega)⟩

/-! ## §3 Existence: driver-shaped machines inhabit the clause

The witness world is the two-vertex, zero-edge carrier: `n = 2`,
`ns = W = 0`, `cap = mb = 0`, `B = 4`. Every array of
`LevelMem`/`OrderMem`/`DepthMem` is present at its declared length —
the classifier `len2` says which — so the witness is a whole machine
memory, not a fragment. -/

/-- The declared length of every array name in the witness world
(`n = 2`, `W = 0`, `cap = 0`, `mb = 0`): the `xofName` family and the
`n + 1` scratch at 3, the `xmmName` family and `"xmem"` at `n·n = 4`,
`"path"` at `2·cap + 1 = 1`, the width-`W` and `"wa"` arrays at 0,
everything else — including every per-depth family and the `memName`
family — at `n = 2`. -/
def len2 (a : String) : ℕ :=
  if a.toList.take 2 = ['x', 'f'] then 3
  else if a.toList.take 2 = ['x', 'm'] then 4
  else if a = "xoff" then 3
  else if a ∈ ["off", "doff", "ooff", "gof", "bh", "bv", "bn", "ioff", "noff"] then 3
  else if a = "path" then 1
  else if a ∈ ["tgt", "dtg", "otg", "gtg", "itg", "ntg", "wa"] then 0
  else 2

/-- **The root-shaped witness.** Both vertices alive at depth 0
(`alvName 0 = gamName 0 = [1, 1]`), the member list the identity
enumeration (`memName 0 = [0, 1]`, count 2 — the root list the decode
side emits from the all-ones mask), every other array a zeroed block of
its declared length. -/
def rootEnv : Env :=
  { vars := fun x => if x = "n" then 2 else if x = mnumName 0 then 2 else 0
    arrs := fun a =>
      if a = alvName 0 ∨ a = gamName 0 then [1, 1]
      else if a = memName 0 then [0, 1]
      else List.replicate (len2 a) 0
    inp := [], out := [] }

/-- Every array of the witness has its classified length — including
the three overridden ones, whose contents are length-2 by inspection. -/
theorem rootEnv_length (a : String) : (rootEnv.arrs a).length = len2 a := by
  show (if a = alvName 0 ∨ a = gamName 0 then [1, 1]
      else if a = memName 0 then [0, 1] else List.replicate (len2 a) 0).length = len2 a
  split_ifs with h1 h2
  · rcases h1 with rfl | rfl <;> decide
  · subst h2; decide
  · simp

section FamilyLengths

variable (j c : ℕ)

theorem len2_alvName : len2 (alvName j) = 2 := by
  simp [len2, alvName, String.ext_iff, String.toList_append]
theorem len2_gamName : len2 (gamName j) = 2 := by
  simp [len2, gamName, String.ext_iff, String.toList_append]
theorem len2_cluName : len2 (cluName j) = 2 := by
  simp [len2, cluName, String.ext_iff, String.toList_append]
theorem len2_resName : len2 (resName j) = 2 := by
  simp [len2, resName, String.ext_iff, String.toList_append]
theorem len2_balName : len2 (balName j) = 2 := by
  simp [len2, balName, String.ext_iff, String.toList_append]
theorem len2_balAltName : len2 (balAltName j) = 2 := by
  simp [len2, balAltName, String.ext_iff, String.toList_append]
theorem len2_batName : len2 (batName j) = 2 := by
  simp [len2, batName, String.ext_iff, String.toList_append]
theorem len2_ordName : len2 (ordName j) = 2 := by
  simp [len2, ordName, String.ext_iff, String.toList_append]
theorem len2_xofName : len2 (xofName j) = 3 := by
  simp [len2, xofName, String.toList_append]
theorem len2_xmmName : len2 (xmmName j) = 4 := by
  simp [len2, xmmName, String.toList_append]
theorem len2_asgName : len2 (asgName j) = 2 := by
  simp [len2, asgName, String.ext_iff, String.toList_append]
theorem len2_cpsName : len2 (cpsName j) = 2 := by
  simp [len2, cpsName, String.ext_iff, String.toList_append]
theorem len2_colName : len2 (colName j c) = 2 := by
  simp [len2, colName, String.ext_iff, String.toList_append]
theorem len2_memName : len2 (memName j) = 2 := by
  simp [len2, memName, String.ext_iff, String.toList_append]

end FamilyLengths

/-- The generic-depth arrays of the witness are the zeroed defaults. -/
theorem rootEnv_arrs_of_ne {a : String} (h1 : a ≠ alvName 0) (h2 : a ≠ gamName 0)
    (h3 : a ≠ memName 0) : rootEnv.arrs a = List.replicate (len2 a) 0 := by
  show (if _ then _ else _) = _
  rw [if_neg (by tauto), if_neg h3]

/-- The colour palette of every depth is present (and zero). -/
theorem rootEnv_colName (j c : ℕ) : rootEnv.arrs (colName j c) = arrOf 2 (fun _ => 0) := by
  rw [rootEnv_arrs_of_ne (by simp [colName, alvName, String.ext_iff])
      (by simp [colName, gamName, String.ext_iff])
      (by simp [colName, memName, String.ext_iff]),
    len2_colName]
  decide

/-- The landed `DepthMem`, at the witness: all twelve families of every
depth, at their lengths. -/
theorem depthMem_rootEnv : DepthMem 2 0 0 rootEnv := by
  intro j
  refine ⟨fun p hp => ?_, fun c _ => exists_arrOf ((rootEnv_length _).trans (len2_colName j c))⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exists_arrOf ((rootEnv_length _).trans (len2_alvName j))
  · exact exists_arrOf ((rootEnv_length _).trans (len2_gamName j))
  · exact exists_arrOf ((rootEnv_length _).trans (len2_cluName j))
  · exact exists_arrOf ((rootEnv_length _).trans (len2_resName j))
  · exact exists_arrOf ((rootEnv_length _).trans (len2_balName j))
  · exact exists_arrOf ((rootEnv_length _).trans (len2_balAltName j))
  · exact exists_arrOf ((rootEnv_length _).trans (len2_batName j))
  · exact exists_arrOf ((rootEnv_length _).trans (len2_ordName j))
  · exact exists_arrOf ((rootEnv_length _).trans (len2_xofName j))
  · exact exists_arrOf ((rootEnv_length _).trans (len2_xmmName j))
  · exact exists_arrOf ((rootEnv_length _).trans (len2_asgName j))
  · exact exists_arrOf ((rootEnv_length _).trans (len2_cpsName j))

/-- **The `DepthMem` delta, at the witness**: the member array of every
depth is there at length `n` — the 13th `Sized` entry costs the
allocation story nothing it was not already paying. -/
theorem depthMemM_rootEnv : DepthMemM 2 rootEnv := fun j =>
  exists_arrOf ((rootEnv_length _).trans (len2_memName j))

set_option maxHeartbeats 1000000 in
theorem levelMem_rootEnv : LevelMem 4 2 0 0 rootEnv := by
  refine ⟨fun p hp => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact exists_arrOf ((rootEnv_length _).trans (by decide))
  · rw [rootEnv_arrs_of_ne (by decide) (by decide) (by decide)]; decide
  · rw [rootEnv_arrs_of_ne (by decide) (by decide) (by decide)]; decide

set_option maxHeartbeats 2000000 in
theorem orderMem_rootEnv : OrderMem 4 2 0 0 rootEnv := by
  refine ⟨le_rfl, ⟨by decide, by decide⟩, fun p hp => ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with
      rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact exists_arrOf ((rootEnv_length _).trans (by decide))
  all_goals rw [rootEnv_arrs_of_ne (by decide) (by decide) (by decide)]; decide

set_option maxHeartbeats 400000 in
/-- The landed 15 clauses, at the root witness: depth 0, all-alive
masks, empty palette or zero colours, no slots, zero-width target. -/
theorem levelPre_rootEnv :
    LevelPre 4 2 0 0 0 0 (fun _ => 0) (fun _ => 0) 0 (fun _ => 1) (fun _ => 1)
      (fun _ _ => 0) rootEnv := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    fun c _ => rootEnv_colName 0 c, fun _ _ => (by norm_num : (1 : ℕ) < 4),
    fun _ _ => (by norm_num : (1 : ℕ) < 4), fun _ _ _ _ => Nat.zero_le 1,
    levelMem_rootEnv, depthMem_rootEnv, by decide,
    orderMem_rootEnv, fun z _ hz => absurd hz (Nat.not_lt_zero z),
    fun z hz => absurd hz (Nat.not_lt_zero z)⟩

/-- **Existence, root shape.** A driver-shaped machine memory — the
whole of `LevelPre` at depth 0 — carries the member clause: the
identity list of the all-alive root mask, which is exactly what the
decode side emits (design doc §3, producer P-root). -/
theorem levelPreM_root :
    LevelPreM 4 2 0 0 0 0 (fun _ => 0) (fun _ => 0) 0 (fun _ => 1) (fun _ => 1)
      (fun _ _ => 0) rootEnv := by
  refine ⟨levelPre_rootEnv, depthMemM_rootEnv,
    fun z => z, 2, by decide, by decide, ?_,
    fun z hz => Nat.lt_of_lt_of_le hz (by norm_num)⟩
  exact ⟨fun j hj => hj, fun i j hij _ => hij, fun j hj => ⟨hj, by simp [markSet]⟩,
    fun a ha => ⟨a, ha.1, rfl⟩⟩

/-! ### The child shape, after a descend-like update

`descendCom`'s stores, replayed on the root witness by hand: the child
work mask (`alvName 1` — vertex 1 survives, vertex 0 does not), the
child game mask (`gamName 1` — both), and the two NEW stores the
threading adds: the child member list (`memName 1` — the filtered
block list `[1]`) and the child count (`mnumName 1 = 1`). The witness
is literally an `Env.setArr`/`setVar` chain off `rootEnv`, which is
what makes it descend-shaped rather than merely well-typed. -/

/-- The root witness after the descend-like update. -/
def childEnv : Env :=
  (((((rootEnv.setArr (alvName 1) 1 1).setArr (gamName 1) 0 1).setArr
      (gamName 1) 1 1).setArr (memName 1) 0 1).setVar (mnumName 1) 1)

theorem childEnv_length (a : String) : (childEnv.arrs a).length = len2 a := by
  show ((((((rootEnv.setArr (alvName 1) 1 1).setArr (gamName 1) 0 1).setArr
      (gamName 1) 1 1).setArr (memName 1) 0 1).setVar (mnumName 1) 1).arrs a).length = len2 a
  rw [arrs_setVar, length_arrs_setArr, length_arrs_setArr, length_arrs_setArr,
    length_arrs_setArr]
  exact rootEnv_length a

/-- The colour palette of depth 1, through the update chain. -/
theorem childEnv_colName (c : ℕ) : childEnv.arrs (colName 1 c) = arrOf 2 (fun _ => 0) := by
  show ((((((rootEnv.setArr (alvName 1) 1 1).setArr (gamName 1) 0 1).setArr
      (gamName 1) 1 1).setArr (memName 1) 0 1).setVar (mnumName 1) 1).arrs _) = _
  rw [arrs_setVar,
    arrs_setArr, if_neg (by simp [colName, memName, String.ext_iff]),
    arrs_setArr, if_neg (by simp [colName, gamName, String.ext_iff]),
    arrs_setArr, if_neg (by simp [colName, gamName, String.ext_iff]),
    arrs_setArr, if_neg (by simp [colName, alvName, String.ext_iff])]
  exact rootEnv_colName 1 c

/-- `DepthMem` survives the update — the landed transport lemmas, used
as the thread wave will use them. -/
theorem depthMem_childEnv : DepthMem 2 0 0 childEnv :=
  ((((depthMem_rootEnv.setArr (alvName 1) 1 1).setArr (gamName 1) 0 1).setArr
      (gamName 1) 1 1).setArr (memName 1) 0 1).setVar (mnumName 1) 1

theorem depthMemM_childEnv : DepthMemM 2 childEnv := fun j =>
  exists_arrOf ((childEnv_length _).trans (len2_memName j))

set_option maxHeartbeats 1000000 in
theorem levelMem_childEnv : LevelMem 4 2 0 0 childEnv := by
  refine ⟨fun p hp => ?_, by decide, by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact exists_arrOf ((childEnv_length _).trans (by decide))

set_option maxHeartbeats 2000000 in
theorem orderMem_childEnv : OrderMem 4 2 0 0 childEnv := by
  refine ⟨le_rfl, ⟨by decide, by decide⟩, fun p hp => ?_,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact exists_arrOf ((childEnv_length _).trans (by decide))

set_option maxHeartbeats 400000 in
theorem levelPre_childEnv :
    LevelPre 4 2 0 0 0 0 (fun _ => 0) (fun _ => 0) 1 (fun z => z) (fun _ => 1)
      (fun _ _ => 0) childEnv := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    fun c _ => childEnv_colName c,
    fun z hz => Nat.lt_of_lt_of_le hz (by norm_num),
    fun _ _ => (by norm_num : (1 : ℕ) < 4), fun _ _ _ _ => Nat.zero_le 1,
    levelMem_childEnv, depthMem_childEnv, by decide, orderMem_childEnv,
    fun z _ hz => absurd hz (Nat.not_lt_zero z),
    fun z hz => absurd hz (Nat.not_lt_zero z)⟩

/-- **Existence, child shape.** The descend-like update hands depth 1 a
full `LevelPreM`: the child mask kills vertex 0, and the child member
list is the block list filtered by that mask — content `[1]`, count 1,
sorted because the block list was. This is the state `hlevin` will be
built from once `DescendStep`'s postcondition exports the two new
stores (design doc §3, producer P-child). -/
theorem levelPreM_child :
    LevelPreM 4 2 0 0 0 0 (fun _ => 0) (fun _ => 0) 1 (fun z => z) (fun _ => 1)
      (fun _ _ => 0) childEnv := by
  refine ⟨levelPre_childEnv, depthMemM_childEnv,
    fun z => if z = 0 then 1 else 0, 1, by decide, by decide, ?_,
    fun z _ => by show (if z = 0 then 1 else 0) < 4; split <;> omega⟩
  refine ⟨fun j hj => by show (if j = 0 then 1 else 0) < 2; split <;> omega,
    fun i j hij hj => by omega, fun j hj => ?_, fun a ha => ?_⟩
  · have hj0 : j = 0 := by omega
    subst hj0
    exact ⟨by norm_num, by simp [markSet]⟩
  · obtain ⟨hlt, hmem⟩ := ha
    rw [mem_markSet] at hmem
    have hne : a ≠ 0 := by simpa using hmem
    exact ⟨0, by omega, by simp [show a = 1 by omega]⟩

/-! ## §4 The producer, charged at the block — and the two negatives

The instrument is `TgtWidenProbe.execC`, the same cost-carrying
interpreter `OrderBlockProbe` §1 pinned the landed order text with.
The probe state is `CluScan`'s context at depth 0: the block CSR of
the current centre (`curName 0 = 1`, whose row holds the block), the
cluster indicator, and the child member array. The carrier enters only
through `clusterLoad`'s landed `fillCom` head — which is exactly the
per-turn carrier walk BlockLeaves' composed clear+load replaces (E4,
`blockLoadK`); the DELTA the emission adds must not, and does not,
read the carrier at all. -/

/-- `RamDriver.clusterLoad`, with the member-emission add-on: one store
and one counter bump inside the existing block scan. The raw block
list lands in the child's member array in emission order — the block
row's order — and `"bq"` counts it. -/
def clusterLoadM (j : ℕ) : Com :=
  .seq (fillCom (cluName j) (.lit 0))
    (.seq (.assign "bq" (.lit 0))
      (.seq (Csr.loadRow (xofName j) (curName j) "p" "pend")
        (Csr.scan "p" "pend"
          (.seq (.store (cluName j) (.get (xmmName j) (.var "p")) (.lit 1))
            (.seq (.store (memName (j + 1)) (.var "bq") (.get (xmmName j) (.var "p")))
              (.seq (.assign "bq" (.add (.var "bq") (.lit 1)))
                (.assign "p" (.add (.var "p") (.lit 1)))))))))

/-- The scan context: carrier `n`, the current centre `1`, whose block
holds the first `bs` cells of the (sorted) row `[7, 13, 91]`. -/
def cluSt (n bs : ℕ) : PSt :=
  { vars := [("n", n), (curName 0, 1)]
    arrs := [(xofName 0, 0 :: 0 :: bs :: List.replicate (n - 1) bs),
             (xmmName 0, List.take bs [7, 13, 91] ++ List.replicate 7 0),
             (cluName 0, List.replicate n 0),
             (memName 1, List.replicate n 9)] }

/-- The clock of a load variant on the scan context. -/
def cluClock (c : Com) (n bs : ℕ) : ℕ := (execC pB pF c (cluSt n bs)).2

-- both variants complete on every instance
#guard (execC pB pF (clusterLoad 0) (cluSt 100 3)).1.isOk
#guard (execC pB pF (clusterLoadM 0) (cluSt 100 3)).1.isOk
#guard (execC pB pF (clusterLoadM 0) (cluSt 200 3)).1.isOk

-- **the emission delta is carrier-blind**: the add-on's extra clock is
-- the same at carriers 100 and 200, at every block size
#guard cluClock (clusterLoadM 0) 100 0 - cluClock (clusterLoad 0) 100 0 =
  cluClock (clusterLoadM 0) 200 0 - cluClock (clusterLoad 0) 200 0
#guard cluClock (clusterLoadM 0) 100 2 - cluClock (clusterLoad 0) 100 2 =
  cluClock (clusterLoadM 0) 200 2 - cluClock (clusterLoad 0) 200 2
#guard cluClock (clusterLoadM 0) 100 3 - cluClock (clusterLoad 0) 100 3 =
  cluClock (clusterLoadM 0) 200 3 - cluClock (clusterLoad 0) 200 3

-- **and linear in the block**: `8` per member plus the counter init's
-- `2` — the `≤ c·(block size)` law, pinned at three block sizes
#guard cluClock (clusterLoadM 0) 100 0 - cluClock (clusterLoad 0) 100 0 = 2
#guard cluClock (clusterLoadM 0) 100 2 - cluClock (clusterLoad 0) 100 2 = 8 * 2 + 2
#guard cluClock (clusterLoadM 0) 100 3 - cluClock (clusterLoad 0) 100 3 = 8 * 3 + 2

-- the emission really is the block list, in row order
#guard (List.range 3).map ((execC pB pF (clusterLoadM 0) (cluSt 100 3)).1.cell (memName 1)) =
  [7, 13, 91]
#guard (execC pB pF (clusterLoadM 0) (cluSt 100 3)).1.scalar "bq" = 3

/-- **The child filter**: the raw block list against the child mask
`alvName (j+1)`, compacted in place into the live prefix, the count
into `mnumName (j+1)`. Runs after `subCom` has written the child mask,
walks `"bq"` cells — the block, never the carrier — and is stable, so
the child list inherits the block list's order. -/
def memFilterCom (j : ℕ) : Com :=
  .seq (.assign "mk" (.lit 0))
    (.seq (.assign (mnumName j) (.lit 0))
      (.while (.lt (.var "mk") (.var "bq"))
        (.seq (.assign "mv" (.get (memName j) (.var "mk")))
          (.seq (.ite (.lt (.lit 0) (.get (alvName j) (.var "mv")))
              (.seq (.store (memName j) (.var (mnumName j)) (.var "mv"))
                (.assign (mnumName j) (.add (.var (mnumName j)) (.lit 1))))
              .skip)
            (.assign "mk" (.add (.var "mk") (.lit 1)))))))

/-- The filter context: a raw block list of `bq` cells starting
`[7, 13, 91]` in the child member array, the child mask alive exactly
at `{7, 91}` (member `13` went into the batch), inside an
`n`-carrier. -/
def filterSt (n bq : ℕ) : PSt :=
  { vars := [("bq", bq)]
    arrs := [(memName 1, [7, 13, 91] ++ List.replicate (n - 3) 9),
             (alvName 1, ((List.replicate n 0).set 7 1).set 91 1)] }

def filterClock (n bq : ℕ) : ℕ := (execC pB pF (memFilterCom 1) (filterSt n bq)).2

#guard (execC pB pF (memFilterCom 1) (filterSt 100 3)).1.isOk
-- **carrier-blind**: equal clocks at carriers 100 and 200
#guard filterClock 100 3 = filterClock 200 3
-- and the whole pass is the `≤ c·(block size)` law: `21` per block
-- cell over the two-counter head's `8`, empty block at the head alone
#guard filterClock 100 0 = 8
#guard filterClock 100 3 = 21 * 3 + 8
-- the answer: the live prefix is the child list, sorted because the
-- block list was and the filter is stable; the count is its length
#guard (List.range 2).map
  ((execC pB pF (memFilterCom 1) (filterSt 100 3)).1.cell (memName 1)) = [7, 91]
#guard (execC pB pF (memFilterCom 1) (filterSt 100 3)).1.scalar (mnumName 1) = 2

/-- **The E3 hazard, compiled** (design doc §3): a BFS-ordered —
unsorted — block emission cannot feed the clause. `MemList.smono`
fails on the two-member list `[91, 7]`, generically in the mask: the
sortedness supply is the emission order, and the landed `emitLoop`
walks the carrier in index order while a block-driven emit (E3) walks
it in discovery order. Whichever wave moves the emission owns this
obligation. -/
theorem unsorted_emission_refuted (X : Set (Fin 100)) :
    ¬ MemList 100 2 (fun k => if k = 0 then 91 else 7) X := fun h =>
  absurd (h.smono 0 1 (by omega) (by omega)) (by norm_num)

/-- **The negative control: the mask alone is a carrier scan.** The
list-from-mask pass — `OrderBlockProbe`'s prose reason why the parent
must hand the list down — walks `n` cells whatever the arena holds. -/
def memFromMaskCom (j : ℕ) : Com :=
  .seq (.assign "mk" (.lit 0))
    (.seq (.assign (mnumName j) (.lit 0))
      (.while (.lt (.var "mk") (.var "n"))
        (.seq (.ite (.lt (.lit 0) (.get (alvName j) (.var "mk")))
            (.seq (.store (memName j) (.var (mnumName j)) (.var "mk"))
              (.assign (mnumName j) (.add (.var (mnumName j)) (.lit 1))))
            .skip)
          (.assign "mk" (.add (.var "mk") (.lit 1))))))

/-- The mask context: two alive vertices in an `n`-carrier. -/
def maskSt (n : ℕ) : PSt :=
  { vars := [("n", n)]
    arrs := [(alvName 0, ((List.replicate n 0).set 7 1).set 91 1),
             (memName 0, List.replicate n 9)] }

def maskClock (n : ℕ) : ℕ := (execC pB pF (memFromMaskCom 0) (maskSt n)).2

#guard (execC pB pF (memFromMaskCom 0) (maskSt 100)).1.isOk
-- it does produce the right list …
#guard (List.range 2).map ((execC pB pF (memFromMaskCom 0) (maskSt 100)).1.cell (memName 0)) =
  [7, 91]
-- … but the clock GROWS with the carrier at the fixed two-member
-- arena: `14` per carrier vertex — the `Ω(n)` shape, compiled. The
-- parent's descend scan is the only sub-`Ω(n)` producer.
#guard maskClock 200 - maskClock 100 = 14 * 100
#guard maskClock 100 ≠ maskClock 200

/-! ## §5 The consumer direction: the live-prefix copy convention

The engine-side wiring check: a level hands its member list to an
engine by copying the LIVE PREFIX into the fixed names `"mem"`/`"mm"`
(`ArenaA`'s convention, `Refine/ScatterBlock.lean:87-93`) — the
`CoverBlock.memCopy_spec` leaf at `memCopyK mm = 12·mm + 6`, NOT
`copyCom`'s fixed-`n` copy (that copy is itself a carrier walk; the
design doc's consumer table charges every copy at the member count).
The engine here is the landed member-driven clearing pass
`ScatterBlock.clearMem` (budget `clearMemK mm = 25·mm + 12`), reading
`"mem"`/`"mm"` — the composition is a wiring check on landed capital,
not a re-derivation. -/

/-- The consumer composite: count into `"mm"`, live prefix into
`"mem"`, then the landed engine. -/
def consumeCom : Com :=
  .seq (.assign "mm" (.var (mnumName 0)))
    (.seq (copyUpto (memName 0) "mem" (.var "mm"))
      Lax3Proofs.Refine.ScatterBlock.clearMem)

/-- The consumer context: the depth's member list (live prefix
`[7, 91]`, junk tail) at its fixed length `n`, the engine names
pre-allocated at `n` per the E29 story, the exclusion bits all set. -/
def consumeSt (n : ℕ) : PSt :=
  { vars := [(mnumName 0, 2)]
    arrs := [(memName 0, [7, 91] ++ List.replicate (n - 2) 0),
             ("mem", List.replicate n 9),
             ("exc", List.replicate n 1)] }

def consumeClock (n : ℕ) : ℕ := (execC pB pF consumeCom (consumeSt n)).2

#guard (execC pB pF consumeCom (consumeSt 100)).1.isOk
#guard (execC pB pF consumeCom (consumeSt 200)).1.isOk
-- **carrier-blind**: the whole read path — count, prefix copy, engine
-- — has equal clocks at carriers 100 and 200
#guard consumeClock 100 = consumeClock 200
-- and sits inside the named landed budgets, with `4` for the count
-- copy: `memCopyK 2 + clearMemK 2 + 4`
#guard consumeClock 100 ≤
  Lax3Proofs.Refine.CoverBlock.memCopyK 2 + Lax3Proofs.Refine.ScatterBlock.clearMemK 2 + 4
-- the engine got the right members and touched only them
#guard (execC pB pF consumeCom (consumeSt 200)).1.cell "exc" 7 = 0
#guard (execC pB pF consumeCom (consumeSt 200)).1.cell "exc" 91 = 0
#guard ((execC pB pF consumeCom (consumeSt 200)).1.cell "exc" 0 = 1)
#guard ((execC pB pF consumeCom (consumeSt 200)).1.cell "exc" 199 = 1)
-- the copy moved exactly the live prefix
#guard (List.range 3).map ((execC pB pF consumeCom (consumeSt 200)).1.cell "mem") = [7, 91, 9]

/-! ## §6 Floor-death: the §1 order-text shape is escapable

`OrderBlockProbe` §1 compiled the landed order text's clock as affine
in the CARRIER (`+650·n` at `R = 0`) and refuted `orderCostA` read at
the arena weight `4`; its §2 no-escape theorem multiplied any
`Ω(n)` empty-arena charge into the root. With the member clause
available, both die at once: the member-driven phase's measured clock
(`OrderSigProbeM.phaseClockK m = 68·m + 12`, pinned on the tower's own
semantics at two carrier widths) FITS the same budget at the same
reading point, its empty-arena charge is the constant `12`, and the
full Σ-interface arithmetic at exactly these constants closes by
`G2ExistsRevalidation.g2m_exists` — cited, not re-derived. The
surviving carrier term of the landed budget (`orderPhaseCost`'s
`≈1600·n`-per-level class, `n²` nested — `C0Probe`'s floor) has no
analogue: nothing here reads the carrier. -/

open Lax3Proofs.Refine.G2CostProbe (orderCostA bsq)
open Lax3Proofs.Refine.OrderSigProbeM (phaseClockK probeClock probeClock_carrier_blind mem2)

/-- **The escape, at `OrderBlockProbe`'s own instance.** The landed
text's 200-carrier clock refutes `orderCostA (bsq 2 2 0) 0` read at
the two-vertex arena's weight `4` (`OrderBlockProbe`'s compiled
`#guard`); the member-driven phase measured at the same member count
fits it — and fits the EMPTY arena's budget at the constant charge,
which is the exact reading `nested_emptyCharge_floor` needs to be
harmless. -/
theorem memPhase_escapes_floor :
    (probeClock 100 mem2 = probeClock 200 mem2) ∧
    phaseClockK 2 ≤ orderCostA (bsq 2 2 0) 0 4 ∧
    phaseClockK 0 ≤ orderCostA (bsq 2 2 0) 0 0 :=
  ⟨probeClock_carrier_blind.1, by decide, by decide⟩

-- **the nested floor, defused at the measured constant.** The exact
-- `10¹¹` instance where `OrderBlockProbe.emptyCharge_route_dead`
-- killed every carrier-charged budget family: the multiplied
-- empty-arena charge at `phaseClockK 0 = 12` sits far inside the
-- M-class closed form that same theorem read the bound from.
#guard (10 ^ 11 + 2 * (10 ^ 11 - 1)) * (phaseClockK 0 + 11) ≤
  (3 * Lax3Proofs.Refine.G2CostProbe.g2A 2 2 1 (10 ^ 4) (10 ^ 4) (10 ^ 4) (10 ^ 4) 8 +
    10 ^ 4) * (8 + 1) ^ 3 * ((10 ^ 11 + 2 * (10 ^ 11 - 1)) + 1)

/-- **The interface closes at the measured constants** — the
arithmetic the thread wave will discharge its slots against, consumed
from `g2m_exists` (all three phase families at the P4.6 law
`68·m + 12`, `R = 0`, the C0 ladder's `ℓ = 3`, `D = 8`, `ct = 200`,
`ksc = 10⁴`): budgets exist satisfying the M-class phase slots, the
landed Σ-interface shapes byte for byte, and a weight-linear,
`(D+1)^ℓ`-geometric root close. -/
theorem memPhase_interface_closes (Cb : ℕ) :
    ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
      (∀ j w m, m ≤ w →
        Lax3Proofs.Refine.G2ExistsRevalidation.phaseMR 68 12 0 m ≤ Ko j w) ∧
      (∀ j w m, m ≤ w →
        Lax3Proofs.Refine.G2ExistsRevalidation.phaseMR 68 12 0 m ≤ Kc j w) ∧
      (∀ j w m, m ≤ w →
        Lax3Proofs.Refine.G2ExistsRevalidation.phaseMR 68 12 0 m ≤ Kd j w) ∧
      (∀ w, Cb * (w + 1) ≤ Kl 3 w) ∧
      (∀ j, Monotone (Kl j)) ∧
      (∀ j < 3, ∀ s : ℕ,
        Lax3Proofs.Refine.G2CostProbe.turnCostSizeA 200 (10 ^ 4) s (Kl (j + 1) s) ≤
          Ks j s) ∧
      (∀ j < 3, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
        (∑ c ∈ Finset.range t, bs c) ≤ 8 * (w + 1) →
        Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
          ≤ Kl j w) ∧
      (∀ w, Kl 0 w ≤
        (3 * Lax3Proofs.Refine.G2ExistsRevalidation.g2M 68 12 68 12 68 12 0 200 (10 ^ 4) 8 +
          Cb) * (8 + 1) ^ 3 * (w + 1)) :=
  Lax3Proofs.Refine.G2ExistsRevalidation.g2m_exists 3 8 Cb 0 68 12 68 12 68 12 200 (10 ^ 4)
    (fun _ => 10 ^ 4) (fun _ _ => le_rfl)

/-! ## §7 Axioms

Every principal declaration, at the kernel three. -/

#print axioms memList_unique
#print axioms memClause_zero_carrier
#print axioms levelPreM_root
#print axioms levelPreM_child
#print axioms unsorted_emission_refuted
#print axioms memPhase_escapes_floor
#print axioms memPhase_interface_closes

end Lax3Proofs.Refine.MemThreadProbe
