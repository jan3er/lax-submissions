import Lax3Proofs.Refine.ElimCompactWalks

/-!
# ND-MC E2-fold — the compaction walk, discharged

`Refine/ElimCompact.lean` §8 leaves `CompactInstalls`, and
`Refine/ElimCompactWalks.lean` §4 leaves half of it: `cixPass_run` is the
inverse numbering, and `compactCsr` — the nested CSR construction whose
postcondition is a `RamElim.CsrSimple` of the member pullback — is what
this satellite is.

The shape of the argument, in one paragraph. `cixPass` leaves an inverse
numbering `Kix` with `Kix (Mem j) = j` for every member `j`; `cRow` then
walks member `z`'s row **in the level CSR**, and appends `Kix (T p)` for
every slot `p` whose target is alive. So the compact row of `z` is the
image of the row's *live* slots under `Kix ∘ T` (§1's `cNbr`), the
compact offsets are the running sums of its sizes (`cOff`), and the
compact slot count is `cOff mm`. Three facts carry the whole file:

* the image is as large as the set of live slots (`card_cNbr`) — two
  live slots with the same image have the same target, because `Kix` is
  injective on live vertices (a live vertex is a member, and
  `Kix (Mem j) = j`), and the level row lists each neighbour once;
* `j ∈ cNbr z ↔ (memGraph G M hml).Adj ⟨z⟩ ⟨j⟩` (`mem_cNbr_iff`) — the
  forward direction is `CsrGraph.madj_of_slot`, the backward one
  `CsrGraph.slot_of_madj` plus `MemList.complete`;
* the live slots of a row are a subset of its raw slots, so
  `cOff mm ≤ memRowSum mm O Mem ≤ nt` — which is both the charge clause
  of the obligation and the `cs ≤ nt` the engine's scratch width needs.

§0 is the refutation the next section is about. §1 is the mathematics
above. §2 is the renumbering pass: one slot, one row (the kit's
`Csr.rowScan_spec`), every row (`Spec.while_potential` at a potential
with a member term and a raw-slot term — the shape of
`RamDriverDedup.dedupRows_spec`, and for its reason: a turn costs the
member's *raw* row length, so no constant-per-turn combinator applies),
and what the pass built read as a `CsrSimple`. §3 is the install (five
prefix passes at `RamDriverOrder.fillKeep_spec`, which keeps the
carrier-length tails the compact call never touches) and the obligation.
§4 is the charge, compiled two-sided on `ElimCompactWalks` §3.1's
dead-row instance; §5 the axioms.

## The clause this file's §0 forced into the obligation

`CompactInstalls` was frozen with two word bounds, `mm + nt + 1 < B` and
`n < B`, and with them it is **false**. `cRow` tests a target's liveness
with `.lt (.lit 0) (.get "alv" (.var "kw"))`, and an IMP+ `get`
evaluates only if the cell it reads holds a word
(`Reasoning.evalB_get`'s third premise); `ArenaEntryC` pins
`σ.arrs "alv" = arrOf n M` for an arbitrary `M : ℕ → ℕ` and neither
bound reaches the numbers in it. At a mask that marks a live vertex with
a number above `B` the test does not evaluate, so there is no `Run` at
all and the existential conclusion is unsatisfiable however good the
program is. §0 compiles that failure, in the campaign's
refute-before-prove discipline and beside `ElimCompactWalks` §3.1's
refutation of the cost clause.

The repair — a third word bound `∀ v, v < n → M v < B`, exactly
`RamElim.elim_specW`'s own `hMB`, which the compacted entry surface had
lost when `ArenaEntryC` replaced `ElimPre`'s clause list — is landed in
`ElimCompact` §8. So `compactInstalls` below is the obligation verbatim,
with the mask bound arriving as one more `intro`, and nothing is
weakened.
-/

namespace Lax3Proofs.Refine.ElimCompactCsr

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamBfs (masked masked_adj MAdj CsrGraph)
open Lax3Proofs.RamDriver (copyUpto fillUpto)
open Lax3Proofs.RamDriverCluster (markSet mem_markSet)
open Lax3Proofs.Refine.ScatterBlock (MemList MemOf)
open Lax3Proofs.RamElim (CsrSimple liveSlots mem_liveSlots)
open Lax3Proofs.Refine.ElimCompact (memEmb memGraph memGraph_adj memRowSum compactCostRaw
  cixPass cRow compactCsr compactPass installCom ElimPreC ArenaEntryC CompactInstalls)

/-! The walk proofs of §2–§3 are written **goal by goal against one
collapsing simp set** — the six `setVar`/`setArr` projections plus the
handful of reads the walk did — and closed by `(try simp only […]) <;>
tac`, so that a bullet is right whether or not the collapse already
closed its goal. That is deliberate: `run_vcg` hands back one goal per
control-flow path plus the value bounds it could not read off the
precondition, and a proof that guesses which of those the collapse
finishes is a proof that breaks when the program text moves by one
command. The price is that a given bullet uses only part of the set and
sometimes has nothing left to do, which four style linters police; they
are off for this file and for no other reason. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-! ## §0 The mask has to hold words

`Refine/ElimCompactWalks.lean` §3.1 refuted the cost clause of
`CompactInstalls` on data; this is the second refutation, of the
*derivation* clause, and it is one line of evaluation rather than a
clock. The liveness test of `cRow` reads the mask cell of a target, and
`Expr.evalB` returns `none` on a cell that is not a word — so at a mask
whose live marks are large there is no `Run` at all and no state
satisfies the conclusion.

The instance: bound `B = 6`, a mask cell holding `100`. -/

/-- A store whose mask marks a vertex with a number too large to be a
word at the bound the run is taken at. -/
def bigMaskSt : Env :=
  { vars := fun x => if x = "kw" then 0 else 1
    arrs := fun a => if a = "alv" then [100] else [0]
    inp := []
    out := [] }

/-- **The liveness test does not evaluate.** On `bigMaskSt` — word bound
`6`, mask cell `100` — `cRow`'s branch condition is `none`, so the `ite`
has no derivation, so neither does `compactPass`, and
`CompactInstalls`' conclusion (which asserts a `Run`) is unreachable
however good the program is.

This is what forces the third word bound of `ElimCompact` §8's
`CompactInstalls`, `∀ v, v < n → M v < B`. `ArenaEntryC` pins the mask's
*length* and nothing about the numbers in it, and `mm + nt + 1 < B` and
`n < B` do not reach them; the clause is `RamElim.elim_specW`'s own
`hMB`, which the compacted entry surface had lost when `ArenaEntryC`
replaced `ElimPre`'s clause list. -/
theorem evalB_liveness_none :
    (Cond.lt (.lit 0) (.get "alv" (.var "kw"))).evalB 6 bigMaskSt = none := by
  decide

/-! ## §1 The compacted arena, as sets

No program, no store, no cost: what `cRow` is *supposed* to write, said
in `Finset`s, and the three facts §2 spends. -/

section Sets

variable {n mm nt : ℕ} {G : SimpleGraph (Fin n)} {O T M Mem Kix : ℕ → ℕ}

/-- **The compact row of member `z`**: the live slots of its row in the
level CSR, renumbered through the inverse numbering. This is exactly the
set of values `cRow` appends. -/
def cNbr (O T M Mem Kix : ℕ → ℕ) (z : ℕ) : Finset ℕ :=
  (liveSlots O T M (Mem z)).image (fun p => Kix (T p))

/-- **The compact offsets**: the running sums of the compact rows'
sizes. `cOff mm` is the compact slot count. -/
def cOff (O T M Mem Kix : ℕ → ℕ) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, (cNbr O T M Mem Kix j).card

@[simp] theorem cOff_zero : cOff O T M Mem Kix 0 = 0 := by simp [cOff]

theorem cOff_succ (i : ℕ) :
    cOff O T M Mem Kix (i + 1) = cOff O T M Mem Kix i + (cNbr O T M Mem Kix i).card :=
  Finset.sum_range_succ _ _

theorem range_mono {i k : ℕ} (h : i ≤ k) : Finset.range i ⊆ Finset.range k := fun _ hx =>
  Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) h)

theorem cOff_mono {i k : ℕ} (h : i ≤ k) : cOff O T M Mem Kix i ≤ cOff O T M Mem Kix k :=
  Finset.sum_le_sum_of_subset (range_mono h)

theorem memRowSum_mono {i k : ℕ} (h : i ≤ k) : memRowSum i O Mem ≤ memRowSum k O Mem :=
  Finset.sum_le_sum_of_subset (range_mono h)

/-- **A member is alive** — `MemList.sound`, in the form the walks read
the mask in. -/
theorem alive_mem (hml : MemList n mm Mem (markSet n M)) {j : ℕ} (hj : j < mm) :
    M (Mem j) ≠ 0 := by
  obtain ⟨hlt, hmem⟩ := hml.sound j hj
  exact hmem

/-- **A live vertex is a member, and the inverse numbering names it.**
`MemList.complete` plus `cixPass`'s postcondition; this is the one place
the numbering's totality is used, and it is why `cRow` may read `kix` at
any target it finds alive. -/
theorem kix_of_live (hml : MemList n mm Mem (markSet n M))
    (hKix : ∀ j, j < mm → Kix (Mem j) = j) {v : ℕ} (hv : v < n) (hM : M v ≠ 0) :
    Kix v < mm ∧ Mem (Kix v) = v := by
  obtain ⟨j, hj, hMj⟩ := hml.complete v ⟨hv, hM⟩
  subst hMj
  rw [hKix j hj]
  exact ⟨hj, rfl⟩

/-- **…so the numbering is injective on live vertices.** -/
theorem kix_inj_of_live (hml : MemList n mm Mem (markSet n M))
    (hKix : ∀ j, j < mm → Kix (Mem j) = j) {v w : ℕ} (hv : v < n) (hMv : M v ≠ 0)
    (hw : w < n) (hMw : M w ≠ 0) (h : Kix v = Kix w) : v = w := by
  have h₁ := (kix_of_live hml hKix hv hMv).2
  have h₂ := (kix_of_live hml hKix hw hMw).2
  rw [← h₁, ← h₂, h]

/-- **The compact row is as big as the row's live part.** The renumbering
loses nothing: two live slots with the same image name the same vertex
(the numbering is injective on live vertices), and the level row names
each neighbour once — which is the whole reason the input surface is
`CsrSimple` and not `CsrGraph`. -/
theorem card_cNbr (hcsr : CsrSimple G nt O T) (hml : MemList n mm Mem (markSet n M))
    (hKix : ∀ j, j < mm → Kix (Mem j) = j) {z : ℕ} (hz : z < mm) :
    (cNbr O T M Mem Kix z).card = (liveSlots O T M (Mem z)).card := by
  refine Finset.card_image_of_injOn fun p hp q hq he => ?_
  rw [Finset.mem_coe, mem_liveSlots] at hp hq
  have hmz : Mem z < n := hml.lt z hz
  have hpn : T p < n := hcsr.csr.target_lt' hmz hp.1.2
  have hqn : T q < n := hcsr.csr.target_lt' hmz hq.1.2
  exact hcsr.nodup (Mem z) hmz p q hp.1.1 hp.1.2 hq.1.1 hq.1.2
    (kix_inj_of_live hml hKix hpn hp.2 hqn hq.2 he)

/-- **Everything in a compact row is a compact vertex.** -/
theorem cNbr_lt (hcsr : CsrSimple G nt O T) (hml : MemList n mm Mem (markSet n M))
    (hKix : ∀ j, j < mm → Kix (Mem j) = j) {z : ℕ} (hz : z < mm) {v : ℕ}
    (hv : v ∈ cNbr O T M Mem Kix z) : v < mm := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
  rw [mem_liveSlots] at hp
  exact (kix_of_live hml hKix (hcsr.csr.target_lt' (hml.lt z hz) hp.1.2) hp.2).1

/-- **The compact rows are the compacted arena's adjacency.** Forward:
a live slot of a live vertex names a neighbour in the arena
(`CsrGraph.madj_of_slot`), and that neighbour is a member. Backward: a
neighbour of a member in the arena is alive, hence a member, and is named
by a slot of the row (`CsrGraph.slot_of_madj`). -/
theorem mem_cNbr_iff (hcsr : CsrSimple G nt O T) (hml : MemList n mm Mem (markSet n M))
    (hKix : ∀ j, j < mm → Kix (Mem j) = j) {z v : ℕ} (hz : z < mm) (hv : v < mm) :
    v ∈ cNbr O T M Mem Kix z ↔ (memGraph G M hml).Adj ⟨z, hz⟩ ⟨v, hv⟩ := by
  have hmz : Mem z < n := hml.lt z hz
  have hMz : M (Mem z) ≠ 0 := alive_mem hml hz
  constructor
  · intro h
    obtain ⟨p, hp, hpv⟩ := Finset.mem_image.1 h
    rw [mem_liveSlots] at hp
    have hpn : T p < n := hcsr.csr.target_lt' hmz hp.1.2
    have hadj : MAdj G M (Mem z) (T p) :=
      hcsr.csr.madj_of_slot hmz hp.1.1 hp.1.2 hMz hp.2
    have hTp : Mem v = T p := by
      rw [← hpv]; exact (kix_of_live hml hKix hpn hp.2).2
    rw [memGraph_adj,
      show memEmb hml ⟨v, hv⟩ = (⟨T p, hpn⟩ : Fin n) from Fin.ext hTp]
    exact hadj.2.2
  · intro h
    rw [memGraph_adj] at h
    obtain ⟨p, h₁, h₂, h₃⟩ :=
      hcsr.csr.slot_of_madj (M := M) (a := Mem z) (b := Mem v) ⟨hmz, hml.lt v hv, h⟩
    refine Finset.mem_image.2 ⟨p, mem_liveSlots.2 ⟨⟨h₁, h₂⟩, ?_⟩, ?_⟩
    · rw [h₃]; exact alive_mem hml hv
    · rw [h₃, hKix v hv]

/-! ### §1.1 The two size bounds -/

/-- A compact row is no longer than the raw row it was read from: the
live slots are a subset of the row's slots. -/
theorem card_cNbr_le_rowLen (hcsr : CsrSimple G nt O T)
    (hml : MemList n mm Mem (markSet n M)) (hKix : ∀ j, j < mm → Kix (Mem j) = j)
    {z : ℕ} (hz : z < mm) : (cNbr O T M Mem Kix z).card ≤ Csr.rowLen O (Mem z) := by
  rw [card_cNbr hcsr hml hKix hz]
  calc (liveSlots O T M (Mem z)).card
      ≤ (Finset.Ico (O (Mem z)) (O (Mem z + 1))).card :=
        Finset.card_filter_le _ _
    _ = Csr.rowLen O (Mem z) := Nat.card_Ico _ _

/-- **The compact slot count is inside the compaction's charge.** This is
the clause `ElimCompactWalks` §3.1's refutation asks for: the walk pays
for the raw rows, and the live count it reports is below that. -/
theorem cOff_le_memRowSum (hcsr : CsrSimple G nt O T)
    (hml : MemList n mm Mem (markSet n M)) (hKix : ∀ j, j < mm → Kix (Mem j) = j) :
    cOff O T M Mem Kix mm ≤ memRowSum mm O Mem :=
  Finset.sum_le_sum fun _ hj =>
    card_cNbr_le_rowLen hcsr hml hKix (Finset.mem_range.1 hj)

/-- **…and the charge is inside the level's slot array.** The members are
distinct vertices, so their rows tile a part of the target array. -/
theorem memRowSum_le (hcsr : CsrSimple G nt O T) (hml : MemList n mm Mem (markSet n M)) :
    memRowSum mm O Mem ≤ nt :=
  hcsr.csr.sum_rowLen_queue (fun i hi => hml.lt i hi) fun i hi j hj hq => by
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hq (Nat.ne_of_lt (hml.smono i j h hj))
    · exact h
    · exact absurd hq.symm (Nat.ne_of_lt (hml.smono j i h hi))

/-! ### §1.2 The row, mid-scan

The read pointer's prefix of a row, and its image: `cRow`'s inner loop
grows the first slot by slot and publishes the second at the write
pointer. At the end of the row they are `liveSlots` and `cNbr`, on the
nose — the two definitions coincide there and no lemma is needed. -/

/-- The live slots of `z`'s row below the read pointer. -/
def livePfx (O T M Mem : ℕ → ℕ) (z j : ℕ) : Finset ℕ :=
  (Finset.Ico (O (Mem z)) j).filter (fun p => M (T p) ≠ 0)

/-- …and what has been published for them. -/
def cPfx (O T M Mem Kix : ℕ → ℕ) (z j : ℕ) : Finset ℕ :=
  (livePfx O T M Mem z j).image (fun p => Kix (T p))

theorem livePfx_end (z : ℕ) :
    livePfx O T M Mem z (O (Mem z + 1)) = liveSlots O T M (Mem z) := rfl

theorem cPfx_end (z : ℕ) :
    cPfx O T M Mem Kix z (O (Mem z + 1)) = cNbr O T M Mem Kix z := rfl

theorem livePfx_live {z j : ℕ} (hj : O (Mem z) ≤ j) (h : M (T j) ≠ 0) :
    livePfx O T M Mem z (j + 1) = insert j (livePfx O T M Mem z j) := by
  ext p
  simp only [livePfx, Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    rcases Nat.lt_or_ge p j with hlt | hge
    · exact Or.inr ⟨⟨h₁, hlt⟩, h₃⟩
    · exact Or.inl (by omega)
  · rintro (rfl | ⟨⟨h₁, h₂⟩, h₃⟩)
    · exact ⟨⟨hj, Nat.lt_succ_self _⟩, h⟩
    · exact ⟨⟨h₁, by omega⟩, h₃⟩

theorem livePfx_dead {z j : ℕ} (h : M (T j) = 0) :
    livePfx O T M Mem z (j + 1) = livePfx O T M Mem z j := by
  ext p
  simp only [livePfx, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    refine ⟨⟨h₁, ?_⟩, h₃⟩
    rcases Nat.lt_or_ge p j with hlt | hge
    · exact hlt
    · exact absurd (show M (T p) = 0 by rw [show p = j by omega]; exact h) h₃
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    exact ⟨⟨h₁, by omega⟩, h₃⟩

theorem cPfx_live {z j : ℕ} (hj : O (Mem z) ≤ j) (h : M (T j) ≠ 0) :
    cPfx O T M Mem Kix z (j + 1) = insert (Kix (T j)) (cPfx O T M Mem Kix z j) := by
  simp only [cPfx, livePfx_live hj h, Finset.image_insert]

theorem cPfx_dead {z j : ℕ} (h : M (T j) = 0) :
    cPfx O T M Mem Kix z (j + 1) = cPfx O T M Mem Kix z j := by
  simp only [cPfx, livePfx_dead h]

theorem livePfx_start (z : ℕ) : livePfx O T M Mem z (O (Mem z)) = ∅ := by
  ext p
  simp only [livePfx, Finset.mem_filter, Finset.mem_Ico, Finset.notMem_empty, iff_false,
    not_and]
  omega

theorem cPfx_start (z : ℕ) : cPfx O T M Mem Kix z (O (Mem z)) = ∅ := by
  simp only [cPfx, livePfx_start, Finset.image_empty]

theorem notMem_livePfx {z j : ℕ} : j ∉ livePfx O T M Mem z j := by
  simp only [livePfx, Finset.mem_filter, Finset.mem_Ico, not_and]
  omega

theorem livePfx_subset {z j : ℕ} (hj : j ≤ O (Mem z + 1)) :
    livePfx O T M Mem z j ⊆ liveSlots O T M (Mem z) := by
  intro p hp
  simp only [livePfx, Finset.mem_filter, Finset.mem_Ico] at hp
  exact mem_liveSlots.2 ⟨⟨hp.1.1, by omega⟩, hp.2⟩

/-- **The write pointer stays inside the block it is filling.** At a live
slot the prefix grows by one and still fits in the row, so the cell the
store writes is below the row's own end — which is what the store's range
condition asks and what `cs ≤ nt` then pays for. -/
theorem card_livePfx_lt (hcsr : CsrSimple G nt O T) (hml : MemList n mm Mem (markSet n M))
    (hKix : ∀ j, j < mm → Kix (Mem j) = j) {z j : ℕ} (hz : z < mm)
    (hj : O (Mem z) ≤ j) (hjlt : j < O (Mem z + 1)) (h : M (T j) ≠ 0) :
    (livePfx O T M Mem z j).card < (cNbr O T M Mem Kix z).card := by
  rw [card_cNbr hcsr hml hKix hz]
  have h₁ : (livePfx O T M Mem z (j + 1)).card = (livePfx O T M Mem z j).card + 1 := by
    rw [livePfx_live hj h, Finset.card_insert_of_notMem notMem_livePfx]
  have h₂ : (livePfx O T M Mem z (j + 1)).card ≤ (liveSlots O T M (Mem z)).card :=
    Finset.card_le_card (livePfx_subset (by omega))
  omega

theorem card_livePfx_le (hcsr : CsrSimple G nt O T) (hml : MemList n mm Mem (markSet n M))
    (hKix : ∀ j, j < mm → Kix (Mem j) = j) {z j : ℕ} (hz : z < mm)
    (hj : j ≤ O (Mem z + 1)) :
    (livePfx O T M Mem z j).card ≤ (cNbr O T M Mem Kix z).card := by
  rw [card_cNbr hcsr hml hKix hz]
  exact Finset.card_le_card (livePfx_subset hj)

end Sets

/-! ## §2 The walk

`cixPass` is `ElimCompactWalks` §4; this is `compactCsr`. One slot, one
row (the kit's `Csr.rowScan_spec`), every row (`Spec.while_potential` at
a potential with a row term and a raw-slot term — the shape of
`RamDriverDedup.dedupRows_spec`, and for its reason: a turn costs the
member's *raw* row length, so no constant-per-turn combinator applies). -/

section Walk

variable {B n mm nt : ℕ} {G : SimpleGraph (Fin n)} {O T M Mem Kix : ℕ → ℕ}

/-- One slot of `cRow`'s row scan, named. Definitionally the body of the
inner `while` of `ElimCompact` §1; nothing is restated. -/
def cSlot : Com :=
  .seq (.assign "kw" (.get "tgt" (.var "kj")))
    (.seq (.ite (.lt (.lit 0) (.get "alv" (.var "kw")))
            (.seq (.store "ktg" (.var "ks") (.get "kix" (.var "kw")))
              (.assign "ks" (.add (.var "ks") (.lit 1))))
            .skip)
      (.assign "kj" (.add (.var "kj") (.lit 1))))

/-! ### §2.1 The invariants -/

/-- The arena arrays the compaction reads and never writes. -/
def CArena (n nt : ℕ) (O T M Mem Kix : ℕ → ℕ) (σ : Env) : Prop :=
  σ.arrs "mem" = arrOf n Mem ∧ σ.arrs "off" = arrOf (n + 1) O ∧
    σ.arrs "tgt" = arrOf nt T ∧ σ.arrs "alv" = arrOf n M ∧ σ.arrs "kix" = arrOf n Kix

/-- **The rows the outer loop has closed**: every compact block below `i`
names exactly the compact row of its member. `RamDriverAugment.RowsDone`
at the member pullback. -/
def CDone (O T M Mem Kix KT : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ z < i,
    (∀ p, cOff O T M Mem Kix z ≤ p → p < cOff O T M Mem Kix (z + 1) →
      KT p ∈ cNbr O T M Mem Kix z) ∧
    (∀ v ∈ cNbr O T M Mem Kix z, ∃ p, cOff O T M Mem Kix z ≤ p ∧
      p < cOff O T M Mem Kix (z + 1) ∧ KT p = v)

/-- A write at or above the current block leaves the closed ones alone. -/
theorem cDone_upd {KT : ℕ → ℕ} {z p v : ℕ} (h : CDone O T M Mem Kix KT z)
    (hp : cOff O T M Mem Kix z ≤ p) : CDone O T M Mem Kix (upd KT p v) z := by
  obtain rfl | hz := Nat.eq_zero_or_pos z
  · intro y hy; omega
  intro y hy
  obtain ⟨h₁, h₂⟩ := h y hy
  have hne : ∀ q, q < cOff O T M Mem Kix (y + 1) → q ≠ p := fun q hq => by
    have := cOff_mono (O := O) (T := T) (M := M) (Mem := Mem) (Kix := Kix)
      (show y + 1 ≤ z by omega)
    omega
  exact ⟨fun q hq₁ hq₂ => by rw [upd_of_ne _ (hne q hq₂)]; exact h₁ q hq₁ hq₂,
    fun w hw => by
      obtain ⟨q, a, b, c⟩ := h₂ w hw
      exact ⟨q, a, b, by rw [upd_of_ne _ (hne q b)]; exact c⟩⟩

/-- One more row closed. -/
theorem cDone_succ {KT : ℕ → ℕ} {z : ℕ} (h : CDone O T M Mem Kix KT z)
    (hs : ∀ p, cOff O T M Mem Kix z ≤ p → p < cOff O T M Mem Kix (z + 1) →
      KT p ∈ cNbr O T M Mem Kix z)
    (hc : ∀ v ∈ cNbr O T M Mem Kix z, ∃ p, cOff O T M Mem Kix z ≤ p ∧
      p < cOff O T M Mem Kix (z + 1) ∧ KT p = v) :
    CDone O T M Mem Kix KT (z + 1) := by
  intro y hy
  rcases Nat.lt_or_ge y z with hlt | hge
  · exact h y hlt
  · rw [show y = z by omega]; exact ⟨hs, hc⟩

/-- **The outer loop's invariant, read at a row boundary.** -/
def COuter (n mm nt : ℕ) (O T M Mem Kix : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "mm" = mm ∧ σ.vars "km" ≤ mm ∧ CArena n nt O T M Mem Kix σ ∧
    σ.vars "ks" = cOff O T M Mem Kix (σ.vars "km") ∧
    (∃ KOf, σ.arrs "kof" = arrOf (n + 1) KOf ∧
      ∀ i ≤ σ.vars "km", KOf i = cOff O T M Mem Kix i) ∧
    (∃ KT, σ.arrs "ktg" = arrOf nt KT ∧ CDone O T M Mem Kix KT (σ.vars "km"))

/-- **The row scan's invariant.** The write pointer stands at the block's
start plus the live slots the read pointer has passed, and the cells
between hold exactly what those slots renumber to — soundness and
completeness of the block in progress, which is what `block_nodup` is fed
at the end of the row. -/
def CInner (n mm nt : ℕ) (O T M Mem Kix : ℕ → ℕ) (z : ℕ) (σ : Env) : Prop :=
  σ.vars "mm" = mm ∧ σ.vars "km" = z ∧ σ.vars "ku" = Mem z ∧
    σ.vars "ke" = O (Mem z + 1) ∧
    O (Mem z) ≤ σ.vars "kj" ∧ σ.vars "kj" ≤ O (Mem z + 1) ∧
    CArena n nt O T M Mem Kix σ ∧
    σ.vars "ks" = cOff O T M Mem Kix z + (livePfx O T M Mem z (σ.vars "kj")).card ∧
    (∃ KOf, σ.arrs "kof" = arrOf (n + 1) KOf ∧ ∀ i ≤ z, KOf i = cOff O T M Mem Kix i) ∧
    (∃ KT, σ.arrs "ktg" = arrOf nt KT ∧ CDone O T M Mem Kix KT z ∧
      (∀ p, cOff O T M Mem Kix z ≤ p → p < σ.vars "ks" →
        KT p ∈ cPfx O T M Mem Kix z (σ.vars "kj")) ∧
      (∀ v ∈ cPfx O T M Mem Kix z (σ.vars "kj"), ∃ p, cOff O T M Mem Kix z ≤ p ∧
        p < σ.vars "ks" ∧ KT p = v))

/-! ### §2.2 One slot -/

/-- **One slot of a member's row.** A dead target is passed over; a live
one is renumbered through `kix` and appended at the write pointer.
Twenty ticks, and the two directions of the block in progress grow by one
cell — `RamElim.fillSlot_run`'s shape, with the same liveness test and
the same reason for it. -/
theorem cSlot_run {z : ℕ} (hcsr : CsrSimple G nt O T)
    (hml : MemList n mm Mem (markSet n M)) (hKix : ∀ j, j < mm → Kix (Mem j) = j)
    (hB : mm + nt + 1 < B) (hnB : n < B) (hMB : ∀ v < n, M v < B) (hz : z < mm)
    {σ : Env} (hI : CInner n mm nt O T M Mem Kix z σ)
    (hjlt : σ.vars "kj" < O (Mem z + 1)) :
    ∃ σ' K, Run B cSlot σ σ' K ∧ K ≤ 20 ∧
      CInner n mm nt O T M Mem Kix z σ' ∧ σ'.vars "kj" = σ.vars "kj" + 1 := by
  classical
  obtain ⟨hmm, hkm, hku, hke, hj₁, hj₂, harena, hks, ⟨KOf, hkof, hKOf⟩,
    KT, hktg, hdone, hsnd, hcmp⟩ := hI
  obtain ⟨hmem, hoff, htgt, halv, hkix⟩ := harena
  have hmz : Mem z < n := hml.lt z hz
  have hmn : mm ≤ n := hml.card_le
  have hend : O (Mem z + 1) ≤ nt := hcsr.csr.le_ns (by omega)
  have hjnt : σ.vars "kj" < nt := by omega
  have htn : T (σ.vars "kj") < n := hcsr.csr.target_lt _ (by omega)
  have htv : (σ.arrs "tgt").getD (σ.vars "kj") 0 = T (σ.vars "kj") := by
    rw [htgt, getD_arrOf T hjnt]
  have htv' : (σ.arrs "tgt")[σ.vars "kj"]?.getD 0 = T (σ.vars "kj") := by
    rw [← List.getD_eq_getElem?_getD]; exact htv
  have htgtLen : (σ.arrs "tgt").length = nt := by rw [htgt, length_arrOf]
  have halvLen : (σ.arrs "alv").length = n := by rw [halv, length_arrOf]
  have hkixLen : (σ.arrs "kix").length = n := by rw [hkix, length_arrOf]
  have hktgLen : (σ.arrs "ktg").length = nt := by rw [hktg, length_arrOf]
  -- the compact slot count is inside the target array, so the write fits
  have hcsnt : cOff O T M Mem Kix mm ≤ nt :=
    le_trans (cOff_le_memRowSum hcsr hml hKix) (memRowSum_le hcsr hml)
  have hksle : σ.vars "ks" ≤ cOff O T M Mem Kix (z + 1) := by
    rw [hks, cOff_succ]
    have := card_livePfx_le hcsr hml hKix (j := σ.vars "kj") hz (by omega)
    omega
  have hoffle : cOff O T M Mem Kix (z + 1) ≤ nt :=
    le_trans (cOff_mono (show z + 1 ≤ mm by omega)) hcsnt
  have hkslive : M (T (σ.vars "kj")) ≠ 0 → σ.vars "ks" < cOff O T M Mem Kix (z + 1) := by
    intro h
    rw [hks, cOff_succ]
    have := card_livePfx_lt hcsr hml hKix hz hj₁ hjlt h
    omega
  -- the two reads of the branch, in the environment the walk tests them in
  have hbrAlv : ((σ.setVar "kw" ((σ.arrs "tgt").getD (σ.vars "kj") 0)).arrs "alv").getD
      ((σ.setVar "kw" ((σ.arrs "tgt").getD (σ.vars "kj") 0)).vars "kw") 0
      = M (T (σ.vars "kj")) := by
    rw [arrs_setVar, vars_setVar]; simpa [htv', halv] using getD_arrOf M htn
  have hbrAlvLen : ((σ.setVar "kw" ((σ.arrs "tgt").getD (σ.vars "kj") 0)).vars "kw")
      < ((σ.setVar "kw" ((σ.arrs "tgt").getD (σ.vars "kj") 0)).arrs "alv").length := by
    rw [arrs_setVar, vars_setVar, halv, length_arrOf]; simpa [htv'] using htn
  have hbrKix : ((σ.setVar "kw" ((σ.arrs "tgt").getD (σ.vars "kj") 0)).arrs "kix").getD
      ((σ.setVar "kw" ((σ.arrs "tgt").getD (σ.vars "kj") 0)).vars "kw") 0
      = Kix (T (σ.vars "kj")) := by
    rw [arrs_setVar, vars_setVar]; simpa [htv', hkix] using getD_arrOf Kix htn
  have hbrKixLen : ((σ.setVar "kw" ((σ.arrs "tgt").getD (σ.vars "kj") 0)).vars "kw")
      < ((σ.setVar "kw" ((σ.arrs "tgt").getD (σ.vars "kj") 0)).arrs "kix").length := by
    rw [arrs_setVar, vars_setVar, hkix, length_arrOf]; simpa [htv'] using htn
  have hKixB : M (T (σ.vars "kj")) ≠ 0 → Kix (T (σ.vars "kj")) < mm := fun h =>
    (kix_of_live hml hKix htn h).1
  have hMBj : M (T (σ.vars "kj")) < B := hMB _ htn
  have hkixv : (σ.arrs "kix").getD (T (σ.vars "kj")) 0 = Kix (T (σ.vars "kj")) := by
    rw [hkix, getD_arrOf Kix htn]
  have halvv : (σ.arrs "alv").getD (T (σ.vars "kj")) 0 = M (T (σ.vars "kj")) := by
    rw [halv, getD_arrOf M htn]
  run_vcg
  · -- **a live target**: renumbered, published, and the pointers move
    have hlive : M (T (σ.vars "kj")) ≠ 0 := by
      have hc : 0 < ((σ.setVar "kw" ((σ.arrs "tgt").getD (σ.vars "kj") 0)).arrs "alv").getD
        ((σ.setVar "kw" ((σ.arrs "tgt").getD (σ.vars "kj") 0)).vars "kw") 0 := ‹_›
      rw [hbrAlv] at hc; omega
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨KOf, ?_, hKOf⟩,
      upd KT (σ.vars "ks") (Kix (T (σ.vars "kj"))), ?_, ?_, ?_, ?_⟩, ?_⟩
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hmm
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hkm
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hku
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hke
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> omega
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> omega
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hmem
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hoff
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact htgt
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact halv
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hkix
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;>
        (rw [livePfx_live hj₁ hlive, Finset.card_insert_of_notMem notMem_livePfx]; omega)
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hkof
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> rfl
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact cDone_upd hdone (by omega)
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;>
        (intro p hp₁ hp₂
         rw [cPfx_live hj₁ hlive, Finset.mem_insert]
         rcases Nat.lt_or_ge p (σ.vars "ks") with hlt | hge
         · exact Or.inr (by rw [upd_of_ne _ (by omega)]; exact hsnd p hp₁ hlt)
         · exact Or.inl (by rw [show p = σ.vars "ks" by omega, upd_self]))
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;>
        (intro v hv
         rw [cPfx_live hj₁ hlive, Finset.mem_insert] at hv
         rcases hv with rfl | hv
         · exact ⟨σ.vars "ks", by omega, by omega, upd_self ..⟩
         · obtain ⟨p, a, b, c⟩ := hcmp v hv
           exact ⟨p, a, by omega, by rw [upd_of_ne _ (by omega)]; exact c⟩)
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> rfl
  · -- **a dead target**: passed over, and only the read pointer moves
    have hdead : M (T (σ.vars "kj")) = 0 := by
      have hc : ¬ (0 < ((σ.setVar "kw" ((σ.arrs "tgt").getD (σ.vars "kj") 0)).arrs "alv").getD
        ((σ.setVar "kw" ((σ.arrs "tgt").getD (σ.vars "kj") 0)).vars "kw") 0) := ‹_›
      rw [hbrAlv] at hc; omega
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨KOf, ?_, hKOf⟩,
      KT, ?_, hdone, ?_, ?_⟩, ?_⟩
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hmm
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hkm
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hku
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hke
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> omega
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> omega
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hmem
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hoff
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact htgt
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact halv
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hkix
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> (rw [livePfx_dead hdead]; exact hks)
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hkof
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> exact hktg
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> (rw [cPfx_dead hdead]; exact hsnd)
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> (rw [cPfx_dead hdead]; exact hcmp)
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, htv, hkixv, halvv, hktg, set_arrOf_eq_upd]) <;> rfl
  all_goals first
    | omega
    | (simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
        String.reduceEq, htv, htv', hkixv, halvv, htgtLen, halvLen, hkixLen, hktgLen] at *; omega)
    | (-- the write stays inside the target array, which liveness pays for
       simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
        String.reduceEq, htv, htv', hkixv, halvv, htgtLen, halvLen, hkixLen, hktgLen] at *
       first
         | omega
         | (have h₁ := hkslive (by omega); have h₂ := hKixB (by omega); omega))

/-! ### §2.3 One row -/

/-- **The row scan's entry state.** The three reads `cRow` does before
its loop — the member's arena number and its two row bounds — put the
scan's invariant in place with nothing published yet. Stated of an
abstract triple of read values so that the row's proof discharges it by
naming what the three reads returned. -/
theorem cScan_entry {z : ℕ} {σ : Env} {a b c : ℕ} {KOf KT : ℕ → ℕ}
    (hmm : σ.vars "mm" = mm) (hkmv : σ.vars "km" = z)
    (ha : a = Mem z) (hb : b = O (Mem z)) (hc : c = O (Mem z + 1))
    (hmem : σ.arrs "mem" = arrOf n Mem) (hoff : σ.arrs "off" = arrOf (n + 1) O)
    (htgt : σ.arrs "tgt" = arrOf nt T) (halv : σ.arrs "alv" = arrOf n M)
    (hkix : σ.arrs "kix" = arrOf n Kix) (hstart : O (Mem z) ≤ O (Mem z + 1))
    (hks : σ.vars "ks" = cOff O T M Mem Kix z)
    (hkof : σ.arrs "kof" = arrOf (n + 1) KOf)
    (hKOf : ∀ i ≤ z, KOf i = cOff O T M Mem Kix i)
    (hktg : σ.arrs "ktg" = arrOf nt KT) (hdone : CDone O T M Mem Kix KT z) :
    CInner n mm nt O T M Mem Kix z (((σ.setVar "ku" a).setVar "kj" b).setVar "ke" c) ∧
      (((σ.setVar "ku" a).setVar "kj" b).setVar "ke" c).vars "kj" = O (Mem z) := by
  subst ha; subst hb; subst hc
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨KOf, ?_, hKOf⟩,
    KT, ?_, hdone, ?_, ?_⟩, ?_⟩
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> exact hmm
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> exact hkmv
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> rfl
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> rfl
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> exact le_rfl
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> exact hstart
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> exact hmem
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> exact hoff
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> exact htgt
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> exact halv
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> exact hkix
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;>
      (rw [hks, livePfx_start]; simp)
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> exact hkof
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> exact hktg
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;>
      (intro p hp₁ hp₂; omega)
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;>
      (intro v hv; rw [cPfx_start] at hv; exact absurd hv (Finset.notMem_empty v))
  · (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq]) <;> rfl

/-- **What the row's closing store needs off the scan's exit state.**
The member counter has not moved, the write pointer is inside the block
the row opened (so the next offset is a word), and the offset array is
the carrier's. -/
theorem cInner_exit {z : ℕ} {τ : Env} (hcsr : CsrSimple G nt O T)
    (hml : MemList n mm Mem (markSet n M)) (hKix : ∀ j, j < mm → Kix (Mem j) = j)
    (hz : z < mm) (hI : CInner n mm nt O T M Mem Kix z τ) :
    τ.vars "km" = z ∧ τ.vars "ks" ≤ cOff O T M Mem Kix (z + 1) ∧
      (τ.arrs "kof").length = n + 1 := by
  obtain ⟨-, hkm, -, -, -, hj₂, -, hks, ⟨KOf, hkof, -⟩, -⟩ := hI
  refine ⟨hkm, ?_, by rw [hkof, length_arrOf]⟩
  rw [hks, cOff_succ]
  have := card_livePfx_le hcsr hml hKix hz hj₂
  omega

/-- **One member's row, compacted.** The arena row of `mem[km]` is read
in the *level* CSR, scanned by the kit's row scan, and the member's block
closed in `kof`. The charge is the member's **raw** row length — the
`ite` that drops the dead targets is inside the loop, which is
`ElimCompactWalks` §3.1's finding. -/
theorem cRow_run {z : ℕ} (hcsr : CsrSimple G nt O T)
    (hml : MemList n mm Mem (markSet n M)) (hKix : ∀ j, j < mm → Kix (Mem j) = j)
    (hB : mm + nt + 1 < B) (hnB : n < B) (hMB : ∀ v < n, M v < B) (hz : z < mm)
    {σ : Env} (hI : COuter n mm nt O T M Mem Kix σ) (hkmv : σ.vars "km" = z) :
    ∃ σ' K, Run B cRow σ σ' K ∧ K ≤ 24 * Csr.rowLen O (Mem z) + 22 ∧
      COuter n mm nt O T M Mem Kix σ' ∧ σ'.vars "km" = z + 1 := by
  classical
  obtain ⟨hmm, hkmle, harena, hks, ⟨KOf, hkof, hKOf⟩, KT, hktg, hdone⟩ := hI
  obtain ⟨hmem, hoff, htgt, halv, hkix⟩ := harena
  rw [hkmv] at hkmle hks hKOf hdone
  have hmz : Mem z < n := hml.lt z hz
  have hmn : mm ≤ n := hml.card_le
  have hend : O (Mem z + 1) ≤ nt := hcsr.csr.le_ns (by omega)
  have hstart : O (Mem z) ≤ O (Mem z + 1) := hcsr.csr.mono _ hmz
  have hcsnt : cOff O T M Mem Kix mm ≤ nt :=
    le_trans (cOff_le_memRowSum hcsr hml hKix) (memRowSum_le hcsr hml)
  have hoffle : cOff O T M Mem Kix (z + 1) ≤ nt :=
    le_trans (cOff_mono (show z + 1 ≤ mm by omega)) hcsnt
  have hzle : cOff O T M Mem Kix z ≤ cOff O T M Mem Kix (z + 1) :=
    cOff_mono (Nat.le_succ z)
  -- the row scan, as the kit's
  have hscan : Spec B
      (fun τ => CInner n mm nt O T M Mem Kix z τ ∧ τ.vars "kj" = O (Mem z))
      (Csr.scan "kj" "ke" cSlot)
      (fun _ τ' => CInner n mm nt O T M Mem Kix z τ' ∧ τ'.vars "kj" = O (Mem z + 1))
      (24 * Csr.rowLen O (Mem z) + 4) :=
    Csr.rowScan_spec B (24 * Csr.rowLen O (Mem z) + 4) (O (Mem z + 1)) 20
      "kj" "ke" cSlot (CInner n mm nt O T M Mem Kix z) (by omega)
      (fun τ hτ => ⟨hτ.2.2.2.1, hτ.2.2.2.2.2.1⟩)
      (fun τ hτ hlt => by
        obtain ⟨τ', K', hr, hK', hI', hj'⟩ := cSlot_run hcsr hml hKix hB hnB hMB hz hτ hlt
        exact ⟨τ', K', hr, hI', hj', hK'⟩)
      (fun _ hτ => hτ.1) (fun τ hτ => le_of_eq (by rw [hτ.2]; simp only [Csr.rowLen]))
  -- the five reads and the one store the row does itself
  have hmemLen : (σ.arrs "mem").length = n := by rw [hmem, length_arrOf]
  have hoffLen : (σ.arrs "off").length = n + 1 := by rw [hoff, length_arrOf]
  have hkofLen : (σ.arrs "kof").length = n + 1 := by rw [hkof, length_arrOf]
  have hmemv : (σ.arrs "mem").getD (σ.vars "km") 0 = Mem z := by
    rw [hkmv, hmem, getD_arrOf Mem (by omega)]
  have hoffv : (σ.arrs "off").getD (Mem z) 0 = O (Mem z) := by
    rw [hoff, getD_arrOf O (by omega)]
  have hoffv1 : (σ.arrs "off").getD (Mem z + 1) 0 = O (Mem z + 1) := by
    rw [hoff, getD_arrOf O (by omega)]
  have hOB : O (Mem z) ≤ nt := le_trans (hcsr.csr.mono' (Nat.le_succ _) (by omega)) hend
  run_vcg [hscan]
  · -- **the row closes**: the block's two directions, and the next offset
    obtain ⟨hIn, hjend⟩ := ‹CInner n mm nt O T M Mem Kix z _ ∧ _›
    obtain ⟨hmm', hkm', hku', hke', hj₁', hj₂', harena', hks', ⟨KOf', hkof', hKOf'⟩,
      KT', hktg', hdone', hsnd', hcmp'⟩ := hIn
    obtain ⟨hmem', hoff', htgt', halv', hkix'⟩ := harena'
    rw [hjend] at hks' hsnd' hcmp'
    rw [livePfx_end, ← card_cNbr hcsr hml hKix hz, ← cOff_succ] at hks'
    rw [cPfx_end] at hsnd' hcmp'
    rw [hks'] at hsnd' hcmp'
    refine ⟨⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_,
      ⟨upd KOf' (z + 1) (cOff O T M Mem Kix (z + 1)), ?_, ?_⟩, KT', ?_, ?_⟩, ?_⟩
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, hkm', hks', hkof', set_arrOf_eq_upd]) <;> exact hmm'
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, hkm', hks', hkof', set_arrOf_eq_upd]) <;> omega
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, hkm', hks', hkof', set_arrOf_eq_upd]) <;> exact hmem'
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, hkm', hks', hkof', set_arrOf_eq_upd]) <;> exact hoff'
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, hkm', hks', hkof', set_arrOf_eq_upd]) <;> exact htgt'
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, hkm', hks', hkof', set_arrOf_eq_upd]) <;> exact halv'
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, hkm', hks', hkof', set_arrOf_eq_upd]) <;> exact hkix'
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, hkm', hks', hkof', set_arrOf_eq_upd]) <;> rfl
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, hkm', hks', hkof', set_arrOf_eq_upd]) <;> rfl
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, hkm', hks', hkof', set_arrOf_eq_upd]) <;>
        (intro i hi
         rcases Nat.lt_or_ge i (z + 1) with hlt | hge
         · rw [upd_of_ne _ (by omega)]; exact hKOf' i (by omega)
         · rw [show i = z + 1 by omega, upd_self])
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, hkm', hks', hkof', set_arrOf_eq_upd]) <;> exact hktg'
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, hkm', hks', hkof', set_arrOf_eq_upd]) <;> exact cDone_succ hdone' hsnd' hcmp'
    · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr,
        ↓reduceIte, String.reduceEq, hkm', hks', hkof', set_arrOf_eq_upd]) <;> rfl
  all_goals try (first
    | omega
    | (simp only [arrs_setVar, vars_setVar, ↓reduceIte, String.reduceEq, hmemv, hoffv,
        hoffv1, hmemLen, hoffLen, hkofLen] at *; omega)
    | (obtain ⟨hkm', hksb', hkofl'⟩ :=
         cInner_exit hcsr hml hKix hz (‹CInner n mm nt O T M Mem Kix z _ ∧ _›).1
       (try simp only [arrs_setVar, vars_setVar, ↓reduceIte, String.reduceEq, hkm', hkofl'])
       omega))
  exact cScan_entry hmm hkmv hmemv
    (by simp only [arrs_setVar, vars_setVar, ↓reduceIte, String.reduceEq, hmemv]; exact hoffv)
    (by simp only [arrs_setVar, vars_setVar, ↓reduceIte, String.reduceEq, hmemv]; exact hoffv1)
    hmem hoff htgt halv hkix hstart hks hkof hKOf hktg hdone

/-! ### §2.4 Every row, and the whole pass -/

/-- **Every member's row.** Amortized, not counted: a turn costs the
member's raw row length, and the members' rows tile a part of the level's
target array, so the potential is "so much per member left, so much per
raw slot left". `RamDriverDedup.dedupRows_spec`'s argument at the member
list. -/
theorem compactRows_spec (hcsr : CsrSimple G nt O T)
    (hml : MemList n mm Mem (markSet n M)) (hKix : ∀ j, j < mm → Kix (Mem j) = j)
    (hB : mm + nt + 1 < B) (hnB : n < B) (hMB : ∀ v < n, M v < B) :
    Spec B (COuter n mm nt O T M Mem Kix)
      (.while (.lt (.var "km") (.var "mm")) cRow)
      (fun _ σ' => COuter n mm nt O T M Mem Kix σ' ∧ σ'.vars "km" = mm)
      (26 * mm + 24 * memRowSum mm O Mem + 4) := by
  refine (Spec.while_potential (COuter n mm nt O T M Mem Kix)
    (fun σ => 26 * (mm - σ.vars "km") +
      24 * (memRowSum mm O Mem - memRowSum (σ.vars "km") O Mem))
    (fun σ hσ => evalB_condLt_vars (by have := hσ.2.1; omega) (by rw [hσ.1]; omega))
    (fun σ hσ hb => ?_) (fun _ h => h)
    (fun σ _ => by simp only [size_condLt, size_var]; omega)).post (fun _ σ' _ hQ => ?_)
  · have hlt : σ.vars "km" < mm := by
      have h := lt_of_condLt_true hb
      rw [hσ.1] at h; exact h
    obtain ⟨σ', K, hrun, hK, hI', hi'⟩ := cRow_run hcsr hml hKix hB hnB hMB hlt hσ rfl
    refine ⟨σ', K, hrun, hI', ?_⟩
    have h₁ : memRowSum (σ.vars "km" + 1) O Mem
        = memRowSum (σ.vars "km") O Mem + Csr.rowLen O (Mem (σ.vars "km")) :=
      Finset.sum_range_succ _ _
    have h₂ : memRowSum (σ.vars "km" + 1) O Mem ≤ memRowSum mm O Mem :=
      memRowSum_mono (by omega)
    simp only [size_condLt, size_var, hi']
    omega
  · refine ⟨hQ.1, ?_⟩
    have h₀ := le_of_condLt_false hQ.2
    have h₁ := hQ.1.1
    have h₂ := hQ.1.2.1
    omega

/-- **The row loop's entry state.** `kof[0] := 0; ks := 0; km := 0` opens
the first block and publishes nothing. -/
theorem cOuter_entry {σ : Env} {g₁ g₂ : ℕ → ℕ}
    (hmm : σ.vars "mm" = mm) (harena : CArena n nt O T M Mem Kix σ)
    (hg₁ : σ.arrs "kof" = arrOf (n + 1) g₁) (hg₂ : σ.arrs "ktg" = arrOf nt g₂) :
    COuter n mm nt O T M Mem Kix (((σ.setArr "kof" 0 0).setVar "ks" 0).setVar "km" 0) := by
  obtain ⟨hmem, hoff, htgt, halv, hkix⟩ := harena
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨upd g₁ 0 0, ?_, ?_⟩, g₂, ?_, ?_⟩
  · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
      String.reduceEq, hg₁, hg₂, set_arrOf_eq_upd]) <;> exact hmm
  · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
      String.reduceEq, hg₁, hg₂, set_arrOf_eq_upd]) <;> exact Nat.zero_le _
  · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
      String.reduceEq, hg₁, hg₂, set_arrOf_eq_upd]) <;> exact hmem
  · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
      String.reduceEq, hg₁, hg₂, set_arrOf_eq_upd]) <;> exact hoff
  · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
      String.reduceEq, hg₁, hg₂, set_arrOf_eq_upd]) <;> exact htgt
  · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
      String.reduceEq, hg₁, hg₂, set_arrOf_eq_upd]) <;> exact halv
  · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
      String.reduceEq, hg₁, hg₂, set_arrOf_eq_upd]) <;> exact hkix
  · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
      String.reduceEq, hg₁, hg₂, set_arrOf_eq_upd]) <;> exact cOff_zero.symm
  · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
      String.reduceEq, hg₁, hg₂, set_arrOf_eq_upd]) <;> rfl
  · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
      String.reduceEq, hg₁, hg₂, set_arrOf_eq_upd]) <;>
      (intro i hi; rw [show i = 0 by omega, upd_self, cOff_zero])
  · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
      String.reduceEq, hg₁, hg₂, set_arrOf_eq_upd]) <;> rfl
  · (try simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
      String.reduceEq, hg₁, hg₂, set_arrOf_eq_upd]) <;> (intro y hy; omega)

/-- **The compacted CSR, built.** The offsets in `kof` over `mm + 1`
cells, the targets in `ktg` over the compact slot count, which the pass
leaves in `ks`. -/
theorem compactCsr_run (hcsr : CsrSimple G nt O T)
    (hml : MemList n mm Mem (markSet n M)) (hKix : ∀ j, j < mm → Kix (Mem j) = j)
    (hB : mm + nt + 1 < B) (hnB : n < B) (hMB : ∀ v < n, M v < B) {σ : Env}
    (hmm : σ.vars "mm" = mm) (harena : CArena n nt O T M Mem Kix σ)
    (hkof : ∃ g, σ.arrs "kof" = arrOf (n + 1) g)
    (hktg : ∃ g, σ.arrs "ktg" = arrOf nt g) :
    ∃ σ' K, Run B compactCsr σ σ' K ∧ K ≤ 26 * mm + 24 * memRowSum mm O Mem + 11 ∧
      COuter n mm nt O T M Mem Kix σ' ∧ σ'.vars "km" = mm := by
  classical
  obtain ⟨g₁, hg₁⟩ := hkof
  obtain ⟨g₂, hg₂⟩ := hktg
  have hkofLen : (σ.arrs "kof").length = n + 1 := by rw [hg₁, length_arrOf]
  have hrows := compactRows_spec hcsr hml hKix hB hnB hMB
  run_vcg [hrows]
  · assumption
  all_goals first
    | omega
    | (simp only [arrs_setVar, vars_setVar, ↓reduceIte, String.reduceEq, hkofLen] at *; omega)
    | exact cOuter_entry hmm harena hg₁ hg₂

/-- `cixPass` writes only `kix`. -/
theorem notMem_cixPass_warrs {a : String} (h : a ≠ "kix") : a ∉ cixPass.warrs := by
  simp [cixPass, Com.warrs, h]

/-- `compactCsr` writes only `kof` and `ktg`. -/
theorem notMem_compactCsr_warrs {a : String} (h₁ : a ≠ "kof") (h₂ : a ≠ "ktg") :
    a ∉ compactCsr.warrs := by
  simp [compactCsr, cRow, Com.warrs, h₁, h₂]

/-- **The renumbering, both halves.** `ElimCompactWalks.cixPass_run` and
§2.4, sequenced: the inverse numbering and the compacted CSR, at
`40·mm + 24·rs + 17` ticks, and everything else in the store untouched. -/
theorem compactPass_run {O T M Mem : ℕ → ℕ} (hcsr : CsrSimple G nt O T)
    (hml : MemList n mm Mem (markSet n M))
    (hB : mm + nt + 1 < B) (hnB : n < B) (hMB : ∀ v < n, M v < B) {σ : Env}
    (hmm : σ.vars "mm" = mm) (hmem : σ.arrs "mem" = arrOf n Mem)
    (hoff : σ.arrs "off" = arrOf (n + 1) O) (htgt : σ.arrs "tgt" = arrOf nt T)
    (halv : σ.arrs "alv" = arrOf n M) (hkix : ∃ g, σ.arrs "kix" = arrOf n g)
    (hkof : ∃ g, σ.arrs "kof" = arrOf (n + 1) g)
    (hktg : ∃ g, σ.arrs "ktg" = arrOf nt g) :
    ∃ (σ' : Env) (Kix KOf KT : ℕ → ℕ),
      Run B compactPass σ σ' (40 * mm + 24 * memRowSum mm O Mem + 17) ∧
      (∀ j, j < mm → Kix (Mem j) = j) ∧
      σ'.vars "mm" = mm ∧ σ'.vars "ks" = cOff O T M Mem Kix mm ∧
      σ'.arrs "kof" = arrOf (n + 1) KOf ∧ (∀ i ≤ mm, KOf i = cOff O T M Mem Kix i) ∧
      σ'.arrs "ktg" = arrOf nt KT ∧ CDone O T M Mem Kix KT mm ∧
      (∀ a, a ≠ "kix" → a ≠ "kof" → a ≠ "ktg" → σ'.arrs a = σ.arrs a) := by
  obtain ⟨σ₁, Kix, r₁, hkix₁, hKix, hmm₁, hmem₁⟩ :=
    Lax3Proofs.Refine.ElimCompactWalks.cixPass_run (B := B) hnB hmm hmem
      (fun j hj => hml.lt j hj) (fun i j hij hj => hml.smono i j hij hj) hkix
  have hfr₁ : ∀ a, a ≠ "kix" → σ₁.arrs a = σ.arrs a := fun a ha =>
    r₁.frame_arr a (notMem_cixPass_warrs ha)
  obtain ⟨σ₂, K₂, r₂, hK₂, hout, hkm₂⟩ :=
    compactCsr_run hcsr hml hKix hB hnB hMB hmm₁
      ⟨hmem₁, by rw [hfr₁ "off" (by decide), hoff],
        by rw [hfr₁ "tgt" (by decide), htgt], by rw [hfr₁ "alv" (by decide), halv], hkix₁⟩
      (by obtain ⟨g, hg⟩ := hkof; exact ⟨g, by rw [hfr₁ "kof" (by decide), hg]⟩)
      (by obtain ⟨g, hg⟩ := hktg; exact ⟨g, by rw [hfr₁ "ktg" (by decide), hg]⟩)
  obtain ⟨hmm₂, -, -, hks₂, ⟨KOf, hkof₂, hKOf⟩, KT, hktg₂, hdone⟩ := hout
  rw [hkm₂] at hks₂ hKOf hdone
  refine ⟨σ₂, Kix, KOf, KT, (r₁.seq r₂).mono ?_, hKix, hmm₂, hks₂, hkof₂, hKOf, hktg₂,
    hdone, fun a h₁ h₂ h₃ => ?_⟩
  · omega
  · rw [r₂.frame_arr a (notMem_compactCsr_warrs h₂ h₃), hfr₁ a h₁]

/-! ### §2.5 What the pass built is the engine's input surface -/

/-- Everything a closed block names is a compact vertex. -/
theorem cDone_target_lt (hcsr : CsrSimple G nt O T) (hml : MemList n mm Mem (markSet n M))
    (hKix : ∀ j, j < mm → Kix (Mem j) = j) {KT : ℕ → ℕ}
    (hdone : CDone O T M Mem Kix KT mm) {k : ℕ} (hk : k < cOff O T M Mem Kix mm) :
    KT k < mm := by
  obtain ⟨z, hz₁, hz₂, hz₃⟩ := Lax3Proofs.RamDriverAugment.exists_block_of_mono
    (O := cOff O T M Mem Kix) (nv := mm) (s := cOff O T M Mem Kix mm)
    cOff_zero rfl (fun i _ => cOff_mono (Nat.le_succ i)) hk
  exact cNbr_lt hcsr hml hKix hz₁ ((hdone z hz₁).1 k hz₂ hz₃)

/-- **`CompactInstalls`' correctness content.** Soundness and completeness
of every closed block give the block structure of the compacted arena;
the block being exactly as long as its compact row gives `nodup`, which
is `RamDriverAugment.block_nodup` — the same argument
`Symmetrize.csrSimple_of_rowsDone` runs, at the member pullback instead
of the symmetrized orientation.

The target function is the caller's, not the pass's: the install copies
only the first `cs` cells of `ktg` into `tgt`, so what the engine reads
above `cs` is the level's own targets. Every clause of `CsrSimple` here
looks only at slots below `cOff mm`, so the merged function does. -/
theorem csrSimple_of_done (hcsr : CsrSimple G nt O T)
    (hml : MemList n mm Mem (markSet n M)) (hKix : ∀ j, j < mm → Kix (Mem j) = j)
    {KT T' : ℕ → ℕ} (hdone : CDone O T M Mem Kix KT mm)
    (hT' : ∀ k, k < cOff O T M Mem Kix mm → T' k = KT k) :
    CsrSimple (memGraph G M hml) (cOff O T M Mem Kix mm) (cOff O T M Mem Kix) T' := by
  classical
  refine ⟨⟨cOff_zero, rfl, fun i _ => cOff_mono (Nat.le_succ i), fun j hj => ?_,
    fun u v => ?_⟩, fun u hu j₁ j₂ a₁ a₂ a₃ a₄ he => ?_⟩
  · rw [hT' j hj]; exact cDone_target_lt hcsr hml hKix hdone hj
  · have hble : cOff O T M Mem Kix ((u : ℕ) + 1) ≤ cOff O T M Mem Kix mm :=
      cOff_mono (by omega)
    constructor
    · intro hadj
      obtain ⟨p, h₁, h₂, h₃⟩ := (hdone (u : ℕ) u.isLt).2 (v : ℕ)
        ((mem_cNbr_iff hcsr hml hKix u.isLt v.isLt).2 hadj)
      exact ⟨p, h₁, h₂, by rw [hT' p (by omega)]; exact h₃⟩
    · rintro ⟨p, h₁, h₂, h₃⟩
      have hm := (hdone (u : ℕ) u.isLt).1 p h₁ h₂
      rw [hT' p (by omega)] at h₃
      have hlt : KT p < mm := cNbr_lt hcsr hml hKix u.isLt hm
      have hadj := (mem_cNbr_iff hcsr hml hKix u.isLt hlt).1 hm
      rwa [show (⟨KT p, hlt⟩ : Fin mm) = v from Fin.ext h₃] at hadj
  · have hble : cOff O T M Mem Kix (u + 1) ≤ cOff O T M Mem Kix mm := cOff_mono (by omega)
    refine Lax3Proofs.RamDriverAugment.block_nodup (S := cNbr O T M Mem Kix u)
      (by rw [cOff_succ]; omega) (cOff_mono (Nat.le_succ u)) (fun q hq₁ hq₂ => ?_)
      (fun w hw => ?_) a₁ a₂ a₃ a₄ he
    · rw [hT' q (by omega)]; exact (hdone u hu).1 q hq₁ hq₂
    · obtain ⟨q, b₁, b₂, b₃⟩ := (hdone u hu).2 w hw
      exact ⟨q, b₁, b₂, by rw [hT' q (by omega)]; exact b₃⟩

end Walk

/-! ## §3 The install, and the obligation

`installCom` is five prefix passes and one assignment. Every one of the
five runs to a bound at the **arena's** carrier and keeps the tail of a
carrier-length array — `RamDriverOrder.fillKeep_spec`, which is exactly
the live-prefix reading `ElimCompact` §3 closes the length seam with. -/

section Install

variable {B n mm nt W : ℕ}

/-- A prefix pass writes its own array and the kit's counter. -/
theorem notMem_fillUpto_warrs {a b : String} {bnd e : Expr} (h : b ≠ a) :
    b ∉ (fillUpto a bnd e).warrs := by
  simp [fillUpto, Fill.put, Com.warrs, h]

theorem notMem_fillUpto_wvars {a y : String} {bnd e : Expr} (h : y ≠ "i") :
    y ∉ (fillUpto a bnd e).wvars := by
  simp [fillUpto, Fill.put, Com.wvars, h]

/-- **The engine's entry, installed.** The compact offsets over `mm + 1`
cells, the compact targets over `cs`, the all-alive mask and the two
zeroed scratch prefixes over the arena's carrier, and the carrier scalar
moved to `mm`. Nothing here is carrier-bounded — which is the zero-seam
of `OrderEngineProbe` §2 dead — and every pass keeps the tail it did not
write, which is what makes the exit state the compact answer over the
store's own arrays. `49·mm + 12·cs + 63` ticks. -/
theorem installCom_run {O' T KOf KT : ℕ → ℕ} {cs : ℕ} {σ : Env}
    (hB : mm + nt + 1 < B) (hmn : mm ≤ n) (hcs : cs ≤ nt)
    (hmm : σ.vars "mm" = mm) (hks : σ.vars "ks" = cs)
    (hkof : σ.arrs "kof" = arrOf (n + 1) KOf) (hKOf : ∀ i, i ≤ mm → KOf i = O' i)
    (hO'B : ∀ i, i ≤ mm → O' i < B)
    (hktg : σ.arrs "ktg" = arrOf nt KT) (hKTB : ∀ k, k < cs → KT k < B)
    (hoff : ∃ g, σ.arrs "off" = arrOf (n + 1) g) (htgt : σ.arrs "tgt" = arrOf nt T)
    (halv : ∃ g, σ.arrs "alv" = arrOf n g) (helm : ∃ g, σ.arrs "elm" = arrOf n g)
    (hbh : ∃ g, σ.arrs "bh" = arrOf (n + 1) g) :
    ∃ σ' K, Run B installCom σ σ' K ∧ K ≤ 49 * mm + 12 * cs + 63 ∧
      σ'.vars "n" = mm ∧ σ'.vars "mm" = mm ∧
      (∃ g, σ'.arrs "off" = arrOf (n + 1) g ∧ ∀ i, i ≤ mm → g i = O' i) ∧
      σ'.arrs "tgt" = arrOf nt (fun k => if k < cs then KT k else T k) ∧
      (∃ g, σ'.arrs "alv" = arrOf n g ∧ ∀ v, v < mm → g v = 1) ∧
      (∃ g, σ'.arrs "elm" = arrOf n g ∧ ∀ v, v < mm → g v = 0) ∧
      (∃ g, σ'.arrs "bh" = arrOf (n + 1) g ∧ ∀ i, i ≤ mm → g i = 0) ∧
      (∀ a, a ≠ "off" → a ≠ "tgt" → a ≠ "alv" → a ≠ "elm" → a ≠ "bh" →
        σ'.arrs a = σ.arrs a) := by
  classical
  -- **the compact offsets**, into the engine's own array
  have hp1 := Lax3Proofs.RamDriverOrder.fillKeep_spec (B := B) (mm + 1) (n + 1) "off"
    (.add (.var "mm") (.lit 1)) (.get "kof" (.var "i")) O'
    (fun τ => τ.vars "mm" = mm ∧ τ.arrs "kof" = arrOf (n + 1) KOf)
    (by omega) (by omega) (by omega)
    (fun τ τ' hQ hv ha => ⟨by rw [← hQ.1]; exact hv "mm" (by decide),
      by rw [← hQ.2]; exact ha "kof" (by decide)⟩)
    (fun τ hQ => by
      have h := evalB_bin (op := .add) (B := B) (σ := τ)
        (evalB_var (x := "mm") (by rw [hQ.1]; omega)) (evalB_lit (B := B) (n := 1) (by omega))
        (by rw [Bop.apply_add, hQ.1]; omega)
      rwa [Bop.apply_add, hQ.1] at h)
    (fun τ hQ hi => evalB_get (evalB_var (by omega))
      (by rw [hQ.2, getElem?_arrOf (n := n + 1) KOf (show τ.vars "i" < n + 1 by omega),
        hKOf _ (by omega)]) (hO'B _ (by omega)))
  obtain ⟨σ₁, r₁, ⟨O₁, hO₁, hO₁lo, -⟩, -, -⟩ := hp1 σ ⟨hoff, hmm, hkof⟩
  have f₁ : ∀ a, a ≠ "off" → σ₁.arrs a = σ.arrs a := fun a ha =>
    r₁.frame_arr a (notMem_fillUpto_warrs ha)
  have v₁ : ∀ y, y ≠ "i" → σ₁.vars y = σ.vars y := fun y hy =>
    r₁.frame_var y (notMem_fillUpto_wvars hy)
  -- **the compact targets**, over the live slot count and no further
  have hp2 := Lax3Proofs.RamDriverOrder.fillKeep_spec (B := B) cs nt "tgt"
    (.var "ks") (.get "ktg" (.var "i")) KT
    (fun τ => τ.vars "ks" = cs ∧ τ.arrs "ktg" = arrOf nt KT)
    (by omega) (by omega) hcs
    (fun τ τ' hQ hv ha => ⟨by rw [← hQ.1]; exact hv "ks" (by decide),
      by rw [← hQ.2]; exact ha "ktg" (by decide)⟩)
    (fun τ hQ => by rw [← hQ.1]; exact evalB_var (by rw [hQ.1]; omega))
    (fun τ hQ hi => evalB_get (evalB_var (by omega))
      (by rw [hQ.2, getElem?_arrOf (n := nt) KT (show τ.vars "i" < nt by omega)])
      (hKTB _ hi))
  obtain ⟨σ₂, r₂, ⟨T₂, hT₂, hT₂lo, hT₂hi⟩, -, -⟩ :=
    hp2 σ₁ ⟨⟨T, by rw [f₁ "tgt" (by decide), htgt]⟩,
      by rw [v₁ "ks" (by decide), hks], by rw [f₁ "ktg" (by decide), hktg]⟩
  have f₂ : ∀ a, a ≠ "tgt" → σ₂.arrs a = σ₁.arrs a := fun a ha =>
    r₂.frame_arr a (notMem_fillUpto_warrs ha)
  have v₂ : ∀ y, y ≠ "i" → σ₂.vars y = σ₁.vars y := fun y hy =>
    r₂.frame_var y (notMem_fillUpto_wvars hy)
  -- **the mask**: compaction made the dead vertices nonexistent
  have hp3 := Lax3Proofs.RamDriverOrder.fillKeep_spec (B := B) mm n "alv"
    (.var "mm") (.lit 1) (fun _ => 1) (fun τ => τ.vars "mm" = mm)
    (by omega) (by omega) hmn
    (fun τ τ' hQ hv _ => by rw [← hQ]; exact hv "mm" (by decide))
    (fun τ hQ => by rw [← hQ]; exact evalB_var (by rw [hQ]; omega))
    (fun _ _ _ => evalB_lit (by omega))
  obtain ⟨σ₃, r₃, ⟨A₃, hA₃, hA₃lo, -⟩, -, -⟩ :=
    hp3 σ₂ ⟨(by obtain ⟨g, hg⟩ := halv
                exact ⟨g, by rw [f₂ "alv" (by decide), f₁ "alv" (by decide), hg]⟩),
      show σ₂.vars "mm" = mm by rw [v₂ "mm" (by decide), v₁ "mm" (by decide), hmm]⟩
  have f₃ : ∀ a, a ≠ "alv" → σ₃.arrs a = σ₂.arrs a := fun a ha =>
    r₃.frame_arr a (notMem_fillUpto_warrs ha)
  have v₃ : ∀ y, y ≠ "i" → σ₃.vars y = σ₂.vars y := fun y hy =>
    r₃.frame_var y (notMem_fillUpto_wvars hy)
  -- **the two zeroed scratch prefixes**, both at the arena's carrier
  have hp4 := Lax3Proofs.RamDriverOrder.fillKeep_spec (B := B) mm n "elm"
    (.var "mm") (.lit 0) (fun _ => 0) (fun τ => τ.vars "mm" = mm)
    (by omega) (by omega) hmn
    (fun τ τ' hQ hv _ => by rw [← hQ]; exact hv "mm" (by decide))
    (fun τ hQ => by rw [← hQ]; exact evalB_var (by rw [hQ]; omega))
    (fun _ _ _ => evalB_lit (by omega))
  obtain ⟨σ₄, r₄, ⟨E₄, hE₄, hE₄lo, -⟩, -, -⟩ :=
    hp4 σ₃ ⟨(by obtain ⟨g, hg⟩ := helm
                exact ⟨g, by rw [f₃ "elm" (by decide), f₂ "elm" (by decide),
                  f₁ "elm" (by decide), hg]⟩),
      show σ₃.vars "mm" = mm by
        rw [v₃ "mm" (by decide), v₂ "mm" (by decide), v₁ "mm" (by decide), hmm]⟩
  have f₄ : ∀ a, a ≠ "elm" → σ₄.arrs a = σ₃.arrs a := fun a ha =>
    r₄.frame_arr a (notMem_fillUpto_warrs ha)
  have v₄ : ∀ y, y ≠ "i" → σ₄.vars y = σ₃.vars y := fun y hy =>
    r₄.frame_var y (notMem_fillUpto_wvars hy)
  have hp5 := Lax3Proofs.RamDriverOrder.fillKeep_spec (B := B) (mm + 1) (n + 1) "bh"
    (.add (.var "mm") (.lit 1)) (.lit 0) (fun _ => 0) (fun τ => τ.vars "mm" = mm)
    (by omega) (by omega) (by omega)
    (fun τ τ' hQ hv _ => by rw [← hQ]; exact hv "mm" (by decide))
    (fun τ hQ => by
      have h := evalB_bin (op := .add) (B := B) (σ := τ)
        (evalB_var (x := "mm") (by rw [hQ]; omega)) (evalB_lit (B := B) (n := 1) (by omega))
        (by rw [Bop.apply_add, hQ]; omega)
      rwa [Bop.apply_add, hQ] at h)
    (fun _ _ _ => evalB_lit (by omega))
  obtain ⟨σ₅, r₅, ⟨H₅, hH₅, hH₅lo, -⟩, -, hmm₅⟩ :=
    hp5 σ₄ ⟨(by obtain ⟨g, hg⟩ := hbh
                exact ⟨g, by rw [f₄ "bh" (by decide), f₃ "bh" (by decide),
                  f₂ "bh" (by decide), f₁ "bh" (by decide), hg]⟩),
      show σ₄.vars "mm" = mm by
        rw [v₄ "mm" (by decide), v₃ "mm" (by decide), v₂ "mm" (by decide),
          v₁ "mm" (by decide), hmm]⟩
  have f₅ : ∀ a, a ≠ "bh" → σ₅.arrs a = σ₄.arrs a := fun a ha =>
    r₅.frame_arr a (notMem_fillUpto_warrs ha)
  -- **the carrier scalar**, at the arena
  have r₆ : Run B (.assign "n" (.var "mm")) σ₅ (σ₅.setVar "n" mm) (1 + (Expr.var "mm").size) := by
    have := Run.assign (B := B) (σ := σ₅) (x := "n") (e := .var "mm")
      (evalB_var (by rw [hmm₅]; omega))
    rwa [hmm₅] at this
  refine ⟨σ₅.setVar "n" mm, _, r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq r₆)))), ?_,
    by simp, by simp [hmm₅], ⟨O₁, ?_, fun i hi => hO₁lo i (by omega)⟩, ?_,
    ⟨A₃, ?_, fun v hv => hA₃lo v hv⟩, ⟨E₄, ?_, fun v hv => hE₄lo v hv⟩,
    ⟨H₅, ?_, fun i hi => hH₅lo i (by omega)⟩, fun a h₁ h₂ h₃ h₄ h₅ => ?_⟩
  · simp only [size_get, size_var, size_add, size_lit]
    omega
  · simp only [arrs_setVar]
    rw [f₅ "off" (by decide), f₄ "off" (by decide), f₃ "off" (by decide),
      f₂ "off" (by decide), hO₁]
  · simp only [arrs_setVar]
    rw [f₅ "tgt" (by decide), f₄ "tgt" (by decide), f₃ "tgt" (by decide), hT₂]
    refine arrOf_congr fun k hk => ?_
    rcases Nat.lt_or_ge k cs with hlt | hge
    · rw [hT₂lo k hlt, if_pos hlt]
    · rw [hT₂hi k hge hk, if_neg (by omega), f₁ "tgt" (by decide), htgt,
        getD_arrOf T hk]
  · simp only [arrs_setVar]
    rw [f₅ "alv" (by decide), f₄ "alv" (by decide), hA₃]
  · simp only [arrs_setVar]
    rw [f₅ "elm" (by decide), hE₄]
  · simp only [arrs_setVar]; exact hH₅
  · simp only [arrs_setVar]
    rw [f₅ a h₅, f₄ a h₄, f₃ a h₃, f₂ a h₂, f₁ a h₁]

/-! ### §3.1 The obligation -/

/-- **`ElimCompact.CompactInstalls`, discharged.**

`compactPass` renumbers (`ElimCompactWalks.cixPass_run` and §2.4) and
`installCom` installs (§3), at `40·mm + 24·rs + 17` and
`49·mm + 12·cs + 63` ticks respectively — inside `compactCostRaw mm rs`
with room, since `cs ≤ rs`. What comes out is a `RamElim.CsrSimple` block
structure of the member pullback `memGraph G M hml` at the compact slot
count, installed in the engine's own array names, with the all-alive mask
(compaction made the dead vertices nonexistent) and the two zeroed
prefixes, and with the carrier scalar at `mm`.

The two size clauses are the ones `ElimCompactWalks` §3 asked for:
`cs ≤ memRowSum mm O Mem` because a row's live slots are a subset of its
raw slots, and `cs ≤ nt` because the members are distinct vertices, so
their rows tile a part of the level's target array. -/
theorem compactInstalls {B n mm nt W : ℕ} {G : SimpleGraph (Fin n)} {M Mem : ℕ → ℕ} :
    CompactInstalls B n mm nt W G M Mem := by
  classical
  intro O T σ hml hcsr hent hB hnB hMB
  obtain ⟨hn, hmm, hmn, hoff, htgt, halv, hmem, hkof, hktg, hkix, hork, hdeg, helm,
    hrnk, hidg, hbh, hbv, hbn, hioff, hifl, hitg⟩ := hent
  obtain ⟨σ₁, Kix, KOf, KT, r₁, hKix, hmm₁, hks₁, hkof₁, hKOf, hktg₁, hdone, hfr₁⟩ :=
    compactPass_run hcsr hml hB hnB hMB hmm hmem hoff htgt halv hkix hkof hktg
  have hcsrs : cOff O T M Mem Kix mm ≤ memRowSum mm O Mem :=
    cOff_le_memRowSum hcsr hml hKix
  have hrsnt : memRowSum mm O Mem ≤ nt := memRowSum_le hcsr hml
  have hcsnt : cOff O T M Mem Kix mm ≤ nt := le_trans hcsrs hrsnt
  have hO'B : ∀ i, i ≤ mm → cOff O T M Mem Kix i < B := fun i hi => by
    have := cOff_mono (O := O) (T := T) (M := M) (Mem := Mem) (Kix := Kix) hi
    omega
  have hKTB : ∀ k, k < cOff O T M Mem Kix mm → KT k < B := fun k hk => by
    have := cDone_target_lt hcsr hml hKix hdone hk
    omega
  obtain ⟨σ₂, K₂, r₂, hK₂, hn₂, hmm₂, hoff₂, htgt₂, halv₂, helm₂, hbh₂, hfr₂⟩ :=
    installCom_run (T := T) (KOf := KOf) (KT := KT) hB hmn hcsnt hmm₁ hks₁ hkof₁ hKOf
      hO'B hktg₁ hKTB
      ⟨O, by rw [hfr₁ "off" (by decide) (by decide) (by decide), hoff]⟩
      (by rw [hfr₁ "tgt" (by decide) (by decide) (by decide), htgt])
      ⟨M, by rw [hfr₁ "alv" (by decide) (by decide) (by decide), halv]⟩
      (by obtain ⟨g, hg⟩ := helm
          exact ⟨g, by rw [hfr₁ "elm" (by decide) (by decide) (by decide), hg]⟩)
      (by obtain ⟨g, hg⟩ := hbh
          exact ⟨g, by rw [hfr₁ "bh" (by decide) (by decide) (by decide), hg]⟩)
  -- the frame of the composite, for the arrays neither half writes
  have hfr : ∀ a, a ≠ "kix" → a ≠ "kof" → a ≠ "ktg" → a ≠ "off" → a ≠ "tgt" → a ≠ "alv" →
      a ≠ "elm" → a ≠ "bh" → σ₂.arrs a = σ.arrs a := fun a h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ => by
    rw [hfr₂ a h₄ h₅ h₆ h₇ h₈, hfr₁ a h₁ h₂ h₃]
  refine ⟨σ₂, cOff O T M Mem Kix, (fun k => if k < cOff O T M Mem Kix mm then KT k else T k),
    cOff O T M Mem Kix mm, (r₁.seq r₂).mono ?_,
    csrSimple_of_done hcsr hml hKix hdone (fun k hk => if_pos hk),
    hcsrs, hcsnt,
    ⟨hn₂, hmn, hoff₂, htgt₂, halv₂, ?_, helm₂, ?_, ?_, hbh₂, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, hmm₂, ?_⟩
  · simp only [compactCostRaw]
    have : cOff O T M Mem Kix mm ≤ memRowSum mm O Mem := hcsrs
    omega
  · obtain ⟨g, hg⟩ := hdeg
    exact ⟨g, by rw [hfr "deg" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hg]⟩
  · obtain ⟨g, hg⟩ := hrnk
    exact ⟨g, by rw [hfr "rnk" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hg]⟩
  · obtain ⟨g, hg⟩ := hidg
    exact ⟨g, by rw [hfr "idg" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hg]⟩
  · obtain ⟨g, hg⟩ := hbv
    exact ⟨g, by rw [hfr "bv" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hg]⟩
  · obtain ⟨g, hg⟩ := hbn
    exact ⟨g, by rw [hfr "bn" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hg]⟩
  · obtain ⟨g, hg⟩ := hioff
    exact ⟨g, by rw [hfr "ioff" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hg]⟩
  · obtain ⟨g, hg⟩ := hifl
    exact ⟨g, by rw [hfr "ifl" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hg]⟩
  · obtain ⟨g, hg⟩ := hitg
    exact ⟨g, by rw [hfr "itg" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hg]⟩
  · rw [hfr "mem" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hmem]
  · obtain ⟨g, hg⟩ := hork
    exact ⟨g, by rw [hfr "ork" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hg]⟩

end Install

/-! ## §4 The charge, compiled

The two-sided reading of the cost clause, on `ElimCompactWalks` §3.1's
dead-row star (`mm = 1`, one member whose forty raw slots are all dead,
so `cs = 0` and `rs = 40`). The budget holds; a **slot-blind** budget —
the same function read at zero raw slots, i.e. any `c·mm + c'` charge —
does not, so the raw-row term of `compactCostRaw` is load-bearing and not
slack. The clock's own pin is exact to the tick. -/

open Lax3Proofs.Refine.ElimCompactWalks (deadClock)

#guard deadClock 100 128 = 849
#guard deadClock 100 128 ≤ compactCostRaw 1 40
#guard compactCostRaw 1 40 = 4400
-- the honesty direction on the clock: the pin is exact
#guard ¬ (deadClock 100 128 ≤ 848)
-- the honesty direction on the shape: without the raw-slot term the
-- charge is `400` and the walk does not fit it
#guard compactCostRaw 1 0 = 400
#guard ¬ (deadClock 100 128 ≤ compactCostRaw 1 0)
-- the two halves this file actually proves, added up on the same
-- instance: `compactPass` inside `40·mm + 24·rs + 17` and `installCom`
-- inside `49·mm + 12·cs + 63`
#guard deadClock 100 128 ≤ (40 * 1 + 24 * 40 + 17) + (49 * 1 + 12 * 0 + 63)
#guard (40 * 1 + 24 * 40 + 17) + (49 * 1 + 12 * 0 + 63) ≤ compactCostRaw 1 40
-- and carrier-blindness, which is the wave's whole claim
#guard deadClock 800 128 = 849

/-! ## §5 Axioms -/

#print axioms compactInstalls
#print axioms csrSimple_of_done
#print axioms compactPass_run
#print axioms installCom_run

end Lax3Proofs.Refine.ElimCompactCsr
