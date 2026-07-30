import Lax3Proofs.Refine.ElimSynth4

/-!
# P2 wave 2B‴ — the elimination engine, exported

`ElimSynth4` left three named debts (its §5): the elimination loop's
invariant transport across the four turns, the amortization out of the
four-term potential, and the exit reading. This wave pays all three and
composes the engine.

* §1 — the devices: `ACost` arithmetic and the two sequencing rules.
* §2 — the potential the loop is paid out of, and the variant.
* §3 — the four turns: each one preserves `ElimI`, drops the variant
  and pays for itself out of the potential.
* §4 — the loop, run.
* §5 — the exit reading, and the loop's export.
* §6 — the loop's cost, cashed.
* §7 — the whole engine, composed, with its negative controls.
* §8 — what is landed and what is left.
* §9 — axioms.

## House traps observed

`omega` is blind through a tuple projection — every arithmetic clause
of a structure over `DS`/`ES` needs its `show`. `decide +kernel` for
the cashed constants. Never `simp [Codegen.embed]`.
-/

namespace Lax3Proofs.Refine.ElimSynth5

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax13Proofs.Refine.Codegen
open Lax13Proofs.Refine.BfsQ (Shape cu iter irWhile_exit get!_set res_of_le liftACost_cu)
open Lax3Proofs.Refine.ElimSynth hiding mopSucc mopSucc_eq mopKeep mopKeep_eq
open Lax3Proofs.Refine.ElimSynth2
open Lax3Proofs.Refine.ElimSynth3
open Lax3Proofs.Refine.ElimSynth4

/-! ## 1. Devices -/

section Devices

/-- A price is at most itself plus another, at the `ℕ` layer the
potential is written in. -/
theorem acost_le_add (a b : ACost String ℕ) : a ≤ a + b := by
  rw [← liftACost_le_iff, liftACost_add]; exact cost_le_add _ _

/-- **The workhorse of the amortization**: a smaller multiple of a
price is a smaller price. -/
theorem nsmul_le_nsmul' {a b : ℕ} (h : a ≤ b) (x : ACost String ℕ) : a • x ≤ b • x := by
  rw [show b = a + (b - a) by omega, add_nsmul]
  exact acost_le_add _ _

/-- Sequencing two bounded programs adds their prices. -/
theorem seqA_le {α β : Type} {m : NRest α ECost} {f : α → NRest β ECost} {P : α → Prop}
    {Q : β → Prop} {c d : ACost String ℕ}
    (hm : m ≤ NRest.spec P (fun _ => liftACost c))
    (hf : ∀ x, P x → f x ≤ NRest.spec Q (fun _ => liftACost d)) :
    NRest.bindT m f ≤ NRest.spec Q (fun _ => liftACost (c + d)) :=
  le_trans (le_trans (NRest.bindT_mono hm fun _ => le_rfl)
      (bindT_spec_le P (liftACost c) f Q (liftACost d) hf))
    (spec_mono (fun _ h => h) (fun _ _ => le_of_eq (liftACost_add c d).symm))

/-- Reading a bounded program's result through a function costs
nothing. -/
theorem bindA_ret {α β : Type} {m : NRest α ECost} {P : α → Prop} {Q : β → Prop}
    {c : ACost String ℕ} {g : α → β} (hm : m ≤ NRest.spec P (fun _ => liftACost c))
    (hg : ∀ x, P x → Q (g x)) :
    NRest.bindT m (fun x => NRest.returnT (g x)) ≤ NRest.spec Q (fun _ => liftACost c) := by
  refine le_trans (le_trans (NRest.bindT_mono hm fun _ => le_rfl)
    (bindT_spec_le P (liftACost c) _ Q 0 (fun x hx => ?_))) (spec_mono (fun _ h => h) ?_)
  · rw [← NRest.consume_zero (NRest.returnT (g x))]
    exact consume_returnT_le_spec (hg x hx) le_rfl
  · exact fun _ _ => le_of_eq (add_zero _)

end Devices

/-! ## 2. The potential, and the variant

`RamElim.Pot`'s four terms, denominated in the tower's own prices:
`ElimSynth4` §4.5 cashes them at `25`, `44`, `104` and `132`. -/

section Potential

/-- A pointer bump's price — the first term. -/
def A1 : ACost String ℕ := iter bumpC

/-- A stale pop's — the second. -/
def A2 : ACost String ℕ := iter staleC

/-- A slot of a row scan, with the pop its push will one day pay for —
the third. -/
def A3 : ACost String ℕ := iter decC + A2

/-- An extraction outside its scan, with the bump the pointer's drop
will one day cost — the fourth. -/
def A4 : ACost String ℕ := iter (takeC0 + cu Currency.«while») + A1

/-- The four terms, at four counts. -/
def pot4 (m l s c : ℕ) : ACost String ℕ := m • A1 + l • A2 + s • A3 + c • A4

/-- **The potential the elimination loop is paid out of.** `ls` and
`sc` are read off the state by `lsOf` and `scOf` (2B′/D-a). -/
def elimPot (n ns : ℕ) (off alv : List ℕ) (e : ES) : ACost String ℕ :=
  pot4 (n + 1 - e.2.2.2.2.2.2.2.2.2.1) (lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1)
    (ns - scOf n (larr off) (larr alv) e.2.1) (n - e.2.2.2.2.2.2.2.2.1)

/-- Every term of the potential is monotone in its count. -/
theorem pot4_mono {m l s c m' l' s' c' : ℕ} (hm : m ≤ m') (hl : l ≤ l') (hs : s ≤ s')
    (hc : c ≤ c') : pot4 m l s c ≤ pot4 m' l' s' c' :=
  add_le_add (add_le_add (add_le_add (nsmul_le_nsmul' hm _) (nsmul_le_nsmul' hl _))
    (nsmul_le_nsmul' hs _)) (nsmul_le_nsmul' hc _)

/-- **The loop's variant.** `cnt` alone does not decrease — a bump and
a stale pop leave it standing — so the variant is the potential's own
shape at the smallest coefficients that make all four turns drop it. -/
def elimV (n ns : ℕ) (off alv : List ℕ) (e : ES) : ℕ :=
  (n + 1 - e.2.2.2.2.2.2.2.2.2.1) + lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1
    + 3 * (ns - scOf n (larr off) (larr alv) e.2.1)
    + 3 * (n - e.2.2.2.2.2.2.2.2.1)

/-- **What a live extraction pays over a dead one**: the row's two
offsets, the index bump and the five `skip`s the row load assembles. -/
def rowLoadC : ACost String ℕ := cu Currency.aget + cu Currency.aget + cu Currency.add
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip

/-- **2B‴/T-a — a forty-term `ac_rfl` does not terminate**, and does not
have to: two costs are equal when they are equal at every currency, and
at a currency the claim is linear arithmetic over the atoms `omega`
already counts. -/
theorem takeC0_eq_deadC_add : takeC0 = deadC + rowLoadC := by
  refine ACost.toFun_injective (funext fun k => ?_)
  simp only [takeC0, deadC, rowLoadC, ACost.toFun_add]
  omega

/-- **A dead extraction is cheaper than a live one and a pop.** The
program that skips the row load pays two reads, a bump and five state
`skip`s less — and does not pay the row scan's own exit test. -/
theorem deadC_le : iter deadC ≤ A2 + iter (takeC0 + cu Currency.«while») := by
  have h : A2 + iter (takeC0 + cu Currency.«while»)
      = iter deadC + (A2 + rowLoadC + cu Currency.«while») := by
    simp only [iter, takeC0_eq_deadC_add]
    abel
  rw [h]
  exact acost_le_add _ _

/-! ### 2.1 The four inequalities, each true by construction -/

/-- **A pointer bump** comes out of the first term. -/
theorem pot4_bump (m l s c : ℕ) : iter bumpC + pot4 m l s c ≤ pot4 (m + 1) l s c := by
  refine le_of_eq ?_
  show A1 + pot4 m l s c = _
  simp only [pot4, succ_nsmul]
  abel

/-- **A stale pop** comes out of the second. -/
theorem pot4_stale (m l s c : ℕ) : iter staleC + pot4 m l s c ≤ pot4 m (l + 1) s c := by
  refine le_of_eq ?_
  show A2 + pot4 m l s c = _
  simp only [pot4, succ_nsmul]
  abel

/-- The extraction term pays the pointer's drop as well as the
extraction. -/
theorem take_key : iter (takeC0 + cu Currency.«while») + A1 ≤ A4 :=
  le_of_eq (by rw [A4])

/-- **An extraction on a dead vertex** comes out of the fourth term and
the pop the second refunds. -/
theorem pot4_dead (m l s c : ℕ) :
    iter deadC + pot4 (m + 1) l s c ≤ pot4 m (l + 1) s (c + 1) := by
  have key : iter deadC + A1 ≤ A2 + A4 := by
    calc iter deadC + A1
        ≤ (A2 + iter (takeC0 + cu Currency.«while»)) + A1 := add_le_add deadC_le le_rfl
      _ = A2 + A4 := by rw [A4]; abel
  calc iter deadC + pot4 (m + 1) l s c
      = (iter deadC + A1) + pot4 m l s c := by simp only [pot4, succ_nsmul]; abel
    _ ≤ (A2 + A4) + pot4 m l s c := add_le_add key le_rfl
    _ = pot4 m (l + 1) s (c + 1) := by simp only [pot4, succ_nsmul]; abel

/-- **An extraction on a live vertex**, whose row has `L` slots and
whose scan pushes at most `L` of them: the third term releases the
scan, the fourth the extraction, and the second the pop. -/
theorem pot4_take (m l s c L : ℕ) :
    iter (takeC0 + (L • iter decC + cu Currency.«while»)) + pot4 (m + 1) (l + L) s c
      ≤ pot4 m (l + 1) (s + L) (c + 1) := by
  have hC : iter (takeC0 + (L • iter decC + cu Currency.«while»))
      = iter (takeC0 + cu Currency.«while») + L • iter decC := by
    simp only [iter]; abel
  have hsum : pot4 m (l + 1) (s + L) (c + 1)
      = (iter (takeC0 + cu Currency.«while») + L • iter decC + pot4 (m + 1) (l + L) s c)
        + A2 := by
    simp only [pot4, A3, A4, succ_nsmul, add_nsmul, smul_add]
    abel
  rw [hC, hsum]
  exact acost_le_add _ _

end Potential

/-! ## 3. The four turns

Each one preserves `ElimI`, drops the variant, and pays for itself out
of the potential — which is the triple `while_pot_le'` asks for, per
state. -/

section Turns

open Lax13Proofs.Reasoning.Lib (upd upd_self upd_of_ne)

variable {n ns W : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}

/-- **What one turn has to deliver**: the invariant preserved, the
variant dropped, and a price and a continuation bound that pay for it. -/
def TurnGoal (n ns W : ℕ) (G : SimpleGraph (Fin n)) (off tgt alv : List ℕ) (e : ES) : Prop :=
  ∃ C Φ', elimTurnF n off tgt alv e
      ≤ NRest.spec
          (fun t : ES => ElimI n ns W G off tgt alv t ∧
            elimV n ns off alv t < elimV n ns off alv e ∧ elimPot n ns off alv t ≤ Φ')
          (fun _ => liftACost C) ∧
    iter C + Φ' ≤ elimPot n ns off alv e

/-- While there is work left the pointer names a degree of a surviving
vertex, so it is below `n`. -/
theorem elimI_mind_lt {e : ES} (hI : ElimI n ns W G off tgt alv e)
    (hcnt : e.2.2.2.2.2.2.2.2.1 < n) : e.2.2.2.2.2.2.2.2.2.1 < n := by
  obtain ⟨v, hv, hEv⟩ := hI.elim.exists_alive hcnt
  exact hI.elim.mind_lt hv hEv

/-- The head slot of the bucket the pointer names is an allocated
slot. -/
theorem elimI_slot_lt {e : ES} (hI : ElimI n ns W G off tgt alv e) :
    slotOf e < e.2.2.2.2.2.2.2.1 := by
  have h := hI.buck.head_lt e.2.2.2.2.2.2.2.2.2.1 hI.mindLe
  simpa using h

/-- And the arena never runs past the scratch. -/
theorem elimI_sp_le (hin : EIn n ns W G off tgt alv) {e : ES}
    (hI : ElimI n ns W G off tgt alv e) : e.2.2.2.2.2.2.2.1 ≤ n + W + 1 := by
  have h1 := hI.spSc
  have h2 := hin.scOf_le e.2.1
  have h3 := hin.wide
  omega

/-! ### 3.1 The pointer, bumped -/

theorem elimTurn_bump (_hin : EIn n ns W G off tgt alv) {e : ES}
    (hI : ElimI n ns W G off tgt alv e) (hcnt : e.2.2.2.2.2.2.2.2.1 < n)
    (hbh0 : slotOf e = 0) : TurnGoal n ns W G off tgt alv e := by
  have hmind : e.2.2.2.2.2.2.2.2.2.1 < n := elimI_mind_lt hI hcnt
  have hbhlen : e.2.2.2.2.2.2.2.2.2.1 < e.2.2.2.2.1.length := by rw [hI.bhLen]; omega
  have hno : ∀ v < n, larr e.2.1 v = 0 → larr e.1 v ≠ e.2.2.2.2.2.2.2.2.2.1 :=
    fun v hv hE => hI.buck.no_deg (by simpa using hbh0) hv hE
  have hI' : ElimI n ns W G off tgt alv (bumpStep e) := by
    refine ⟨hI.degLen, hI.elmLen, hI.rnkLen, hI.idgLen, hI.bhLen, hI.bvLen, hI.bnLen,
      hI.elim.bump hno, hI.buck, hI.degLt, hI.spSc, hI.lsSp, ?_, hI.kmaxLe⟩
    show e.2.2.2.2.2.2.2.2.2.1 + 1 ≤ n
    omega
  refine ⟨bumpC, elimPot n ns off alv (bumpStep e), ?_, ?_⟩
  · refine le_trans (elimTurnF_bump_le n off tgt alv e hbhlen hbh0)
      (consume_returnT_le_spec ⟨hI', ?_, le_rfl⟩ le_rfl)
    show elimV n ns off alv (bumpStep e) < elimV n ns off alv e
    simp only [elimV, bumpStep]
    omega
  · show iter bumpC + elimPot n ns off alv (bumpStep e) ≤ elimPot n ns off alv e
    simp only [elimPot, bumpStep]
    rw [show n + 1 - e.2.2.2.2.2.2.2.2.2.1 = (n + 1 - (e.2.2.2.2.2.2.2.2.2.1 + 1)) + 1 by omega]
    exact pot4_bump _ _ _ _

/-! ### 3.2 A stale slot, dropped -/

theorem elimTurn_stale (hin : EIn n ns W G off tgt alv) {e : ES}
    (hI : ElimI n ns W G off tgt alv e) (hcnt : e.2.2.2.2.2.2.2.2.1 < n)
    (hbh0 : slotOf e ≠ 0)
    (hstale : ¬ (e.2.1[vtxOf e]! = 0 ∧ e.1[vtxOf e]! = e.2.2.2.2.2.2.2.2.2.1)) :
    TurnGoal n ns W G off tgt alv e := by
  have hmind : e.2.2.2.2.2.2.2.2.2.1 < n := elimI_mind_lt hI hcnt
  have hbhlen : e.2.2.2.2.2.2.2.2.2.1 < e.2.2.2.2.1.length := by rw [hI.bhLen]; omega
  have hsplt : slotOf e < e.2.2.2.2.2.2.2.1 := elimI_slot_lt hI
  have hsple : e.2.2.2.2.2.2.2.1 ≤ n + W + 1 := elimI_sp_le hin hI
  have hbv : slotOf e < e.2.2.2.2.2.1.length := by rw [hI.bvLen]; omega
  have hbn : slotOf e < e.2.2.2.2.2.2.1.length := by rw [hI.bnLen]; omega
  have hwn : vtxOf e < n :=
    hI.buck.val_lt (slotOf e) (Nat.pos_of_ne_zero hbh0) hsplt
  have helm : vtxOf e < e.2.1.length := by rw [hI.elmLen]; exact hwn
  have hdeg : vtxOf e < e.1.length := by rw [hI.degLen]; exact hwn
  have hout : ∀ v < n, larr e.2.1 v = 0 → larr e.1 v = e.2.2.2.2.2.2.2.2.2.1 →
      v ≠ larr e.2.2.2.2.2.1 (larr e.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1) := by
    intro v hv hE hD hc
    exact hstale ⟨by simpa [hc] using hE, by simpa [hc] using hD⟩
  obtain ⟨hlspos, hpop⟩ := hI.buck.pop (d := e.2.2.2.2.2.2.2.2.2.1) hI.mindLe
    (by simpa using hbh0) (larr e.2.1) (fun _ _ h => h) hout
  have hbh' : larr (staleStep e).2.2.2.2.1
      = upd (larr e.2.2.2.2.1) e.2.2.2.2.2.2.2.2.2.1
          (larr e.2.2.2.2.2.2.1 (larr e.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1)) :=
    larr_set hbhlen _
  have hls : lsOf n (staleStep e).2.2.2.2.1 (staleStep e).2.2.2.2.2.2.1
      = lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 - 1 := by
    rw [lsOf, hbh']
    exact hpop.ls_eq.symm
  have hI' : ElimI n ns W G off tgt alv (staleStep e) := by
    refine ⟨hI.degLen, hI.elmLen, hI.rnkLen, hI.idgLen, by simpa [staleStep] using hI.bhLen,
      hI.bvLen, hI.bnLen, hI.elim, ?_, hI.degLt, hI.spSc, ?_, hI.mindLe, hI.kmaxLe⟩
    · show RamElim.Buck n n (larr e.2.1) (larr e.1) (larr (staleStep e).2.2.2.2.1) _ _ _
        (lsOf n (staleStep e).2.2.2.2.1 (staleStep e).2.2.2.2.2.2.1)
      rw [hls, hbh']
      exact hpop
    · show lsOf n (staleStep e).2.2.2.2.1 (staleStep e).2.2.2.2.2.2.1 + 1
        ≤ e.2.2.2.2.2.2.2.1
      rw [hls]
      have := hI.lsSp
      omega
  refine ⟨staleC, elimPot n ns off alv (staleStep e), ?_, ?_⟩
  · refine le_trans (elimTurnF_stale_le n off tgt alv e hbhlen hbh0 hbv hbn helm hdeg
      (fun h => hstale ⟨h.1, h.2⟩)) (consume_returnT_le_spec ⟨hI', ?_, le_rfl⟩ le_rfl)
    show elimV n ns off alv (staleStep e) < elimV n ns off alv e
    simp only [elimV]
    rw [hls]
    have h1 : (staleStep e).2.2.2.2.2.2.2.2.2.1 = e.2.2.2.2.2.2.2.2.2.1 := rfl
    have h2 : (staleStep e).2.1 = e.2.1 := rfl
    have h3 : (staleStep e).2.2.2.2.2.2.2.2.1 = e.2.2.2.2.2.2.2.2.1 := rfl
    rw [h1, h2, h3]
    omega
  · show iter staleC + elimPot n ns off alv (staleStep e) ≤ elimPot n ns off alv e
    simp only [elimPot]
    rw [hls, show (staleStep e).2.2.2.2.2.2.2.2.2.1 = e.2.2.2.2.2.2.2.2.2.1 from rfl,
      show (staleStep e).2.1 = e.2.1 from rfl,
      show (staleStep e).2.2.2.2.2.2.2.2.1 = e.2.2.2.2.2.2.2.2.1 from rfl]
    obtain ⟨l₁, hl₁⟩ : ∃ l₁, lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 = l₁ + 1 :=
      ⟨lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 - 1, by omega⟩
    rw [hl₁, Nat.add_sub_cancel]
    exact pot4_stale _ _ _ _

/-! ### 3.3 The two extractions

Both pop the slot, stamp the vertex and drop the pointer; a live
vertex's row is scanned as well. What the two share is written out
once. -/

/-- **What a popped slot leaves**, in either extraction: the vertex is
a vertex, the arrays are long enough to hold what is written, and the
bucket relation survives the pop with the vertex marked. -/
structure PopOut (n ns W : ℕ) (G : SimpleGraph (Fin n)) (off tgt alv : List ℕ)
    (e : ES) : Prop where
  /-- The pointer is a degree. -/
  mindLt : e.2.2.2.2.2.2.2.2.2.1 < n
  /-- …and names a bucket. -/
  bhIdx : e.2.2.2.2.2.2.2.2.2.1 < e.2.2.2.2.1.length
  /-- The head slot is allocated. -/
  slotLt : slotOf e < e.2.2.2.2.2.2.2.1
  /-- The arena is inside the scratch. -/
  spLe : e.2.2.2.2.2.2.2.1 ≤ n + W + 1
  /-- The slot is inside the arena's two columns. -/
  bvIdx : slotOf e < e.2.2.2.2.2.1.length
  /-- …and the link column. -/
  bnIdx : slotOf e < e.2.2.2.2.2.2.1.length
  /-- Its vertex is a vertex. -/
  wLt : vtxOf e < n
  /-- The buckets, after the pop, with the vertex marked. -/
  buck : RamElim.Buck n n (upd (larr e.2.1) (vtxOf e) 1) (larr e.1)
    (upd (larr e.2.2.2.2.1) e.2.2.2.2.2.2.2.2.2.1
      (larr e.2.2.2.2.2.2.1 (larr e.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1)))
    (larr e.2.2.2.2.2.1) (larr e.2.2.2.2.2.2.1) e.2.2.2.2.2.2.2.1
    (lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 - 1)
  /-- The buckets were not empty, so the pop really removed a slot. -/
  lsPos : 0 < lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1
  /-- And the popped head array reads as the update. -/
  bhSet : lsOf n (e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.1[slotOf e]!)
    e.2.2.2.2.2.2.1 = lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 - 1

theorem elimI_pop (hin : EIn n ns W G off tgt alv) {e : ES}
    (hI : ElimI n ns W G off tgt alv e) (hcnt : e.2.2.2.2.2.2.2.2.1 < n)
    (hbh0 : slotOf e ≠ 0) (_hew : e.2.1[vtxOf e]! = 0) :
    PopOut n ns W G off tgt alv e := by
  have hmind : e.2.2.2.2.2.2.2.2.2.1 < n := elimI_mind_lt hI hcnt
  have hbhlen : e.2.2.2.2.2.2.2.2.2.1 < e.2.2.2.2.1.length := by rw [hI.bhLen]; omega
  have hsplt : slotOf e < e.2.2.2.2.2.2.2.1 := elimI_slot_lt hI
  have hsple : e.2.2.2.2.2.2.2.1 ≤ n + W + 1 := elimI_sp_le hin hI
  have hwn : vtxOf e < n := hI.buck.val_lt (slotOf e) (Nat.pos_of_ne_zero hbh0) hsplt
  have hout : ∀ v < n, upd (larr e.2.1) (vtxOf e) 1 v = 0 →
      larr e.1 v = e.2.2.2.2.2.2.2.2.2.1 →
      v ≠ larr e.2.2.2.2.2.1 (larr e.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1) := by
    intro v hv hE _ hc
    subst hc
    simp at hE
  obtain ⟨hlspos, hpop⟩ := hI.buck.pop (d := e.2.2.2.2.2.2.2.2.2.1) hI.mindLe
    (by simpa using hbh0) (upd (larr e.2.1) (vtxOf e) 1)
    (fun v hv hE => by
      by_cases hvw : v = vtxOf e
      · rw [hvw, upd_self] at hE; omega
      · rwa [upd_of_ne _ hvw] at hE)
    hout
  refine ⟨hmind, hbhlen, hsplt, hsple, by rw [hI.bvLen]; omega, by rw [hI.bnLen]; omega,
    hwn, hpop, hlspos, ?_⟩
  rw [lsOf, larr_set hbhlen]
  exact hpop.ls_eq.symm

/-- **An extraction on a dead vertex.** Its row is never looked at, so
the state moves in one step. -/
theorem elimTurn_dead (hin : EIn n ns W G off tgt alv) {e : ES}
    (hI : ElimI n ns W G off tgt alv e) (hcnt : e.2.2.2.2.2.2.2.2.1 < n)
    (hbh0 : slotOf e ≠ 0) (hew : e.2.1[vtxOf e]! = 0)
    (hdw : e.1[vtxOf e]! = e.2.2.2.2.2.2.2.2.2.1) (haw : ¬ 0 < alv[vtxOf e]!) :
    TurnGoal n ns W G off tgt alv e := by
  obtain ⟨hmind, hbhlen, hsplt, hsple, hbv, hbn, hwn, hpop, hlspos, hbhSet⟩ :=
    elimI_pop hin hI hcnt hbh0 hew
  have helm : vtxOf e < e.2.1.length := by rw [hI.elmLen]; exact hwn
  have hdeg : vtxOf e < e.1.length := by rw [hI.degLen]; exact hwn
  have hrnk : vtxOf e < e.2.2.1.length := by rw [hI.rnkLen]; exact hwn
  have hidg : vtxOf e < e.2.2.2.1.length := by rw [hI.idgLen]; exact hwn
  have halv : vtxOf e < alv.length := by rw [hin.alvLen]; exact hwn
  have hMw : larr alv (vtxOf e) = 0 := by simp only [larr_apply]; omega
  have hEw : larr e.2.1 (vtxOf e) = 0 := by simpa using hew
  have hDw : larr e.1 (vtxOf e) = e.2.2.2.2.2.2.2.2.2.1 := by simpa using hdw
  have hext := hI.elim.extract hcnt hwn hEw hDw
    (fun u _ _ hadj => absurd hMw hadj.alive_right) (fun _ _ _ _ => rfl)
  have hscd : scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1)
      = scOf n (larr off) (larr alv) e.2.1 := by
    rw [scOf, larr_set helm, RamElim.scanned_upd_dead hMw, scOf]
  have hstate : takeState n e (takeScan0 off e)
      = (e.1, e.2.1.set (vtxOf e) 1,
          e.2.2.1.set (vtxOf e) (n - 1 - e.2.2.2.2.2.2.2.2.1),
          e.2.2.2.1.set (vtxOf e) e.2.2.2.2.2.2.2.2.2.1,
          e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.1[slotOf e]!,
          e.2.2.2.2.2.1, e.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.1,
          e.2.2.2.2.2.2.2.2.1 + 1, e.2.2.2.2.2.2.2.2.2.1 - 1,
          e.2.2.2.2.2.2.2.2.2.2 + (e.2.2.2.2.2.2.2.2.2.1 - e.2.2.2.2.2.2.2.2.2.2)) := rfl
  have hkm : e.2.2.2.2.2.2.2.2.2.2 + (e.2.2.2.2.2.2.2.2.2.1 - e.2.2.2.2.2.2.2.2.2.2)
      = max e.2.2.2.2.2.2.2.2.2.2 e.2.2.2.2.2.2.2.2.2.1 := by omega
  have hI' : ElimI n ns W G off tgt alv (takeState n e (takeScan0 off e)) := by
    rw [hstate]
    refine ⟨hI.degLen, by simpa using hI.elmLen, by simpa using hI.rnkLen,
      by simpa using hI.idgLen, by simpa using hI.bhLen, hI.bvLen, hI.bnLen, ?_, ?_,
      hI.degLt, ?_, ?_, ?_, ?_⟩
    · show RamElim.Elim G (larr alv) (larr (e.2.1.set (vtxOf e) 1)) (larr e.1)
        (larr (e.2.2.1.set (vtxOf e) (n - 1 - e.2.2.2.2.2.2.2.2.1)))
        (larr (e.2.2.2.1.set (vtxOf e) e.2.2.2.2.2.2.2.2.2.1)) _ _ _
      rw [larr_set helm, larr_set hrnk, larr_set hidg, hkm]
      exact hext
    · show RamElim.Buck n n (larr (e.2.1.set (vtxOf e) 1)) (larr e.1)
        (larr (e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.1[slotOf e]!)) _ _ _
        (lsOf n (e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.1[slotOf e]!)
          e.2.2.2.2.2.2.1)
      rw [hbhSet, larr_set helm, larr_set hbhlen]
      exact hpop
    · show e.2.2.2.2.2.2.2.1 ≤ n + 1 + scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1)
      rw [hscd]
      exact hI.spSc
    · show lsOf n (e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.1[slotOf e]!)
        e.2.2.2.2.2.2.1 + 1 ≤ e.2.2.2.2.2.2.2.1
      rw [hbhSet]
      have := hI.lsSp
      omega
    · show e.2.2.2.2.2.2.2.2.2.1 - 1 ≤ n
      omega
    · show e.2.2.2.2.2.2.2.2.2.2 + (e.2.2.2.2.2.2.2.2.2.1 - e.2.2.2.2.2.2.2.2.2.2) ≤ n
      have := hI.kmaxLe
      omega
  refine ⟨deadC, elimPot n ns off alv (takeState n e (takeScan0 off e)), ?_, ?_⟩
  · refine le_trans (elimTurnF_takeDead_le n off tgt alv e hbhlen hbv hbn helm hdeg hrnk
      hidg halv hbh0 (by omega) hdw haw) (consume_returnT_le_spec ⟨hI', ?_, le_rfl⟩ le_rfl)
    show elimV n ns off alv (takeState n e (takeScan0 off e)) < elimV n ns off alv e
    rw [hstate]
    show (n + 1 - (e.2.2.2.2.2.2.2.2.2.1 - 1))
        + lsOf n (e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.1[slotOf e]!)
            e.2.2.2.2.2.2.1
        + 3 * (ns - scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1))
        + 3 * (n - (e.2.2.2.2.2.2.2.2.1 + 1)) < _
    rw [hbhSet, hscd]
    show _ < (n + 1 - e.2.2.2.2.2.2.2.2.2.1) + lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1
      + 3 * (ns - scOf n (larr off) (larr alv) e.2.1) + 3 * (n - e.2.2.2.2.2.2.2.2.1)
    omega
  · show iter deadC + elimPot n ns off alv (takeState n e (takeScan0 off e))
      ≤ elimPot n ns off alv e
    rw [hstate]
    show iter deadC + pot4 (n + 1 - (e.2.2.2.2.2.2.2.2.2.1 - 1))
        (lsOf n (e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.1[slotOf e]!)
          e.2.2.2.2.2.2.1)
        (ns - scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1))
        (n - (e.2.2.2.2.2.2.2.2.1 + 1)) ≤ _
    rw [hbhSet, hscd]
    obtain ⟨l₁, hl₁⟩ : ∃ l₁, lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 = l₁ + 1 :=
      ⟨lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 - 1, by omega⟩
    obtain ⟨c₁, hc₁⟩ : ∃ c₁, n - e.2.2.2.2.2.2.2.2.1 = c₁ + 1 :=
      ⟨n - e.2.2.2.2.2.2.2.2.1 - 1, by omega⟩
    show _ ≤ pot4 (n + 1 - e.2.2.2.2.2.2.2.2.2.1) (lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1)
      (ns - scOf n (larr off) (larr alv) e.2.1) (n - e.2.2.2.2.2.2.2.2.1)
    rw [hl₁, hc₁, Nat.add_sub_cancel,
      show n - (e.2.2.2.2.2.2.2.2.1 + 1) = c₁ by omega]
    refine le_trans (add_le_add (le_refl (iter deadC))
      (pot4_mono (show n + 1 - (e.2.2.2.2.2.2.2.2.2.1 - 1)
          ≤ (n + 1 - e.2.2.2.2.2.2.2.2.2.1) + 1 by omega) (le_refl l₁) (le_refl _)
        (le_refl c₁))) ?_
    exact pot4_dead _ _ _ _

/-- **An extraction on a live vertex.** The row is scanned; what the
scan leaves is `RamElim.Elim.extract`'s two hypotheses, through
`RamElim.extract_of_scan`, and what it costs is one `decC` per slot,
which the third term of the potential releases. -/
theorem elimTurn_take (hin : EIn n ns W G off tgt alv) {e : ES}
    (hI : ElimI n ns W G off tgt alv e) (hcnt : e.2.2.2.2.2.2.2.2.1 < n)
    (hbh0 : slotOf e ≠ 0) (hew : e.2.1[vtxOf e]! = 0)
    (hdw : e.1[vtxOf e]! = e.2.2.2.2.2.2.2.2.2.1) (haw : 0 < alv[vtxOf e]!) :
    TurnGoal n ns W G off tgt alv e := by
  obtain ⟨hmind, hbhlen, hsplt, hsple, hbv, hbn, hwn, hpop, hlspos, hbhSet⟩ :=
    elimI_pop hin hI hcnt hbh0 hew
  have helm : vtxOf e < e.2.1.length := by rw [hI.elmLen]; exact hwn
  have hdeg : vtxOf e < e.1.length := by rw [hI.degLen]; exact hwn
  have hrnk : vtxOf e < e.2.2.1.length := by rw [hI.rnkLen]; exact hwn
  have hidg : vtxOf e < e.2.2.2.1.length := by rw [hI.idgLen]; exact hwn
  have halv : vtxOf e < alv.length := by rw [hin.alvLen]; exact hwn
  have hoff : vtxOf e < off.length := by rw [hin.offLen]; omega
  have hoff' : vtxOf e + 1 < off.length := by rw [hin.offLen]; omega
  have hMw : larr alv (vtxOf e) ≠ 0 := by simp only [larr_apply]; omega
  have hEw : larr e.2.1 (vtxOf e) = 0 := by simpa using hew
  have hDw : larr e.1 (vtxOf e) = e.2.2.2.2.2.2.2.2.2.1 := by simpa using hdw
  have hrow : off[vtxOf e]! ≤ off[vtxOf e + 1]! := by
    have h := hin.csr.csr.mono (vtxOf e) hwn
    simpa using h
  -- the row the extraction adds to the scanned ones
  have hnotmem : vtxOf e ∉ RamElim.scanned n (larr e.2.1) (larr alv) := by
    intro hmem
    have h := (RamElim.mem_scanned.1 hmem).2.1
    omega
  have hscanned : scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1)
      = (off[vtxOf e + 1]! - off[vtxOf e]!) + scOf n (larr off) (larr alv) e.2.1 := by
    show ∑ v ∈ RamElim.scanned n (larr (e.2.1.set (vtxOf e) 1)) (larr alv),
      rowLen (larr off) v = _
    rw [larr_set helm, RamElim.scanned_upd_alive hwn hEw hMw, Finset.sum_insert hnotmem]
    try rfl
  have hscle : scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1) ≤ ns := hin.scOf_le _
  -- the scan's invariant, at the top of the row
  have hDecI : DecI n ns W G off tgt alv (e.2.1.set (vtxOf e) 1) (larr e.1) (vtxOf e)
      (scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1))
      (lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 - 1) (takeScan0 off e) := by
    refine ⟨hI.degLen, by simpa [takeScan0] using hI.bhLen, hI.bvLen, hI.bnLen, ?_,
      hI.degLt, ?_, fun _ _ _ => rfl, le_rfl, hrow, ?_, ?_, ?_⟩
    · show RamElim.Buck n n (larr (e.2.1.set (vtxOf e) 1)) (larr e.1)
        (larr (e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.1[slotOf e]!)) _ _ _
        (lsOf n (e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.1[slotOf e]!)
          e.2.2.2.2.2.2.1)
      rw [hbhSet, larr_set helm, larr_set hbhlen]
      exact hpop
    · rintro u hu ⟨-, -, t, h1, h2, -⟩
      simp only [larr_apply, takeScan0] at h1 h2
      omega
    · show e.2.2.2.2.2.2.2.1 + (off[vtxOf e + 1]! - off[vtxOf e]!)
        ≤ n + 1 + scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1)
      have h := hI.spSc
      omega
    · show lsOf n (e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.1[slotOf e]!)
        e.2.2.2.2.2.2.1 ≤ _ + (off[vtxOf e]! - off[vtxOf e]!)
      rw [hbhSet]
      omega
    · show lsOf n (e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.1[slotOf e]!)
        e.2.2.2.2.2.2.1 + 1 ≤ e.2.2.2.2.2.2.2.1
      rw [hbhSet]
      have := hI.lsSp
      omega
  have hscan := decScan_le (elm := e.2.1.set (vtxOf e) 1) (D₀ := larr e.1) (w := vtxOf e)
    (sc₀ := scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1))
    (ls₀ := lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 - 1)
    hin hwn (by simpa using hI.elmLen) hscle
    (off[vtxOf e + 1]! - off[vtxOf e]! + 1) (takeScan0 off e) hDecI
    (by show off[vtxOf e + 1]! - off[vtxOf e]! < _; omega)
  have hnf := elimTurnF_take_eq n off tgt alv e hbhlen hbv hbn helm hdeg hrnk hidg halv
    hoff hoff' hbh0 (by omega) hdw haw
  have hkm : e.2.2.2.2.2.2.2.2.2.2 + (e.2.2.2.2.2.2.2.2.2.1 - e.2.2.2.2.2.2.2.2.2.2)
      = max e.2.2.2.2.2.2.2.2.2.2 e.2.2.2.2.2.2.2.2.2.1 := by omega
  refine ⟨takeC0 + ((off[vtxOf e + 1]! - off[vtxOf e]!) • iter decC + cu Currency.«while»),
    pot4 ((n + 1 - e.2.2.2.2.2.2.2.2.2.1) + 1)
      ((lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 - 1) + (off[vtxOf e + 1]! - off[vtxOf e]!))
      (ns - scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1))
      (n - e.2.2.2.2.2.2.2.2.1 - 1), ?_, ?_⟩
  · have hcost : (fun _ : ES => liftACost (takeC0 + ((off[vtxOf e + 1]! - off[vtxOf e]!)
          • iter decC + cu Currency.«while»)))
        = fun _ : ES => liftACost takeC0
          + liftACost ((off[vtxOf e + 1]! - off[vtxOf e]!) • iter decC
            + cu Currency.«while») := by
      funext _
      rw [liftACost_add]
    rw [hnf, hcost, ← Sepref.consume_spec]
    refine NRest.consume_mono (bindA_ret hscan ?_) le_rfl
    · rintro t ⟨hDt, hjt⟩
      -- the row is scanned to its end, so the degrees are `Elim.extract`'s
      have hhit : ∀ u < n, RamElim.hit (larr off) (larr tgt) (larr alv)
          (upd (larr e.2.1) (vtxOf e) 1) (vtxOf e) (larr off (vtxOf e + 1)) u →
          larr t.1 u = larr e.1 u - 1 := by
        have h := hDt.hitDec
        rw [hjt, larr_set helm] at h
        exact h
      have hnhit : ∀ u < n, ¬ RamElim.hit (larr off) (larr tgt) (larr alv)
          (upd (larr e.2.1) (vtxOf e) 1) (vtxOf e) (larr off (vtxOf e + 1)) u →
          larr t.1 u = larr e.1 u := by
        have h := hDt.hitKeep
        rw [hjt, larr_set helm] at h
        exact h
      obtain ⟨hdecl, hkeepl⟩ := RamElim.extract_of_scan hin.csr hwn hMw hhit hnhit
      have hext := hI.elim.extract hcnt hwn hEw hDw hdecl hkeepl
      have hlsacc : lsOf n t.2.1 t.2.2.2.1
          ≤ (lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 - 1)
            + (off[vtxOf e + 1]! - off[vtxOf e]!) := by
        have h := hDt.lsAcc
        rw [hjt] at h
        exact h
      have hspc : t.2.2.2.2.1
          ≤ n + 1 + scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1) := by
        have h := hDt.spSc
        rw [hjt] at h
        omega
      have hstate : takeState n e t
          = (t.1, e.2.1.set (vtxOf e) 1,
              e.2.2.1.set (vtxOf e) (n - 1 - e.2.2.2.2.2.2.2.2.1),
              e.2.2.2.1.set (vtxOf e) e.2.2.2.2.2.2.2.2.2.1,
              t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1,
              e.2.2.2.2.2.2.2.2.1 + 1, e.2.2.2.2.2.2.2.2.2.1 - 1,
              e.2.2.2.2.2.2.2.2.2.2 + (e.2.2.2.2.2.2.2.2.2.1 - e.2.2.2.2.2.2.2.2.2.2)) := rfl
      have hI' : ElimI n ns W G off tgt alv (takeState n e t) := by
        rw [hstate]
        refine ⟨hDt.degLen, by simpa using hI.elmLen, by simpa using hI.rnkLen,
          by simpa using hI.idgLen, hDt.bhLen, hDt.bvLen, hDt.bnLen, ?_, ?_, hDt.degLt,
          hspc, hDt.lsSp, by show e.2.2.2.2.2.2.2.2.2.1 - 1 ≤ n; omega, ?_⟩
        · show RamElim.Elim G (larr alv) (larr (e.2.1.set (vtxOf e) 1)) (larr t.1)
            (larr (e.2.2.1.set (vtxOf e) (n - 1 - e.2.2.2.2.2.2.2.2.1)))
            (larr (e.2.2.2.1.set (vtxOf e) e.2.2.2.2.2.2.2.2.2.1)) _ _ _
          rw [larr_set helm, larr_set hrnk, larr_set hidg, hkm]
          exact hext
        · exact hDt.buck
        · show e.2.2.2.2.2.2.2.2.2.2 + (e.2.2.2.2.2.2.2.2.2.1 - e.2.2.2.2.2.2.2.2.2.2) ≤ n
          have := hI.kmaxLe
          omega
      refine ⟨hI', ?_, ?_⟩
      · show elimV n ns off alv (takeState n e t) < elimV n ns off alv e
        rw [hstate]
        show (n + 1 - (e.2.2.2.2.2.2.2.2.2.1 - 1)) + lsOf n t.2.1 t.2.2.2.1
            + 3 * (ns - scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1))
            + 3 * (n - (e.2.2.2.2.2.2.2.2.1 + 1))
          < (n + 1 - e.2.2.2.2.2.2.2.2.2.1) + lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1
            + 3 * (ns - scOf n (larr off) (larr alv) e.2.1)
            + 3 * (n - e.2.2.2.2.2.2.2.2.1)
        omega
      · show elimPot n ns off alv (takeState n e t) ≤ _
        rw [hstate]
        show pot4 (n + 1 - (e.2.2.2.2.2.2.2.2.2.1 - 1)) (lsOf n t.2.1 t.2.2.2.1)
            (ns - scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1))
            (n - (e.2.2.2.2.2.2.2.2.1 + 1)) ≤ _
        exact pot4_mono (by omega) hlsacc le_rfl (by omega)
  · obtain ⟨l₁, hl₁⟩ : ∃ l₁, lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 = l₁ + 1 :=
      ⟨lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 - 1, by omega⟩
    obtain ⟨c₁, hc₁⟩ : ∃ c₁, n - e.2.2.2.2.2.2.2.2.1 = c₁ + 1 :=
      ⟨n - e.2.2.2.2.2.2.2.2.1 - 1, by omega⟩
    have hs : ns - scOf n (larr off) (larr alv) e.2.1
        = (ns - scOf n (larr off) (larr alv) (e.2.1.set (vtxOf e) 1))
          + (off[vtxOf e + 1]! - off[vtxOf e]!) := by omega
    show _ ≤ pot4 (n + 1 - e.2.2.2.2.2.2.2.2.2.1) (lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1)
      (ns - scOf n (larr off) (larr alv) e.2.1) (n - e.2.2.2.2.2.2.2.2.1)
    rw [hl₁, hc₁, hs]
    simp only [Nat.add_sub_cancel]
    exact pot4_take _ _ _ _ _

end Turns

/-! ## 4. The loop, run

The four cases are dispatched by the same three tests the program makes,
and `while_pot_le'` pays for the run out of the potential. -/

section Loop

variable {n ns W : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}

/-- **The elimination loop, bounded.** -/
theorem elimLoop_le (hin : EIn n ns W G off tgt alv) :
    ∀ (fuel : ℕ) (e : ES), ElimI n ns W G off tgt alv e →
      elimV n ns off alv e < fuel →
      elimLoop n off tgt alv e
        ≤ NRest.spec (fun t : ES => ElimI n ns W G off tgt alv t ∧ elimBf n t = false)
            (fun _ => liftACost (elimPot n ns off alv e + cu Currency.«while»)) := by
  refine while_pot_le' (P := elimP n off tgt alv) (V := elimV n ns off alv)
    (Φ := elimPot n ns off alv) (fun e hI hb => ?_) (fun e hI hb => ?_)
  · have hcnt : e.2.2.2.2.2.2.2.2.1 < n := by simpa [elimBf] using hb
    show e.2.2.2.2.2.2.2.2.2.1 < e.2.2.2.2.1.length
    rw [hI.bhLen]
    have := elimI_mind_lt hI hcnt
    omega
  · have hcnt : e.2.2.2.2.2.2.2.2.1 < n := by simpa [elimBf] using hb
    by_cases hslot : slotOf e = 0
    · exact elimTurn_bump hin hI hcnt hslot
    · by_cases htake : e.2.1[vtxOf e]! = 0 ∧ e.1[vtxOf e]! = e.2.2.2.2.2.2.2.2.2.1
      · by_cases haw : 0 < alv[vtxOf e]!
        · exact elimTurn_take hin hI hcnt hslot htake.1 htake.2 haw
        · exact elimTurn_dead hin hI hcnt hslot htake.1 htake.2 haw
      · exact elimTurn_stale hin hI hcnt hslot htake

end Loop

/-! ## 5. The exit, read

`RamElim.elimExit_read`'s list-layer twin: at `cnt = n` the certificate,
the extraction degrees and **the rank bound** are three clauses of the
invariant, so nothing has to be re-run to recover them. -/

section Exit

open Lax3Proofs.Augmentation (nbrsIn mem_nbrsIn)
open Lax3Proofs.RamBfs (masked)

variable {n ns W : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}

/-- **What the engine answers**, at the list layer: exactly what
`RamElim.AfterLoop` says of `rnk`, `idg` and `kmax` — the rank bound
`∀ v < n, R v < n` included, which the old `ElimMem` dropped. -/
def ElimAnswer (n ns : ℕ) (G : SimpleGraph (Fin n)) (alv : List ℕ) (e : ES) : Prop :=
  e.2.2.1.length = n ∧ e.2.2.2.1.length = n ∧
    (∀ v < n, e.2.2.1[v]! < n) ∧
    RamElim.ElimCert (masked G (larr alv)) (fun v : Fin n => larr e.2.2.1 (v : ℕ))
      e.2.2.2.2.2.2.2.2.2.2 ∧
    (∀ w : Fin n, larr e.2.2.2.1 (w : ℕ)
      = ((RamElim.ElimCert.elimOr (masked G (larr alv))
          (fun v : Fin n => larr e.2.2.1 (v : ℕ))).inN w).card) ∧
    RamElim.psum (larr e.2.2.2.1) n ≤ ns

theorem elimExit (hin : EIn n ns W G off tgt alv) {e : ES}
    (hI : ElimI n ns W G off tgt alv e) (hbf : elimBf n e = false) :
    ElimAnswer n ns G alv e := by
  have hcntn : e.2.2.2.2.2.2.2.2.1 = n := by
    have h1 : ¬ (e.2.2.2.2.2.2.2.2.1 < n) := by simpa [elimBf] using hbf
    have h2 := hI.elim.cnt_le
    omega
  have helim := hI.elim
  rw [hcntn] at helim
  have hall : ∀ v < n, larr e.2.1 v = 1 := fun v hv => helim.all_elim ⟨v, hv⟩
  have hcert := helim.cert
  -- the recorded extraction degree is the in-degree of the orientation
  have hID : ∀ w : Fin n, larr e.2.2.2.1 (w : ℕ)
      = ((RamElim.ElimCert.elimOr (masked G (larr alv))
          (fun v : Fin n => larr e.2.2.1 (v : ℕ))).inN w).card := by
    intro w
    have h1 := helim.taken w (helim.all_elim w)
    have h2 := helim.survOf_eq_surv w
    have h4 : (RamElim.ElimCert.elimOr (masked G (larr alv))
          (fun v : Fin n => larr e.2.2.1 (v : ℕ))).inN w
        = nbrsIn (masked G (larr alv))
            (RamElim.surv (fun v : Fin n => larr e.2.2.1 (v : ℕ))
              (larr e.2.2.1 (w : ℕ))) w :=
      (RamElim.curNbrs_eq_backNbrs hcert.inj w).symm
    rw [h1, h2, h4]
  -- and it fits inside the row it was counted from
  have hIDrow : ∀ v ∈ Finset.range n, larr e.2.2.2.1 v
      ≤ (if larr e.2.1 v = 1 ∧ larr alv v ≠ 0 then rowLen (larr off) v else 0) := by
    intro v hv
    have hvn : v < n := Finset.mem_range.1 hv
    have h1 := helim.taken ⟨v, hvn⟩ (helim.all_elim ⟨v, hvn⟩)
    have hsub : nbrsIn (masked G (larr alv))
        (RamElim.survOf (n := n) (larr e.2.1) (larr e.2.2.1) (larr e.2.2.1 v + 1))
        (⟨v, hvn⟩ : Fin n) ⊆
        nbrsIn (masked G (larr alv)) Finset.univ (⟨v, hvn⟩ : Fin n) := fun u hu =>
      mem_nbrsIn.2 ⟨Finset.mem_univ _, (mem_nbrsIn.1 hu).2⟩
    have h2 : larr e.2.2.2.1 v ≤ RamElim.adeg G (larr alv) v := by
      rw [h1, RamElim.adeg_eq hvn]
      exact Finset.card_le_card hsub
    by_cases hM : larr alv v = 0
    · rw [RamElim.adeg_of_dead hvn hM] at h2
      simp only [hM, ne_eq, not_true_eq_false, and_false, if_false]
      omega
    · rw [if_pos ⟨hall v hvn, hM⟩]
      refine le_trans h2 ?_
      rw [RamElim.adeg_of_alive hin.csr hvn hM]
      calc (RamElim.liveSlots (larr off) (larr tgt) (larr alv) v).card
          ≤ (Finset.Ico (larr off v) (larr off (v + 1))).card := Finset.card_filter_le _ _
        _ = rowLen (larr off) v := by rw [Nat.card_Ico]; rfl
  have hpsum : RamElim.psum (larr e.2.2.2.1) n ≤ ns := by
    have hle : ∑ v ∈ Finset.range n, larr e.2.2.2.1 v
        ≤ ∑ v ∈ RamElim.scanned n (larr e.2.1) (larr alv), rowLen (larr off) v := by
      rw [RamElim.scanned, Finset.sum_filter]
      exact Finset.sum_le_sum hIDrow
    exact le_trans hle (RamElim.scanned_sum_le hin.csr.csr _)
  exact ⟨hI.rnkLen, hI.idgLen,
    fun v hv => helim.rank_lt v hv (hall v hv), hcert, hID, hpsum⟩

/-- **The elimination loop's budget**: the potential at the state the
bucket build leaves — `mind` and `cnt` at nought, `ls` at `n`, nothing
scanned — plus the loop's last test. -/
def elimBudget (n ns : ℕ) : ACost String ℕ := pot4 (n + 1) n ns n + cu Currency.«while»

/-- **The elimination loop's export.** From the state the bucket build
leaves, the loop delivers `RamElim.AfterLoop`'s answer — the rank bound
included — at the potential's own price. -/
theorem elimLoop_spec (hin : EIn n ns W G off tgt alv)
    {deg elm rnk idg bh bv bn : List ℕ} (hdeg : deg.length = n)
    (hdegA : ∀ v < n, deg[v]! = RamElim.adeg G (larr alv) v)
    (helm : elm.length = n) (helm0 : ∀ v < n, elm[v]! = 0)
    (hrnk : rnk.length = n) (hidg : idg.length = n) (hbh : bh.length = n + 1)
    (hbv : bv.length = n + W + 1) (hbn : bn.length = n + W + 1)
    (hbuck : RamElim.Buck n n (fun _ => 0) (larr deg) (larr bh) (larr bv) (larr bn)
      (n + 1) n) :
    elimLoop n off tgt alv (deg, elm, rnk, idg, bh, bv, bn, n + 1, 0, 0, 0)
      ≤ NRest.spec (ElimAnswer n ns G alv) (fun _ => liftACost (elimBudget n ns)) := by
  have hls : lsOf n bh bn = n := hbuck.ls_eq.symm
  have hsc0 : scOf n (larr off) (larr alv) elm = 0 := by
    have hempty : RamElim.scanned n (larr elm) (larr alv) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
      have h := RamElim.mem_scanned.1 hv
      have h0 := helm0 v h.1
      have h1 := h.2.1
      simp only [larr_apply] at h1
      omega
    show ∑ v ∈ RamElim.scanned n (larr elm) (larr alv), rowLen (larr off) v = 0
    rw [hempty, Finset.sum_empty]
  have hdegLt : ∀ u < n, deg[u]! < n := by
    intro u hu
    rw [hdegA u hu, RamElim.adeg_eq hu]
    exact RamElim.card_nbrsIn_lt _ _
  have hI0 : ElimI n ns W G off tgt alv (deg, elm, rnk, idg, bh, bv, bn, n + 1, 0, 0, 0) := by
    refine ⟨hdeg, helm, hrnk, hidg, hbh, hbv, hbn, ?_, ?_, hdegLt, ?_, ?_,
      Nat.zero_le n, Nat.zero_le n⟩
    · exact RamElim.Elim.init (fun v hv => by simpa using helm0 v hv)
        (fun v => by
          show deg[(v : ℕ)]! = _
          rw [hdegA (v : ℕ) v.isLt, RamElim.adeg_eq v.isLt])
    · show RamElim.Buck n n (larr elm) (larr deg) (larr bh) (larr bv) (larr bn) (n + 1)
        (lsOf n bh bn)
      rw [hls]
      exact hbuck.weaken _
    · show n + 1 ≤ n + 1 + scOf n (larr off) (larr alv) elm
      omega
    · show lsOf n bh bn + 1 ≤ n + 1
      rw [hls]
  refine le_trans (elimLoop_le hin
    (elimV n ns off alv (deg, elm, rnk, idg, bh, bv, bn, n + 1, 0, 0, 0) + 1) _ hI0
    (Nat.lt_succ_self _)) (spec_mono ?_ ?_)
  · rintro t ⟨hIt, hbf⟩
    exact elimExit hin hIt hbf
  · intro _ _
    show liftACost (elimPot n ns off alv (deg, elm, rnk, idg, bh, bv, bn, n + 1, 0, 0, 0)
      + cu Currency.«while») ≤ liftACost (elimBudget n ns)
    refine le_of_eq (congrArg liftACost ?_)
    show pot4 (n + 1 - 0) (lsOf n bh bn) (ns - scOf n (larr off) (larr alv) elm) (n - 0)
      + cu Currency.«while» = elimBudget n ns
    rw [hls, hsc0, elimBudget]
    norm_num

end Exit

/-! ## 6. The engine's cost, cashed -/

section Cash

theorem cash_A1 : Codegen.cash A1 = 25 := cash_bumpC

theorem cash_A2 : Codegen.cash A2 = 44 := cash_staleC

theorem cash_A3 : Codegen.cash A3 = 104 := by
  rw [A3, Codegen.cash_add, cash_decC, cash_A2]

theorem cash_A4 : Codegen.cash A4 = 132 := by
  rw [A4, Codegen.cash_add, cash_takeC, cash_A1]

/-- **The elimination loop's cost**: `201·n + 104·ns + 29` IMP+ time
units, against the hand-walked baseline's `160·n + 100·ns + 52`
(`RamElim.elimLoop_spec`). -/
def elimK (n ns : ℕ) : ℕ := 201 * n + 104 * ns + 29

theorem cash_elimBudget (n ns : ℕ) : Codegen.cash (elimBudget n ns) = elimK n ns := by
  rw [elimBudget, pot4, Codegen.cash_add, Codegen.cash_add, Codegen.cash_add,
    Codegen.cash_add, BfsQSynth.cash_nsmul, BfsQSynth.cash_nsmul, BfsQSynth.cash_nsmul,
    BfsQSynth.cash_nsmul, cash_A1, cash_A2, cash_A3, cash_A4,
    show Codegen.cash (cu Currency.«while») = 4 from by decide +kernel, elimK]
  ring

-- the two figures side by side at the demo's size: the tower's
-- extraction term is the dearer one (`132` against `80`), its bump the
-- cheaper (`25` against `40`).
#guard elimK 5 10 = 2074
#guard 160 * 5 + 100 * 10 + 52 = 1852

end Cash

/-! ## 7. The whole engine, composed

The four passes the elimination is, in the program's order, against the
input surface `RamElim.Implements` has: a block structure `CsrSimple`,
a mask, and scratch at its lengths. What comes out is
`RamElim.AfterLoop`'s answer together with the block structure of the
in-lists that `AfterOff` adds. -/

section Engine

open Lax13Proofs.Reasoning (arrOf length_arrOf)

variable {n ns W : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}

/-- **The block structure, read at the list layer.** The engine's own
input predicate holds of the arrays the driver hands it. -/
theorem eIn_arrOf (hcsr : RamElim.CsrSimple G ns O T) (hW : ns ≤ W) :
    EIn n ns W G (arrOf (n + 1) O) (arrOf ns T) (arrOf n M) := by
  have hO : ∀ i ≤ n, larr (arrOf (n + 1) O) i = O i := fun i hi =>
    getElem!_arrOf O (by omega)
  have hT : ∀ j < ns, larr (arrOf ns T) j = T j := fun j hj => getElem!_arrOf T hj
  have hrow : ∀ u : Fin n, larr (arrOf (n + 1) O) ((u : ℕ) + 1) ≤ ns := fun u => by
    rw [hO _ u.isLt]; exact hcsr.csr.le_ns u.isLt
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, hW, by simp [arrOf], by simp [arrOf], by simp [arrOf]⟩
  · rw [hO 0 (Nat.zero_le n)]; exact hcsr.csr.zero
  · rw [hO n le_rfl]; exact hcsr.csr.last
  · intro i hi
    rw [hO i (by omega), hO (i + 1) (by omega)]
    exact hcsr.csr.mono i hi
  · intro j hj
    rw [hT j hj]
    exact hcsr.csr.target_lt j hj
  · intro u v
    have hub : ∀ j, j < O ((u : ℕ) + 1) → j < ns := fun j hj =>
      lt_of_lt_of_le hj (hcsr.csr.le_ns u.isLt)
    rw [hcsr.csr.adj_iff u v, hO (u : ℕ) (le_of_lt u.isLt), hO ((u : ℕ) + 1) u.isLt]
    constructor
    · rintro ⟨j, hj1, hj2, hj3⟩
      exact ⟨j, hj1, hj2, by rw [hT j (hub j hj2)]; exact hj3⟩
    · rintro ⟨j, hj1, hj2, hj3⟩
      refine ⟨j, hj1, hj2, ?_⟩
      rw [hT j (hub j hj2)] at hj3
      exact hj3
  · intro u hu j₁ j₂ h1 h2 h3 h4 h5
    rw [hO u (le_of_lt hu)] at h1 h3
    rw [hO (u + 1) hu] at h2 h4
    have hns : O (u + 1) ≤ ns := hcsr.csr.le_ns hu
    rw [hT j₁ (by omega), hT j₂ (by omega)] at h5
    exact hcsr.nodup u hu j₁ j₂ h1 h2 h3 h4 h5

/-- **The mask, read at the list layer, is the mask.** The arena only
ever looks at a vertex's own cell, so truncating the mask to `n` cells
leaves the graph alone. -/
theorem masked_arrOf : Lax3Proofs.RamBfs.masked G (larr (arrOf n M))
    = Lax3Proofs.RamBfs.masked G M := by
  ext u v
  rw [Lax3Proofs.RamBfs.masked_adj, Lax3Proofs.RamBfs.masked_adj, larr_apply, larr_apply,
    getElem!_arrOf M u.isLt, getElem!_arrOf M v.isLt]

/-- …and so is every arena degree. -/
theorem adeg_arrOf {v : ℕ} : RamElim.adeg G M v = RamElim.adeg G (larr (arrOf n M)) v := by
  by_cases hv : v < n
  · rw [RamElim.adeg_eq hv, RamElim.adeg_eq hv, masked_arrOf]
  · rw [RamElim.adeg, RamElim.adeg, dif_neg hv, dif_neg hv]

/-- **The elimination engine, abstractly**: the degrees, the buckets,
the elimination and the offsets, in the program's order. -/
noncomputable def elimEngine (n : ℕ) (off tgt alv : List ℕ)
    (deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ : List ℕ) : NRest (ES × OS) ECost :=
  bindT (degPass n off tgt alv (deg₀, 0)) fun d =>
    bindT (buckPass n d.1 (bh₀, bv₀, bn₀, 1, 0)) fun b =>
      bindT (elimLoop n off tgt alv
          (d.1, elm₀, rnk₀, idg₀, b.1, b.2.1, b.2.2.1, n + 1, 0, 0, 0)) fun e =>
        bindT (offPass n e.2.2.2.1 (ioff₀, ifl₀, 0, 0)) fun o => NRest.returnT (e, o)

/-- **What the engine leaves**: `RamElim.AfterLoop`'s answer, with the
in-list blocks `AfterOff` opens on top. -/
def EngineOut (n ns : ℕ) (G : SimpleGraph (Fin n)) (alv : List ℕ) (p : ES × OS) : Prop :=
  ElimAnswer n ns G alv p.1 ∧ p.2.1.length = n + 1 ∧ p.2.2.1.length = n ∧
    (∀ j ≤ n, p.2.1[j]! = RamElim.psum (larr p.1.2.2.2.1) j) ∧
    (∀ j < n, p.2.2.1[j]! = RamElim.psum (larr p.1.2.2.2.1) j)

/-- The engine's price: the four passes' own. -/
noncomputable def engineC (n ns : ℕ) : ACost String ℕ :=
  (E2 (iter degRowC) (iter degC) n ns + cu Currency.«while»)
    + ((n • iter buckC + cu Currency.«while»)
      + (elimBudget n ns + (n • iter offC + cu Currency.«while»)))

/-- **THE WHOLE-ENGINE EXPORT.** Against `RamElim.Implements`'s input
surface — a block structure, a mask and scratch at its lengths — the
four passes deliver `RamElim.AfterLoop`'s answer, **the rank bound
`∀ v < n, R v < n` included**, and the in-list offsets `AfterOff` adds,
at the sum of the four passes' derived prices. -/
theorem elimEngine_le (hcsr : RamElim.CsrSimple G ns O T) (hW : ns ≤ W)
    {deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ : List ℕ}
    (hdeg : deg₀.length = n) (helm : elm₀.length = n) (helm0 : ∀ v < n, elm₀[v]! = 0)
    (hrnk : rnk₀.length = n) (hidg : idg₀.length = n)
    (hbh : bh₀.length = n + 1) (hbh0 : ∀ j ≤ n, bh₀[j]! = 0)
    (hbv : bv₀.length = n + W + 1) (hbn : bn₀.length = n + W + 1)
    (hio : ioff₀.length = n + 1) (hio0 : ioff₀[0]! = 0) (hifl : ifl₀.length = n) :
    elimEngine n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M)
        deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀
      ≤ NRest.spec (EngineOut n ns G (arrOf n M)) (fun _ => liftACost (engineC n ns)) := by
  have hin : EIn n ns W G (arrOf (n + 1) O) (arrOf ns T) (arrOf n M) := eIn_arrOf hcsr hW
  rw [elimEngine, engineC]
  refine seqA_le (degPass_adeg hcsr deg₀ hdeg) fun d hd => ?_
  have hdlt : ∀ v < n, d.1[v]! < n := by
    intro v hv
    rw [hd.2 v hv, RamElim.adeg_eq hv]
    exact RamElim.card_nbrsIn_lt _ _
  refine seqA_le (buckPass_spec (W := W) hd.1 hdlt hbh hbh0 hbv hbn) fun b hb => ?_
  refine seqA_le (elimLoop_spec hin hd.1
    (fun v hv => by rw [hd.2 v hv, adeg_arrOf]) helm helm0 hrnk hidg hb.1 hb.2.1 hb.2.2.1
    hb.2.2.2.2.2) fun e he => ?_
  exact bindA_ret (offPass_spec he.2.1 hio hio0 hifl) fun o ho =>
    ⟨he, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2⟩

/-- **The engine's cost**: `296·n + 127·ns + 41` IMP+ time units,
against the hand-walked baseline's `261·n + 144·ns + 84` for the same
four phases (`RamElim.implements`'s `w1`–`w4`). The tower is cheaper on
the block-structure coefficient and the constant, dearer on the vertex
one: the elimination's `132` per extraction against the baseline's `80`
is where it goes. -/
def engineK (n ns : ℕ) : ℕ := 296 * n + 127 * ns + 41

theorem cash_engineBudget (n ns : ℕ) : Codegen.cash (engineC n ns) = engineK n ns := by
  rw [engineC,
    Codegen.cash_add (E2 (iter degRowC) (iter degC) n ns + cu Currency.«while»),
    Codegen.cash_add (n • iter buckC + cu Currency.«while»),
    Codegen.cash_add (elimBudget n ns),
    cash_degBudget n ns, cash_buckBudget n, cash_elimBudget n ns, cash_offBudget n,
    degK, buckK, offK, elimK, engineK]
  ring

-- the two figures side by side at the demo's size
#guard engineK 5 10 = 2791
#guard 261 * 5 + 144 * 10 + 84 = 2829
#guard engineK 5 10 < 261 * 5 + 144 * 10 + 84

/-! ### 7.1 Negative controls on the export

The export is a `≤`, so what falsifies it is a *cheaper* claim. Three
of them, at the cash layer the four coefficients are computed in. -/

-- **(a) the elimination loop's price is not the baseline's.** An export
-- that re-used `RamElim.elimLoop_spec`'s hand-walked `160 n + 100 ns +
-- 52` would be false at the demo's size: the tower charges the
-- state-as-resource `skip`s and the extraction term is the dearer one.
#guard ¬ (elimK 5 10 ≤ 160 * 5 + 100 * 10 + 52)

-- **(b) the third term really carries the pop its push will need.**
-- With `A₃ = iter decC` alone, a two-slot row that pushes both slots
-- outruns what the term releases.
#guard ¬ (60 * 2 + 44 * 2 ≤ 44 + 60 * 2)

-- **(c) …and a scan may push at most one slot per slot passed.**
-- `DecI.lsAcc` is what bounds it; a scan that pushed twice per slot
-- would outrun the second term.
#guard ¬ (44 * (2 + 2) ≤ 44 + 44 * 2)

end Engine

/-! ## 8. What is landed, and what is left (2B‴)

**Debt E2 — paid.** `ElimI` survives all four turns
(`elimTurn_bump`, `elimTurn_stale`, `elimTurn_dead`, `elimTurn_take`),
and `elimExit` reads the answer off it at `cnt = n`. `RamElim.Elim`'s
`bump`, `extract`, `cert`, `init` and `rank_lt`, `Buck`'s `push`,
`pop`, `no_deg`, `weaken` and `ls_eq`, `extract_of_scan`,
`scanned_upd_alive`/`_dead` and `scanned_sum_le` are all *consumed*:
nothing about the mathematics of the engine is re-proved here.

**Debt E1 — paid.** The four prices are paid out of
`elimPot = A₁·(n+1−mind) + A₂·ls + A₃·(ns−sc) + A₄·(n−cnt)` with
`A₁ = iter bumpC`, `A₂ = iter staleC`, `A₃ = iter decC + A₂` and
`A₄ = iter (takeC0 + «while») + A₁` — cashed at `25`, `44`, `104`,
`132`. The loop's budget is the potential at the state the bucket build
leaves: `201 n + 104 ns + 29`, against the hand-walked `160 n + 100 ns +
52`. **2B″'s predicted `157 n + …` dropped the `A₂·ls` term**, and `ls`
starts at `n`: the honest coefficient is `25 + 44 + 132 = 201`.

**The variant.** `cnt` alone does not decrease — a bump and a stale pop
leave it standing — so `elimV` is the potential's own shape at the
smallest integer coefficients that make all four turns drop it
(`1, 1, 3, 3`).

**The export — landed.** `elimEngine_le`: four passes, `AfterLoop`'s
answer with the rank bound, at `296 n + 127 ns + 41` against the
baseline's `261 n + 144 ns + 84` for the same four phases.

**Debt F1 — still open**, and it is the fifth phase: the fill pass's
`InCsr` walk (`ElimSynth2` §4.3). Until it lands the engine's export
stops at the offsets, which is why `elimEngine` returns the loop's state
and the offset pass's rather than an in-list block structure.

**One conversion the caller may need.** `ElimAnswer` speaks of
`masked G (larr alv)`; the driver speaks of `masked G M`. `masked_arrOf`
is the bridge, and `adeg_arrOf` is its degree-level twin. -/

/-! ## 9. Axioms -/

/-- info: 'Lax3Proofs.Refine.ElimSynth5.elimEngine_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms elimEngine_le

/-- info: 'Lax3Proofs.Refine.ElimSynth5.elimLoop_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms elimLoop_spec

/-- info: 'Lax3Proofs.Refine.ElimSynth5.elimExit' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms elimExit

/-- info: 'Lax3Proofs.Refine.ElimSynth5.elimLoop_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms elimLoop_le

end Lax3Proofs.Refine.ElimSynth5
