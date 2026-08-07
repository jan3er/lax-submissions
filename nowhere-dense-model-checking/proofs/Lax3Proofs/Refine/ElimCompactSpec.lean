import Lax3Proofs.Refine.ElimCompactCsr

/-!
# ND-MC E2-fold — the compacted elimination engine, composed

`Refine/ElimCompact.lean` §8 assembles the compacted engine on two named
obligation `Prop`s and names them as hypotheses; this file is the
assembly at **real discharges**, which is the corollary the E2-sat ledger
recorded as missing and refused to manufacture by weakening.

The two obligations are `ElimCompact.CompactInstalls` — the compaction
pass builds a `CsrSimple` block structure of the member pullback and
installs the engine's entry, discharged in `Refine/ElimCompactCsr.lean` —
and `ElimCompact.ScatterBacksW` — the scatter sends the compact ranks to
the members' arena cells, discharged in `Refine/ElimCompactWalks.lean`
§2. Neither is assumed anywhere below: `elimCompact_run` has no
hypothesis that is not about the arena, the word length, or the store the
driver hands down.

§2 reads the composite's clock in the two weights the G2 interface
budgets in. The charge the compaction actually pays is the members' raw
row-length sum (`ElimCompact.memRowSum`) — the compaction crosses the
level rows and pays for the dead targets it drops — and
`ElimCompactWalks.wsum_csrW_markSet` says that `mm + memRowSum` *is* the
level arena's own `csrW`-weight. So the clock is `900 · w + 400` at a
weight of the arena, with the carrier nowhere in it, which is the whole
claim of the wave.

Nothing here is `sorry` and nothing here is new mathematics.
-/

namespace Lax3Proofs.Refine.ElimCompactSpec

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamDriverCluster (markSet)
open Lax3Proofs.Refine.ScatterBlock (MemList)
open Lax3Proofs.RamElim (CsrSimple)
open Lax3Proofs.Refine.MassWeight (wsum csrW)
open Lax3Proofs.Refine.ElimCompact (ArenaEntryC ElimMemPost elimCompactCore elimCompactCost
  memRowSum)

/-! ## §1 The composite, on real discharges -/

/-- **The compacted elimination engine, end to end.** Handed the arena as
the driver hands it down — the level CSR, the mask, the member list at
the carrier's physical length, and the engine's scratch arrays at theirs
— `elimCompactCore` runs, in a clock in which **the carrier does not
occur**, and leaves `ElimMemPost`: the elimination's whole contract read
at the arena's live vertices, in the compacted numbering, with the ranks
scattered back to the members' arena cells.

The hypotheses are the arena's (`MemList`, `CsrSimple`), the word
length's (`mm + nt + 1 < B`, `n < B`, `∀ v < n, M v < B`) and the store's
(`ArenaEntryC`).
No obligation `Prop` appears: `ElimCompact.elimCompact_spec`'s two are
supplied by `ElimCompactCsr.compactInstalls` and
`ElimCompactWalks.scatterBacksW`. -/
theorem elimCompact_run {B n mm nt W : ℕ} {G : SimpleGraph (Fin n)} {O T M Mem : ℕ → ℕ}
    {σ : Env} (hml : MemList n mm Mem (markSet n M)) (hcsr : CsrSimple G nt O T)
    (hB : mm + nt + 1 < B) (hnB : n < B) (hMB : ∀ v, v < n → M v < B) (hW : nt ≤ W)
    (hent : ArenaEntryC n mm nt W O T M Mem σ) :
    ∃ (σ'' : Env) (cs : ℕ), cs ≤ nt ∧ cs ≤ memRowSum mm O Mem ∧
      Run B elimCompactCore σ σ'' (elimCompactCost mm (memRowSum mm O Mem)) ∧
      ElimMemPost G M Mem hml cs W σ'' :=
  Lax3Proofs.Refine.ElimCompact.elimCompact_spec hml hcsr
    ElimCompactCsr.compactInstalls ElimCompactWalks.scatterBacksW hB hnB hMB hW hent

/-! ## §2 The clock, in the arena's own weight

Two readings, and the point of both is that the carrier is absent. -/

/-- **The composite's budget is the level arena's machine weight.**
`ElimCompactWalks.wsum_csrW_markSet` identifies `mm + memRowSum mm O Mem`
with `wsum (csrW n O) (markSet n M)` — the `csrW` reading of the arena,
one plus the row length at each live vertex — and the cost is affine in
it. This is the honest charge: the compaction crosses the members' *raw*
rows, and this weight is what those rows cost. -/
theorem elimCompactCost_le_csrW {n mm : ℕ} {M Mem O : ℕ → ℕ}
    (hml : MemList n mm Mem (markSet n M)) :
    elimCompactCost mm (memRowSum mm O Mem)
      ≤ 900 * wsum (csrW n O) (markSet n M) + 400 :=
  Lax3Proofs.Refine.ElimCompact.elimCompactCost_le_weight
    (le_of_eq (ElimCompactWalks.wsum_csrW_markSet (O := O) hml).symm)

/-- **The composite, budgeted in the arena's weight.** `elimCompact_run`
with its clock read through §2's identity: one number, a weight of the
*level* arena, and no carrier term anywhere in the statement. -/
theorem elimCompact_run_weight {B n mm nt W : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Mem : ℕ → ℕ} {σ : Env} (hml : MemList n mm Mem (markSet n M))
    (hcsr : CsrSimple G nt O T) (hB : mm + nt + 1 < B) (hnB : n < B)
    (hMB : ∀ v, v < n → M v < B) (hW : nt ≤ W)
    (hent : ArenaEntryC n mm nt W O T M Mem σ) :
    ∃ (σ'' : Env) (cs K : ℕ), cs ≤ nt ∧
      Run B elimCompactCore σ σ'' K ∧
      K ≤ 900 * wsum (csrW n O) (markSet n M) + 400 ∧
      ElimMemPost G M Mem hml cs W σ'' := by
  obtain ⟨σ'', cs, hcs, -, hrun, hpost⟩ := elimCompact_run hml hcsr hB hnB hMB hW hent
  exact ⟨σ'', cs, _, hcs, hrun, elimCompactCost_le_csrW hml, hpost⟩

/-! ## §3 Axioms -/

#print axioms elimCompact_run
#print axioms elimCompact_run_weight

end Lax3Proofs.Refine.ElimCompactSpec
