import Lax3Proofs.Refine.ArenaWidth

/-!
**The cover pass re-walked at the arena width** — ND-MC rebase, wave
E-mem, leaf W1.

`Refine.ArenaWidth` compiled the mathematics and left one obligation
named: `CoverImplementsK`, the cover pass's turn walk with the carrier
value bound `n * n + ns + 2 * r + 2 < B` replaced by `WordBoundK`'s
arena clause `n * d + n + ns + 2 * r + 2 < B` and the ordering's
weak-reachability degree bound added. This file discharges it, and runs
the whole pass at the new bound.

**What actually moved, and what did not.** The pass forms exactly one
value off the arena — the write pointer `xp` — and writes into exactly
one array — `xmem`, of length `n * n`. Those are two obligations, not
one, and the repair separates them:

* the **value** ceiling `xp + n < B` used to be read off `xp ≤ c * n`
  (`RamCover.CoverInv.ptr_le`) against `n * n < B`. It is now
  `Refine.ArenaWidth.block_scan_lt`, reading `xp ≤ n * d`
  (`CoverInv.ptr_le_mass`) against `WordBoundK` — §1.
* the **allocation** ceiling `xp + n ≤ n * n` is untouched, and is still
  derived inside `RamDriverOrder.centreStep_specWB` from `ptr_le` alone.
  The `n × n` arena stays exactly where it is; `Refine.ArenaWidth` §1 is
  the reason that costs the word length nothing. `xmem_length` below is
  the compiled check that it did not move.

**Where the walk lives.** It is not repeated here. `RamDriverOrder`'s
`emitSlot_spec`/`emitLoop_spec` now take the value ceiling `hbB` and the
allocation ceiling `hxp₀` as two hypotheses instead of deriving both
from `n * n < B`, and `centreStep_specWB` takes the pointer ceiling as
the predicate `RamDriverOrder.PtrWords`. The landed exports
(`centreStep_specW`, `RamCover.cover_specW`) are those same walks at
`ptrWords_of_square`, unchanged in statement; this file supplies
`ptrWords_of_mass` instead. One walk, two readings.

**Scope.** This is a *space* repair and not a cost repair: the pass
still charges `RamCover.coverCost n ns = 100 * n * n + …`, because the
emission scan still walks the carrier once per centre. The B7/G2 cost
floor is untouched and is not this leaf's business.
-/

namespace Lax3Proofs.Refine.CoverWidth

open Lax12.ColoringNumbers (wreach)
open Lax3Proofs.RamBfs (masked CsrGraph)
open Lax3Proofs.RamCover (CoverInv CoverState CoverStateW CoverPre CoverPreW CoverPost
  OrdersBy)
open Lax3Proofs.Refine.ArenaWidth (WordBoundK block_scan_lt)
open Lax13Proofs.Imp Lax13Proofs.Reasoning

variable {n ns : ℕ} {G : SimpleGraph (Fin n)} {A₀ O T ord : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)} {r d : ℕ}

/-! ## 1. The arena reading of the pointer ceiling

`RamDriverOrder.PtrWords` is the one value bound the turn takes off the
arena. `RamDriverOrder.ptrWords_of_square` is its carrier reading, the
landed one. This is its arena reading, and it is `block_scan_lt`
verbatim: the invariant's own clauses give `xp ≤ n * d`, and
`WordBoundK`'s arena clause turns that into a word.

The `mb` slot of `WordBoundK` plays no part — the cover pass forms no
padded width — so it is taken at `0`, whose clause `0 < B` the arena
clause already implies. -/

/-- **The arena reading**: the pointer ceiling from the mass bound
rather than from the carrier. -/
theorem ptrWords_of_mass {B : ℕ} (hord : OrdersBy n π ord)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hB : n * d + n + ns + 2 * r + 2 < B) :
    RamDriverOrder.PtrWords B G A₀ π ord r := by
  intro c xp Xoff Xmem asg M hI _
  exact block_scan_lt (ns := ns) (cap := r) (mb := 0) hord hI hk ⟨hB, by omega⟩

/-- The same, entered at the driver's own slot rather than at its arena
clause: `WordBoundK` at the search's radius. -/
theorem ptrWords_of_wordBoundK {B mb : ℕ} (hord : OrdersBy n π ord)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hB : WordBoundK B n d ns r mb) : RamDriverOrder.PtrWords B G A₀ π ord r :=
  ptrWords_of_mass (ns := ns) hord hk hB.1

/-! ### The exit pointer: the *second* arena slot

W2 threaded `WordBoundK` through the driver and found that the cover
phase forms two values out of the arena, not one. The first is the
emission scan's running pointer, above. The second is the pointer the
pass *reports* — `RamDriver.CoverHeldAt`'s `m` — which
`RamDriverDescend.clusterLoad_spec` and the readback both form, and
every block offset is below. It is `RamDriver.MassWords`; its carrier
reading is `RamDriver.massWords_of_square`, and this is its arena
reading. Same double count, read at exit rather than at a centre
boundary, and block-injectivity read off the pass's own answer rather
than carried as a slot. -/

/-- **The arena reading of the exit ceiling.** -/
theorem massWords_of_mass {B ns mb : ℕ} (hord : OrdersBy n π ord)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hB : WordBoundK B n d ns r mb) : RamDriver.MassWords B G A₀ π ord r := fun hout _ =>
  lt_of_le_of_lt
    (MassMath.mass_le hord hout (MassMath.blockInj_of_coverOut hout) hk)
    (by have := hB.arena; omega)

/-! ## 2. One centre, at the arena width

`RamDriverOrder.centreStep_specWB` is the walk; the four readings it
takes off the value bound are `n < B`, `ns < B`, `2 * r + 1 < B` and
the pointer ceiling. Only the last is about the arena. -/

/-- **One centre at the arena width, at a widened target array.** The
same walk as `RamDriverOrder.centreStep_specW`, with the value bound read
at the ordering's degree. -/
theorem centreStep_specKW {B nt : ℕ} (hcsr : CsrGraph G ns O T) (hord : OrdersBy n π ord)
    (hB : n * d + n + ns + 2 * r + 2 < B)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hnt : ns ≤ nt) (hpad : 0 < n → ∀ j, ns ≤ j → j < nt → T j < n) :
    Spec B (fun σ => CoverStateW B G A₀ π ns nt O T ord r σ ∧ σ.vars "c" < n)
      (RamCover.centreStep r)
      (fun σ σ' => CoverStateW B G A₀ π ns nt O T ord r σ' ∧ σ'.vars "c" = σ.vars "c" + 1)
      (RamCover.centreCost n ns) :=
  RamDriverOrder.centreStep_specWB hcsr hord (by omega) (by omega) (by omega)
    (ptrWords_of_mass (ns := ns) hord hk hB) hnt hpad

/-- **One centre at the arena width, at the pinned target array.** -/
theorem centreStep_specK {B : ℕ} (hcsr : CsrGraph G ns O T) (hord : OrdersBy n π ord)
    (hB : n * d + n + ns + 2 * r + 2 < B)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d) :
    Spec B (fun σ => CoverState B G A₀ π ns O T ord r σ ∧ σ.vars "c" < n)
      (RamCover.centreStep r)
      (fun σ σ' => CoverState B G A₀ π ns O T ord r σ' ∧ σ'.vars "c" = σ.vars "c" + 1)
      (RamCover.centreCost n ns) :=
  centreStep_specKW (nt := ns) hcsr hord hB hk le_rfl (fun _ _ h₁ h₂ => absurd h₁ (by omega))

/-! ## 3. `Refine.ArenaWidth.CoverImplementsK`, discharged

The obligation `ArenaWidth` §6 named, with no clause left over. It was
never a `sorry`; it is now not open either. -/

/-- **The named obligation of `Refine.ArenaWidth` §6, discharged.** -/
theorem coverTurnImplementsK (B n ns d : ℕ) (G : SimpleGraph (Fin n)) (A₀ O T ord : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (r : ℕ) :
    ArenaWidth.CoverImplementsK B n ns d G A₀ O T ord π r :=
  fun hcsr hord hB hk _ => centreStep_specK hcsr hord hB hk

/-- **The widened form of the same obligation**, which is what a level
whose target array is allocated at the ordering phase's width consumes
(rebase F-c-3's shape at the new bound). -/
def CoverImplementsKW (B n ns nt d : ℕ) (G : SimpleGraph (Fin n)) (A₀ O T ord : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (r : ℕ) : Prop :=
  CsrGraph G ns O T → OrdersBy n π ord →
    n * d + n + ns + 2 * r + 2 < B →
    (∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d) →
    (∀ z < n, A₀ z < B) → ns ≤ nt → (0 < n → ∀ j, ns ≤ j → j < nt → T j < n) →
    Spec B (fun σ => CoverStateW B G A₀ π ns nt O T ord r σ ∧ σ.vars "c" < n)
      (RamCover.centreStep r)
      (fun σ σ' => CoverStateW B G A₀ π ns nt O T ord r σ' ∧ σ'.vars "c" = σ.vars "c" + 1)
      (RamCover.centreCost n ns)

theorem coverTurnImplementsKW (B n ns nt d : ℕ) (G : SimpleGraph (Fin n))
    (A₀ O T ord : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (r : ℕ) :
    CoverImplementsKW B n ns nt d G A₀ O T ord π r :=
  fun hcsr hord hB hk _ hnt hpad => centreStep_specKW hcsr hord hB hk hnt hpad

/-- The pinned obligation is the widened one at `nt = ns`, clause for
clause — the same relation `RamCover.implements_of_implementsW` records
at the landed bound. -/
theorem coverImplementsK_of_KW {B n ns d : ℕ} {G : SimpleGraph (Fin n)}
    {A₀ O T ord : ℕ → ℕ} {π : Equiv.Perm (Fin n)} {r : ℕ}
    (h : CoverImplementsKW B n ns ns d G A₀ O T ord π r) :
    ArenaWidth.CoverImplementsK B n ns d G A₀ O T ord π r :=
  fun hcsr hord hB hk hA =>
    h hcsr hord hB hk hA le_rfl (fun _ _ h₁ h₂ => absurd h₁ (by omega))

/-! ## 4. The whole pass, at the arena width

`RamCover.cover_specOfW` is the assembly with the turn as a parameter:
the fill that clears the assignments, the two commands that open the
arena, and the loop over the centres. It reads exactly `n < B` off the
value bound and nothing else, so it runs unchanged at either reading. -/

/-- **The cover pass of Grohe–Kreutzer–Siebertz §6 at the arena width,
widened target array.** Same program, same cost, same `CoverPost`. -/
theorem coverPass_specKW {B nt : ℕ} (hcsr : CsrGraph G ns O T) (hord : OrdersBy n π ord)
    (hB : n * d + n + ns + 2 * r + 2 < B)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hA : ∀ z < n, A₀ z < B) (hnt : ns ≤ nt)
    (hpad : 0 < n → ∀ j, ns ≤ j → j < nt → T j < n) :
    Spec B (fun σ => CoverPreW n ns nt O T A₀ ord σ ∧ (∀ v ∈ σ.arrs "dist", v < B) ∧
        (∀ v ∈ σ.arrs "q", v < B))
      (RamCover.coverCom r) (CoverPost G A₀ π ord r) (RamCover.coverCost n ns) :=
  RamCover.cover_specOfW hord (by omega) hA (centreStep_specKW hcsr hord hB hk hnt hpad)

/-- **The same at the pinned target array.** -/
theorem coverPass_specK {B : ℕ} (hcsr : CsrGraph G ns O T) (hord : OrdersBy n π ord)
    (hB : n * d + n + ns + 2 * r + 2 < B)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hA : ∀ z < n, A₀ z < B) :
    Spec B (fun σ => CoverPre n ns O T A₀ ord σ ∧ (∀ v ∈ σ.arrs "dist", v < B) ∧
        (∀ v ∈ σ.arrs "q", v < B))
      (RamCover.coverCom r) (CoverPost G A₀ π ord r) (RamCover.coverCost n ns) :=
  coverPass_specKW (nt := ns) hcsr hord hB hk hA le_rfl
    (fun _ _ h₁ h₂ => absurd h₁ (by omega))

/-- **The pass entered at the driver's slot.** `WordBoundK` at the
search's radius is the shape W3 will restate the root theorem's `hB` in;
this is the cover phase already reading it. -/
theorem coverPass_specKW_of_wordBoundK {B nt mb : ℕ} (hcsr : CsrGraph G ns O T)
    (hord : OrdersBy n π ord) (hB : WordBoundK B n d ns r mb)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hA : ∀ z < n, A₀ z < B) (hnt : ns ≤ nt)
    (hpad : 0 < n → ∀ j, ns ≤ j → j < nt → T j < n) :
    Spec B (fun σ => CoverPreW n ns nt O T A₀ ord σ ∧ (∀ v ∈ σ.arrs "dist", v < B) ∧
        (∀ v ∈ σ.arrs "q", v < B))
      (RamCover.coverCom r) (CoverPost G A₀ π ord r) (RamCover.coverCost n ns) :=
  coverPass_specKW hcsr hord hB.1 hk hA hnt hpad

/-! ## 5. The allocation did not move

The whole repair rests on the value/space distinction. If the `n × n`
arena had quietly shrunk, `Refine.ArenaWidth` §1 would be beside the
point and the flip of finding 3 would be a different claim. It did not:
the state the re-walked pass runs against still allocates the full
carrier square, and the allocation ceiling `xp + n ≤ n * n` is still
derived inside the walk from `CoverInv.ptr_le` alone. -/

/-- **The arena is still `n × n` cells.** -/
theorem xmem_length {B : ℕ} {σ : Env} (h : CoverState B G A₀ π ns O T ord r σ) :
    (σ.arrs "xmem").length = n * n := by
  obtain ⟨-, Xmem, -, -, -, -, -, -, -, -, -, -, -, hxmem, -, -, -, -⟩ := h
  rw [hxmem, length_arrOf]

/-- And so is the arena the widened pass runs against. -/
theorem xmem_lengthW {B nt : ℕ} {σ : Env} (h : CoverStateW B G A₀ π ns nt O T ord r σ) :
    (σ.arrs "xmem").length = n * n := by
  obtain ⟨-, Xmem, -, -, -, -, -, -, -, -, -, -, -, hxmem, -, -, -, -⟩ := h
  rw [hxmem, length_arrOf]

/-! ## 6. The controls, and they bite

Four refutations. Each is the statement some step of the repair would
need if the step were free, and each is false. -/

/-- **Control 1 — the new slot really is a weaker demand on `B`.** The
arena clause does not imply the carrier clause, so the repair buys
something rather than renaming it. The witness is
`Refine.ArenaWidth`'s own realistic profile: `n = 200`, degree `8`,
radius `2`, `B = 1844`. -/
theorem square_not_of_arena :
    ¬ ∀ B n d ns r : ℕ, n * d + n + ns + 2 * r + 2 < B → n * n + ns + 2 * r + 2 < B := by
  intro h
  have := h 1844 200 8 0 2 (by norm_num)
  omega

/-- **Control 2 — and it is not a disguised strengthening either.** The
carrier clause does not imply the arena clause at `d = n`, because of
the `+ n` the block scan needs, so the two slots are genuinely
incomparable and the degree hypothesis is doing real work rather than
being carried for show. -/
theorem arena_not_of_square :
    ¬ ∀ B n d ns r : ℕ, d ≤ n → n * n + ns + 2 * r + 2 < B →
      n * d + n + ns + 2 * r + 2 < B := by
  intro h
  have := h 103 10 10 0 0 le_rfl (by norm_num)
  omega

/-- **Control 3 — the value ceiling is not free.** `n < B` and the
*allocation* clause `xp₀ + n ≤ n * n` together do not give the emission
scan's word clause `xp₀ + n < B`. So `emitSlot_spec`'s `hbB` is a
genuine hypothesis and not bookkeeping, and the two ceilings really are
two. -/
theorem ptrWords_not_free : ¬ ∀ B n xp₀ : ℕ, n < B → xp₀ + n ≤ n * n → xp₀ + n < B := by
  intro h
  exact absurd (h 4 3 6 (by omega) (by omega)) (by omega)

/-- **Control 4 — the mass bound is not free either.** The invariant's
own ceiling `CoverInv.ptr_le : xp ≤ c * n` cannot deliver `xp ≤ n * d`
below the carrier: at `n = 10`, `d = 3`, the last centre's `xp` may be
`90` as far as `ptr_le` knows, and `n * d = 30`. So `ptr_le_mass` — and
with it the degree hypothesis `hk` — is what the re-walk stands on. -/
theorem mass_not_free : ¬ ∀ n d c xp : ℕ, d < n → c < n → xp ≤ c * n → xp ≤ n * d := by
  intro h
  have := h 10 3 9 90 (by omega) (by omega) (by omega)
  omega

/-- **Control 5 — the exit ceiling is a second slot, not the first one
again.** `WordBoundK` together with the *allocation* clause `m ≤ n * n`
does not make the reported pointer a word: at `n = 10` and degree `0`
the value bound is met by `B = 13`, and the arena holds `100` cells. So
`RamDriver.MassWords` is a genuine hypothesis of the cover phase, and
the `m < B` clause W2 added to `RamDriver.CoverHeldAt` is not implied by
the `m ≤ n * n` clause beside it. -/
theorem exitWords_not_free :
    ¬ ∀ B n K ns cap mb m : ℕ,
      RamDriver.WordBoundK B n K ns cap mb → m ≤ n * n → m < B := by
  intro h
  have := h 13 10 0 0 0 0 100 ⟨by norm_num, by norm_num⟩ (by norm_num)
  omega

/-! ### The controls, flipped

Each control is a refutation of a *general* statement; the point of the
repair is that the corresponding *instance* is nevertheless available
once the degree bound is in hand. These are the four positive readings,
so that no control is refuting something the file also needs. -/

-- the arena clause is satisfiable exactly where the carrier clause is not
#guard 200 * 8 + 200 + 0 + 2 * 2 + 2 < 1844
#guard ¬ (200 * 200 + 0 + 2 * 2 + 2 < 1844)
-- the value ceiling *is* available from the mass bound: `xp ≤ n * d` and
-- the arena clause give `xp + n < B` at the same profile
#guard 200 * 8 + 200 < 1844
-- control 5's witness: the value bound holds and the arena does not fit
#guard 10 * 0 + 10 + 0 + 2 * 0 + 2 < 13
#guard ¬ (10 * 10 < 13)
-- and the exit ceiling *is* available at the same profile once the mass
-- bound replaces the allocation clause: `m ≤ n * d` against the arena clause
#guard 200 * 8 < 1844

/-! ## 7. The axiom check -/

#print axioms ptrWords_of_mass
#print axioms massWords_of_mass
#print axioms exitWords_not_free
#print axioms centreStep_specKW
#print axioms coverTurnImplementsK
#print axioms coverTurnImplementsKW
#print axioms coverPass_specKW
#print axioms coverPass_specKW_of_wordBoundK
#print axioms xmem_length
#print axioms square_not_of_arena
#print axioms arena_not_of_square
#print axioms ptrWords_not_free
#print axioms mass_not_free

end Lax3Proofs.Refine.CoverWidth
