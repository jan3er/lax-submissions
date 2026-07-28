import Lax3Proofs.RamElim

/-!
One round of transitive–fraternal augmentation as a word-RAM program:
the round the driver composes `r` times to build an augmentation chain.

Handed the current orientation `D` in the in-neighbour block form
`RamElim.InCsr` leaves behind, the round enumerates the pairs the round
owes an arc to, materializes the fraternity graph, hands *that* to the
elimination engine, and writes the next orientation back out in the
same block form, so that the driver's next round reads what this one
wrote.

### What the round computes

* **The out-lists of `D`.** A counting sort of the in-lists. Every
  later pass needs them: the fraternal partners of `v` are the
  in-neighbours of the vertices `v` points at, and so are the vertices
  `v` reaches transitively.
* **The fraternity graph**, in compressed-row form and *deduplicated*.
  A pair can carry several witnesses `w`, so the raw enumeration emits
  duplicates; the engine's input surface is `RamElim.CsrSimple`, which
  demands a row name each neighbour once, because a degree count is
  what the engine reads a row for. The dedup is a per-vertex stamp
  array: the block of `v` is walked once setting a stamp and counting
  the vertices whose stamp was clear, and walked again clearing it, so
  the whole build is linear rather than a sort.
* **The elimination**, `RamElim.elimCom` on the fraternity graph with
  an all-alive mask. It returns the ranking `ρ` in `rnk`, the greedy
  degeneracy bound in `kmax`, and — this is what makes the call worth
  more than the ranking — the fraternity graph already *oriented* by
  `ρ` in `ioff`/`itg`, which is one of the three lists the assembly
  concatenates.
* **The next in-lists**, assembled per vertex from three enumerations
  under one arc rule, deduplicated by the same stamp trick.

### The arc rule, and why it is what it is

The round must produce an `Augmentation.Orientation`: no loops and *no
two-cycles*. That is the whole difficulty of the assembly, because the
three sources conflict. An old arc `u → v` can also be a fraternal
pair — a triangle `u → v`, `u → w`, `v → w` is one — and a pair can be
transitively linked in both directions at once. Orienting each source
by its own rule would put two arcs on such a pair.

`AugStep.tight` fixes half of the answer: an arc `u → v` of the round
must be justified by `TransLink D u v` in that direction, or by
`FratLink D u v`, which is symmetric. So a transitive link may only
ever produce its forward arc, unless the pair is also fraternal or
transitively linked backwards. What is left is a *priority*, and the
one that works is a single rule with no cases,

    NewArc D ρ u v  :=  ¬ D.Adjacent u v ∧ Demand D u v ∧
                          (Demand D v u → ρ u < ρ v)

where `Demand D u v` is `TransLink D u v ∨ FratLink D u v`. The first
conjunct keeps the round off pairs `D` already carries, so an old arc
never meets a new one. The third is the tie-break: a pair demanded in
*both* directions — every fraternal pair, and a transitive pair linked
backwards too — is oriented by the ranking, and a pair demanded in one
direction only takes that direction unconditionally. Two-cycles are
impossible because the two directions would give `ρ u < ρ v` and
`ρ v < ρ u`, and loops because `Demand D v v` gives `ρ v < ρ v`. So
`augOr D ρ` is an orientation for *any* injective `ρ`, with no
hypothesis on `D` at all, and `augStep_augOr` proves all four clauses
of `AugStep` from injectivity alone.

### The enumerations, as identities

Four lemmas carry everything the program's scans and stamps do, each a
set the arc rule speaks in on the left and a union of blocks a nested
scan walks on the right. `mem_adjSet` is the stamp `sta` — the in-block
and the out-block of `v`. `mem_demandOut` is the stamp `std`, and it is
the one that makes the tie-break a table lookup: `Demand D v u` is `u`
lying in an in-block or an out-block of something `v` points at, the
first union being the fraternal half and the second the
backwards-transitive one. `fratNbrs_eq` is the fraternity build.
`inN_augOr_eq` is the assembly itself: the block it writes — the old
in-list, the transitive candidates that pass the rule, and the engine's
own in-block minus the pairs `D` already carries — is exactly
`(augOr D ρ).inN v`, and `card_inN_augOr` is what its counting pass
adds up, the two halves disjoint because the rule never touches a pair
`D` already carries.

### What the round owes, and what it cannot pay

`RamElim.greedyFratRound_of_cert` turns the engine's certificate into
`Augmentation.GreedyFratRound`, the clause the in-degree recursion is
run against, and asks the caller for one thing: that every arc of the
new orientation lying on a fraternity edge points the way `ρ` does.
`hor_augOr` discharges that for every arc the round *adds*, since a
fraternal pair is demanded both ways and so is oriented by `ρ`. It
cannot discharge it for the arcs the round *inherits*: an old arc
`u → v` on a fraternity edge is kept by `AugStep.mono`, and nothing
makes the engine's ranking of the fraternity graph agree with it. On
three vertices with `D.inN 0 = {1}`, `D.inN 1 = ∅`, `D.inN 2 = {0,1}` —
the arcs `1 → 0`, `1 → 2`, `0 → 2` — the fraternity graph is the single
edge `{0,1}`, forced by the block of `2`; the engine peels `2, 1, 0`
and ranks `ρ 0 = 0 < ρ 1 = 1`, while `D` carries `1 → 0`.

So the residual is isolated, named and *exposed in the
postcondition*, as an implication rather than a hypothesis:
`FratForward D ρ` — every arc of `D` that is a fraternity edge is
`ρ`-increasing — implies `GreedyFratRound D (augOr D ρ)`, and the
round's specification carries that implication rather than its
conclusion. The clause is not an artefact of this program: it is what
`Augmentation.GreedyFratRound` asks of *every* arc of `D'` on a
fraternity edge, where the in-degree union bound of
`inDegLE_of_augStep` only ever needs it of the arcs that are neither
old nor transitive. Narrowing the two definitions to the new arcs is a
one-line change on the mathematics side and would discharge the
implication's hypothesis outright; it is not made here, since this file
changes no other.

### What is proved

The assembly mathematics, unconditionally: `augOr` is an orientation,
`augStep_augOr` is `AugStep` in all four clauses, the four enumeration
identities are the passes, `hor_augOr` and `greedyFratRound_augOr` are
the bridge to the greedy recursion, and `inDegLE_augOr` is the round's
in-degree budget. `fratSlots_le` is the width: the fraternity graph of
an orientation of in-degree at most `d` has at most `n · d²` slots — by
`sum_card_outSet`, since the out-degrees add up to the arcs — so the
scratch arrays are sized in `n · (d+1)²` and the cost with them.

`augCom` is exhibited and run — the worked example builds a four-vertex
orientation, takes one round and checks the block structure it
produces against the hand computation. What is isolated is the Hoare
triple of the program text, `Implements`, exactly as `RamElim` isolates
its own: it splits along the round's ten passes, and it carries the
engine's `RamElim.Implements` as a hypothesis of its own — `ElimAvail`
— so that discharging that one discharges this one's sub-call without
moving any signature here.
-/

namespace Lax3Proofs.RamAugment

open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.RamElim (CsrSimple InCsr ElimCert ElimPre ElimMem elimCost elimCom)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n : ℕ}

/-! ### The pairs a round owes an arc to

`Demand D u v` is the round's obligation on the ordered pair, and it is
`AugStep.tight`'s disjunction on the nose: an arc `u → v` of the new
orientation may exist only if `D` had it, or the pair is demanded in
that direction. Fraternity is symmetric, so a fraternal pair is
demanded both ways; a transitive link need not be. -/

/-- The round owes the ordered pair `u, v` an arc: `u` reaches `v`
transitively, or the two are fraternal. -/
def Demand (D : Orientation n) (u v : Fin n) : Prop := TransLink D u v ∨ FratLink D u v

theorem demand_of_fratLink {D : Orientation n} {u v : Fin n} (h : FratLink D u v) :
    Demand D u v := Or.inr h

theorem demand_symm_of_fratLink {D : Orientation n} {u v : Fin n} (h : FratLink D u v) :
    Demand D v u := Or.inr h.symm

/-- A vertex is never demanded of itself: a transitive self-link is a
two-cycle of `D`, and a fraternal one forces `ρ v < ρ v` through the
arc rule below. -/
theorem not_transLink_self (D : Orientation n) (v : Fin n) : ¬ TransLink D v v := by
  rintro ⟨w, hvw, hwv⟩
  exact D.asymm v w hvw hwv

/-! ### The three sets a vertex's turn stamps

Everything the assembly asks about the current vertex `v` is one of
three sets, and each is the union of blocks the program already holds:
the vertices `D` makes `v` adjacent to, the vertices `v` demands an arc
*to*, and the fraternal partners of `v`. The lemmas here are the
identities the stamping walks realize — a set on the left that the arc
rule speaks in, a union of in- and out-blocks on the right that a
nested scan enumerates. -/

/-- The vertices `v` points at: the out-block of `v`. -/
def outSet (D : Orientation n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => v ∈ D.inN w)

theorem mem_outSet {D : Orientation n} {v w : Fin n} : w ∈ outSet D v ↔ v ∈ D.inN w := by
  rw [outSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The vertices `D` already makes `v` adjacent to: the in-block and
the out-block, which is what the stamp `sta` holds. -/
def adjSet (D : Orientation n) (v : Fin n) : Finset (Fin n) := D.inN v ∪ outSet D v

theorem mem_adjSet {D : Orientation n} {u v : Fin n} :
    u ∈ adjSet D v ↔ D.Adjacent u v := by
  rw [adjSet, Finset.mem_union, mem_outSet]
  exact Iff.rfl

/-- The vertices `v` demands an arc to: the in-blocks and the
out-blocks of the vertices `v` points at, which is what the stamp `std`
holds. The first union is the fraternal half of the demand and the
second the backwards-transitive one. -/
def demandOut (D : Orientation n) (v : Fin n) : Finset (Fin n) :=
  (outSet D v).biUnion (fun w => D.inN w) ∪ (outSet D v).biUnion (fun w => outSet D w)

theorem mem_demandOut {D : Orientation n} {u v : Fin n} :
    u ∈ demandOut D v ↔ Demand D v u := by
  rw [demandOut, Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
  constructor
  · rintro (⟨w, hw, hu⟩ | ⟨w, hw, hu⟩)
    · exact Or.inr ⟨w, mem_outSet.1 hw, hu⟩
    · exact Or.inl ⟨w, mem_outSet.1 hw, mem_outSet.1 hu⟩
  · rintro (⟨w, hvw, hwu⟩ | ⟨w, hvw, huw⟩)
    · exact Or.inr ⟨w, mem_outSet.2 hvw, mem_outSet.2 hwu⟩
    · exact Or.inl ⟨w, mem_outSet.2 hvw, huw⟩

/-- The fraternal partners of a vertex. -/
noncomputable def fratNbrs (D : Orientation n) (v : Fin n) : Finset (Fin n) :=
  pick (fun u => (fratGraph D).Adj u v)

theorem mem_fratNbrs {D : Orientation n} {u v : Fin n} :
    u ∈ fratNbrs D v ↔ (fratGraph D).Adj u v := mem_pick

/-- **The fraternity enumeration.** The partners of `v` are the
in-neighbours of the vertices `v` points at, `v` itself removed — which
is the nested scan the fraternity build runs, with `v`'s own stamp set
first standing for the erasure. -/
theorem fratNbrs_eq (D : Orientation n) (v : Fin n) :
    fratNbrs D v = ((outSet D v).biUnion (fun w => D.inN w)).erase v := by
  ext u
  rw [mem_fratNbrs, Finset.mem_erase, Finset.mem_biUnion]
  constructor
  · rintro ⟨hne, w, huw, hvw⟩
    exact ⟨hne, w, mem_outSet.2 hvw, huw⟩
  · rintro ⟨hne, w, hw, hu⟩
    exact ⟨hne, w, hu, mem_outSet.1 hw⟩

/-- **The arc rule.** A pair `D` does not already carry takes the arc
it is demanded in; a pair demanded both ways takes the one the ranking
points. -/
def NewArc (D : Orientation n) (ρ : Fin n → ℕ) (u v : Fin n) : Prop :=
  ¬ D.Adjacent u v ∧ Demand D u v ∧ (Demand D v u → ρ u < ρ v)

/-- **The round's orientation**: the old arcs and the new ones. -/
noncomputable def augOr (D : Orientation n) (ρ : Fin n → ℕ) : Orientation n where
  inN v := D.inN v ∪ pick (fun u => NewArc D ρ u v)
  not_mem_self v h := by
    rcases Finset.mem_union.1 h with h | h
    · exact D.not_mem_self v h
    · obtain ⟨-, hd, hlt⟩ := mem_pick.1 h
      exact absurd (hlt hd) (lt_irrefl _)
  asymm u v h h' := by
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_union.1 h' with h' | h'
      · exact D.asymm u v h h'
      · exact (mem_pick.1 h').1 (Or.inr h)
    · rcases Finset.mem_union.1 h' with h' | h'
      · exact (mem_pick.1 h).1 (Or.inr h')
      · obtain ⟨-, hd, hlt⟩ := mem_pick.1 h
        obtain ⟨-, hd', hlt'⟩ := mem_pick.1 h'
        exact absurd ((hlt hd').trans (hlt' hd)) (lt_irrefl _)

theorem mem_augOr {D : Orientation n} {ρ : Fin n → ℕ} {u v : Fin n} :
    u ∈ (augOr D ρ).inN v ↔ u ∈ D.inN v ∨ NewArc D ρ u v := by
  rw [show (augOr D ρ).inN v = D.inN v ∪ pick (fun u => NewArc D ρ u v) from rfl,
    Finset.mem_union]
  exact or_congr Iff.rfl mem_pick

/-- **One round is an augmentation step**, for any injective ranking
and with no hypothesis on `D`. Injectivity enters only where a pair
demanded both ways has to be given a direction. -/
theorem augStep_augOr (D : Orientation n) {ρ : Fin n → ℕ} (hinj : Function.Injective ρ) :
    AugStep D (augOr D ρ) where
  mono _ _ h := mem_augOr.2 (Or.inl h)
  trans_cov u v hne hlink := by
    by_cases hadj : D.Adjacent u v
    · rcases hadj with hadj | hadj
      · exact Or.inl (mem_augOr.2 (Or.inl hadj))
      · exact Or.inr (mem_augOr.2 (Or.inl hadj))
    · have hd : Demand D u v := Or.inl hlink
      by_cases hd' : Demand D v u
      · rcases lt_trichotomy (ρ u) (ρ v) with hlt | heq | hgt
        · exact Or.inl (mem_augOr.2 (Or.inr ⟨hadj, hd, fun _ => hlt⟩))
        · exact absurd (hinj heq) hne
        · exact Or.inr (mem_augOr.2 (Or.inr
            ⟨fun hc => hadj (adjacent_comm hc), hd', fun _ => hgt⟩))
      · exact Or.inl (mem_augOr.2 (Or.inr ⟨hadj, hd, fun hc => absurd hc hd'⟩))
  frat_cov u v hne hlink := by
    by_cases hadj : D.Adjacent u v
    · rcases hadj with hadj | hadj
      · exact Or.inl (mem_augOr.2 (Or.inl hadj))
      · exact Or.inr (mem_augOr.2 (Or.inl hadj))
    · rcases lt_trichotomy (ρ u) (ρ v) with hlt | heq | hgt
      · exact Or.inl (mem_augOr.2 (Or.inr ⟨hadj, Or.inr hlink, fun _ => hlt⟩))
      · exact absurd (hinj heq) hne
      · exact Or.inr (mem_augOr.2 (Or.inr
          ⟨fun hc => hadj (adjacent_comm hc), Or.inr hlink.symm, fun _ => hgt⟩))
  tight u v h := by
    rcases mem_augOr.1 h with h | ⟨-, hd, -⟩
    · exact Or.inl h
    · exact Or.inr hd

/-! ### The three enumerations, as one identity

The assembly pass walks three lists into the block of `v`: the old
in-list, the transitive candidates — the in-neighbours of the
in-neighbours — under the arc rule, and the engine's own in-block,
which is the fraternity graph oriented by `ρ`, under the one clause of
the rule the engine cannot know about. `inN_augOr_eq` says their union
is the block. -/

/-- The transitive candidates the assembly keeps. -/
noncomputable def transCand (D : Orientation n) (ρ : Fin n → ℕ) (v : Fin n) :
    Finset (Fin n) := pick (fun u => TransLink D u v ∧ NewArc D ρ u v)

theorem mem_transCand {D : Orientation n} {ρ : Fin n → ℕ} {u v : Fin n} :
    u ∈ transCand D ρ v ↔ TransLink D u v ∧ NewArc D ρ u v := mem_pick

/-- The fraternal candidates the assembly keeps: the engine's in-block
of `v`, minus the pairs `D` already carries. -/
noncomputable def fratCand (D : Orientation n) (ρ : Fin n → ℕ) (v : Fin n) :
    Finset (Fin n) :=
  pick (fun u => u ∈ (RamElim.ElimCert.elimOr (fratGraph D) ρ).inN v ∧ ¬ D.Adjacent u v)

theorem mem_fratCand {D : Orientation n} {ρ : Fin n → ℕ} {u v : Fin n} :
    u ∈ fratCand D ρ v ↔
      ((fratGraph D).Adj u v ∧ ρ u < ρ v) ∧ ¬ D.Adjacent u v := by
  rw [fratCand, mem_pick]
  exact and_congr RamElim.ElimCert.mem_elimOr Iff.rfl

/-- **The assembly identity.** The block the round writes for `v` is
the old in-list together with the two filtered candidate lists — which
is what the program enumerates, and nothing else. -/
theorem inN_augOr_eq (D : Orientation n) (ρ : Fin n → ℕ) (v : Fin n) :
    (augOr D ρ).inN v = D.inN v ∪ transCand D ρ v ∪ fratCand D ρ v := by
  ext u
  rw [mem_augOr, Finset.mem_union, Finset.mem_union, mem_transCand, mem_fratCand]
  constructor
  · rintro (hold | hnew)
    · exact Or.inl (Or.inl hold)
    · obtain ⟨hadj, hd, himp⟩ := hnew
      rcases hd with htr | hfr
      · exact Or.inl (Or.inr ⟨htr, hadj, Or.inl htr, himp⟩)
      · have hlt : ρ u < ρ v := himp (demand_symm_of_fratLink hfr)
        have hne : u ≠ v := by rintro rfl; exact absurd hlt (lt_irrefl _)
        exact Or.inr ⟨⟨⟨hne, hfr⟩, hlt⟩, hadj⟩
  · rintro ((hold | ⟨-, hnew⟩) | ⟨⟨hadj', hlt⟩, hadj⟩)
    · exact Or.inl hold
    · exact Or.inr hnew
    · exact Or.inr ⟨hadj, Or.inr hadj'.2, fun _ => hlt⟩

/-- The old arcs and the candidates are disjoint: the arc rule never
touches a pair `D` already carries. This is why the counting pass adds
the in-degree of `D` to the number of candidates that passed, and why
the duplicate stamp is needed only among the candidates. -/
theorem disjoint_old_cand (D : Orientation n) (ρ : Fin n → ℕ) (v : Fin n) :
    Disjoint (D.inN v) (transCand D ρ v ∪ fratCand D ρ v) := by
  rw [Finset.disjoint_left]
  intro u hu hcand
  rcases Finset.mem_union.1 hcand with h | h
  · exact (mem_transCand.1 h).2.1 (Or.inl hu)
  · exact (mem_fratCand.1 h).2 (Or.inl hu)

/-- **What the counting pass counts**: the block length of `v` is its
old in-degree plus the number of candidates that passed the rule, the
duplicates among them removed once. -/
theorem card_inN_augOr (D : Orientation n) (ρ : Fin n → ℕ) (v : Fin n) :
    ((augOr D ρ).inN v).card
      = (D.inN v).card + (transCand D ρ v ∪ fratCand D ρ v).card := by
  rw [inN_augOr_eq, Finset.union_assoc,
    Finset.card_union_of_disjoint (disjoint_old_cand D ρ v)]

/-! ### The greedy round, and the clause the round inherits -/

/-- The compatibility the round cannot compute: every arc of `D` that
is a fraternity edge already points the way the fraternity ranking
does. -/
def FratForward (D : Orientation n) (ρ : Fin n → ℕ) : Prop :=
  ∀ u v : Fin n, u ∈ D.inN v → (fratGraph D).Adj u v → ρ u < ρ v

/-- **Every arc the round adds on a fraternity edge is
`ρ`-increasing**, since a fraternal pair is demanded both ways and the
arc rule then reads the ranking. What is left is the arcs the round
inherited. -/
theorem hor_augOr {D : Orientation n} {ρ : Fin n → ℕ} (h : FratForward D ρ) :
    ∀ u v : Fin n, u ∈ (augOr D ρ).inN v → (fratGraph D).Adj u v → ρ u < ρ v := by
  intro u v hu hadj
  rcases mem_augOr.1 hu with hu | ⟨-, -, himp⟩
  · exact h u v hu hadj
  · exact himp (demand_symm_of_fratLink hadj.2)

/-- **The greedy round.** The engine's certificate on the fraternity
graph, plus the inherited compatibility, is
`Augmentation.GreedyFratRound`. -/
theorem greedyFratRound_augOr {D : Orientation n} {ρ : Fin n → ℕ} {k : ℕ}
    (hcert : ElimCert (fratGraph D) ρ k) (h : FratForward D ρ) :
    GreedyFratRound D (augOr D ρ) :=
  RamElim.greedyFratRound_of_cert hcert (hor_augOr h)

/-- **The round's in-degree budget**: the old in-degree, the `d²`
transitive links, and a fraternity graph the engine oriented as well as
its degeneracy allows. -/
theorem inDegLE_augOr {D : Orientation n} {ρ : Fin n → ℕ} {k d k' : ℕ}
    (hcert : ElimCert (fratGraph D) ρ k) (h : FratForward D ρ) (hd : D.InDegLE d)
    (hk : LowDegreeVertices (fratGraph D) k') :
    (augOr D ρ).InDegLE (d + d * d + k') := by
  obtain ⟨σ, hσ, hor⟩ := greedyFratRound_augOr hcert h k' hk
  exact inDegLE_of_augStep (augStep_augOr D hcert.inj) hd (fratIn_le_of_backDegLE hσ hor)

/-! ### The width

The fraternity graph is materialized in memory, so its size is what
the scratch arrays are cut to. A fraternal partner of `v` is an
in-neighbour of a vertex `v` points at, so a vertex's fraternal degree
is at most its out-degree times `d`; summing, the out-degrees add up to
the number of arcs, which is at most `n · d`. -/

/-- The number of slots the fraternity graph occupies in compressed-row
form. -/
noncomputable def fratSlots (D : Orientation n) : ℕ := ∑ v, (fratNbrs D v).card

/-- The out-degrees add up to the in-degrees, both counting the arcs. -/
theorem sum_card_outSet (D : Orientation n) :
    ∑ v, (outSet D v).card = ∑ w, (D.inN w).card := by
  simp only [outSet, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.card_filter]
  congr 1
  ext v
  simp

/-- A fraternal partner of `v` is an in-neighbour of something `v`
points at. -/
theorem fratNbrs_subset (D : Orientation n) (v : Fin n) :
    fratNbrs D v ⊆ (outSet D v).biUnion (fun w => D.inN w) := by
  rw [fratNbrs_eq]
  exact Finset.erase_subset _ _

/-- **The width of the fraternity graph.** -/
theorem fratSlots_le {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) :
    fratSlots D ≤ n * (d * d) := by
  classical
  have hstep : ∀ v : Fin n, (fratNbrs D v).card ≤ (outSet D v).card * d := by
    intro v
    refine le_trans (Finset.card_le_card (fratNbrs_subset D v)) ?_
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ w ∈ outSet D v, (D.inN w).card ≤ ∑ _w ∈ outSet D v, d :=
          Finset.sum_le_sum fun w _ => hd w
      _ = (outSet D v).card * d := by rw [Finset.sum_const, smul_eq_mul]
  calc fratSlots D ≤ ∑ v, (outSet D v).card * d := Finset.sum_le_sum fun v _ => hstep v
    _ = (∑ v, (outSet D v).card) * d := by rw [Finset.sum_mul]
    _ = (∑ w, (D.inN w).card) * d := by rw [sum_card_outSet]
    _ ≤ (∑ _w : Fin n, d) * d := by
        exact Nat.mul_le_mul_right d (Finset.sum_le_sum fun w _ => hd w)
    _ = n * (d * d) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]

/-! ### The program

Ten passes over three block structures and one call. Two arrays are
the input — the block structure `doff`/`dtg` of `D` — three are the
output — `noff`/`ntg` and the ranking `rnk` the engine left — and the
rest is the round: the out-lists `ooff`/`otg` of `D`, the fraternity
graph in `off`/`tgt` where the engine expects its input, the fill
pointers `ofl`/`ffl`/`nfl`, the four stamp arrays, and the ten the
engine keeps to itself.

The stamps are what keeps every pass linear. A stamp array is `n`
cells, all zero between vertices; a pass that wants a set of vertices
in constant-time membership walks the list once setting the stamp, uses
it, and walks the same list again clearing it, so a vertex's whole turn
costs its own lists and no array is ever swept. `stf` is the
duplicate-killer of the fraternity build, `sta` the vertices `D`
already makes the current vertex adjacent to, `std` the vertices the
current vertex demands an arc *to* — which is the third clause of the
arc rule — and `ste` the duplicate-killer of the assembly. -/

/-- Scan the block of the vertex held in `x`, binding each target to
`w` and running `c`; the pointer `j` runs the block. -/
def blockScan (o t x j jend w : String) (c : Com) : Com :=
  .seq (Csr.loadRow o x j jend)
    (Csr.scan j jend
      (.seq (.assign w (.get t (.var j)))
        (.seq c (.assign j (.add (.var j) (.lit 1))))))

/-- `for i ∈ [0, n) do body`, the shape of every pass. -/
def forVerts (body : Com) : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.var "n")) (.seq body (.assign "i" (.add (.var "i") (.lit 1)))))

/-! #### The out-lists

A counting sort of the in-lists: an arc `u → i` is a slot of `i`'s
in-block and has to become a slot of `u`'s out-block. -/

/-- The out-degrees, counted into the offsets one place up. -/
def outCount : Com :=
  forVerts (blockScan "doff" "dtg" "i" "j" "jend" "u"
    (.store "ooff" (.add (.var "u") (.lit 1))
      (.add (.get "ooff" (.add (.var "u") (.lit 1))) (.lit 1))))

/-- The running sum that turns the degrees into offsets, opening each
block's fill pointer at its start. -/
def outPrefix : Com :=
  forVerts (.seq (.store "ooff" (.add (.var "i") (.lit 1))
      (.add (.get "ooff" (.add (.var "i") (.lit 1))) (.get "ooff" (.var "i"))))
    (.store "ofl" (.var "i") (.get "ooff" (.var "i"))))

/-- The arcs, written into the out-blocks. -/
def outFill : Com :=
  forVerts (blockScan "doff" "dtg" "i" "j" "jend" "u"
    (.seq (.store "otg" (.get "ofl" (.var "u")) (.var "i"))
      (.store "ofl" (.var "u") (.add (.get "ofl" (.var "u")) (.lit 1)))))

/-- The out-lists of `D`. -/
def outPass : Com := .seq outCount (.seq outPrefix outFill)

/-! #### The fraternity graph

The fraternal partners of `i` are the in-neighbours of the vertices `i`
points at, which is why the out-lists come first. The enumeration
repeats a partner once per witness, so both passes run it under the
stamp `stf` — `i` itself stamped first, which is how the loop of the
fraternity graph is kept out without a test. -/

/-- The fraternal partners of `i`, with duplicates. -/
def fratScan (act : Com) : Com :=
  blockScan "ooff" "otg" "i" "j" "jend" "w" (blockScan "doff" "dtg" "w" "q" "qe" "u" act)

/-- The fraternal degrees, counted into the offsets one place up. -/
def fratCount : Com :=
  forVerts (.seq (.assign "c" (.lit 0))
    (.seq (.store "stf" (.var "i") (.lit 1))
      (.seq (fratScan (.ite (.eq (.get "stf" (.var "u")) (.lit 0))
              (.seq (.store "stf" (.var "u") (.lit 1))
                (.assign "c" (.add (.var "c") (.lit 1)))) .skip))
        (.seq (fratScan (.store "stf" (.var "u") (.lit 0)))
          (.seq (.store "stf" (.var "i") (.lit 0))
            (.store "off" (.add (.var "i") (.lit 1)) (.var "c")))))))

/-- The running sum, into the block structure the engine reads. -/
def fratPrefix : Com :=
  forVerts (.seq (.store "off" (.add (.var "i") (.lit 1))
      (.add (.get "off" (.add (.var "i") (.lit 1))) (.get "off" (.var "i"))))
    (.store "ffl" (.var "i") (.get "off" (.var "i"))))

/-- The partners, written out once each. -/
def fratFill : Com :=
  forVerts (.seq (.store "stf" (.var "i") (.lit 1))
    (.seq (fratScan (.ite (.eq (.get "stf" (.var "u")) (.lit 0))
            (.seq (.store "stf" (.var "u") (.lit 1))
              (.seq (.store "tgt" (.get "ffl" (.var "i")) (.var "u"))
                (.store "ffl" (.var "i") (.add (.get "ffl" (.var "i")) (.lit 1))))) .skip))
      (.seq (fratScan (.store "stf" (.var "u") (.lit 0)))
        (.store "stf" (.var "i") (.lit 0)))))

/-- The fraternity graph, materialized where the engine reads its
input, with its slot count left in `mf`. -/
def fratPass : Com :=
  .seq fratCount (.seq fratPrefix (.seq fratFill (.assign "mf" (.get "off" (.var "n")))))

/-- The mask the engine is handed: nothing is killed, since the whole
fraternity graph is in play. -/
def alvSet : Com := forVerts (.store "alv" (.var "i") (.lit 1))

/-! #### The assembly

Three enumerations into the block of `i`, under the arc rule of
`NewArc`. `sta` holds the pairs `D` already carries, so its clause is
one lookup; `std` holds the vertices `i` demands an arc to — the
in-neighbours *and* the out-neighbours of what `i` points at, the
fraternal and the backwards-transitive halves of `Demand D i u` — so
the tie-break is one lookup and one comparison of ranks. A candidate
out of the engine's own block needs neither: a fraternal pair is
demanded both ways, and the engine has already put it the way the
ranking points. -/

/-- The two stamps of one vertex, set when `b` is one and cleared when
it is zero by the very same walk. -/
def asmStamp (b : ℕ) : Com :=
  .seq (blockScan "doff" "dtg" "i" "j" "jend" "u" (.store "sta" (.var "u") (.lit b)))
    (.seq (blockScan "ooff" "otg" "i" "j" "jend" "u" (.store "sta" (.var "u") (.lit b)))
      (blockScan "ooff" "otg" "i" "j" "jend" "w"
        (.seq (blockScan "doff" "dtg" "w" "q" "qe" "u" (.store "std" (.var "u") (.lit b)))
          (blockScan "ooff" "otg" "w" "q" "qe" "u" (.store "std" (.var "u") (.lit b))))))

/-- The three lists of the block of `i`, each element handed to `act`
once: the old in-neighbours, the transitive candidates that pass the
rule, and the engine's own in-block minus what `D` already carries. -/
def asmEmit (act : Com) : Com :=
  .seq (blockScan "doff" "dtg" "i" "j" "jend" "u" act)
    (.seq (blockScan "doff" "dtg" "i" "j" "jend" "w"
            (blockScan "doff" "dtg" "w" "q" "qe" "u"
              (.ite (.eq (.get "sta" (.var "u")) (.lit 0))
                (.ite (.eq (.get "ste" (.var "u")) (.lit 0))
                  (.ite (.eq (.get "std" (.var "u")) (.lit 0))
                    (.seq (.store "ste" (.var "u") (.lit 1)) act)
                    (.ite (.lt (.get "rnk" (.var "u")) (.get "rnk" (.var "i")))
                      (.seq (.store "ste" (.var "u") (.lit 1)) act) .skip))
                  .skip)
                .skip)))
      (blockScan "ioff" "itg" "i" "j" "jend" "u"
        (.ite (.eq (.get "sta" (.var "u")) (.lit 0))
          (.ite (.eq (.get "ste" (.var "u")) (.lit 0))
            (.seq (.store "ste" (.var "u") (.lit 1)) act) .skip)
          .skip)))

/-- The duplicate stamps of the assembly, cleared by the walk that set
them. -/
def asmClearE : Com :=
  .seq (blockScan "doff" "dtg" "i" "j" "jend" "w"
          (blockScan "doff" "dtg" "w" "q" "qe" "u" (.store "ste" (.var "u") (.lit 0))))
    (blockScan "ioff" "itg" "i" "j" "jend" "u" (.store "ste" (.var "u") (.lit 0)))

/-- One vertex's turn: stamp, emit, unstamp. -/
def asmRow (act : Com) : Com :=
  .seq (asmStamp 1) (.seq (asmEmit act) (.seq (asmStamp 0) asmClearE))

/-- The new in-degrees, counted into the offsets one place up. -/
def asmCount : Com :=
  forVerts (.seq (.assign "c" (.lit 0))
    (.seq (asmRow (.assign "c" (.add (.var "c") (.lit 1))))
      (.store "noff" (.add (.var "i") (.lit 1)) (.var "c"))))

/-- The running sum of the new block structure. -/
def asmPrefix : Com :=
  forVerts (.seq (.store "noff" (.add (.var "i") (.lit 1))
      (.add (.get "noff" (.add (.var "i") (.lit 1))) (.get "noff" (.var "i"))))
    (.store "nfl" (.var "i") (.get "noff" (.var "i"))))

/-- The new in-lists, written out. -/
def asmFill : Com :=
  forVerts (asmRow (.seq (.store "ntg" (.get "nfl" (.var "i")) (.var "u"))
    (.store "nfl" (.var "i") (.add (.get "nfl" (.var "i")) (.lit 1)))))

/-- The next orientation's block structure, with its arc count left in
`mn`. -/
def asmPass : Com :=
  .seq asmCount (.seq asmPrefix (.seq asmFill (.assign "mn" (.get "noff" (.var "n")))))

/-- **One round of the augmentation**: the out-lists, the fraternity
graph, the mask, the elimination, the assembly. -/
def augCom : Com := .seq outPass (.seq fratPass (.seq alvSet (.seq elimCom asmPass)))

/-! ### The specification -/

/-- The width the round's scratch arrays are cut to: room for the
fraternity graph, which is `n · d²` slots by `fratSlots_le`, and for
the block structure the round writes, which is at most `n²`. -/
def augWidth (n d : ℕ) : ℕ := n * (d + 1) ^ 2 + n * n + 1

/-- The fraternity graph fits in the width. -/
theorem fratSlots_lt_augWidth {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) :
    fratSlots D < augWidth n d := by
  have h₁ := fratSlots_le hd
  have h₂ : n * (d * d) ≤ n * (d + 1) ^ 2 := Nat.mul_le_mul_left n (by nlinarith)
  have : 0 ≤ n * n := Nat.zero_le _
  simp only [augWidth]
  omega

/-- The running time: ten passes over block structures whose slots the
width bounds, plus the engine, each linear. The constants are
generous — with `W` at `augWidth n d` this is
`O(n · (d+1)² + n²)`, which is the shape the campaign's budget is spent
against. -/
def augCost (n W : ℕ) : ℕ := 8000 * (n + W + 1)

/-- **What the round is handed.** The block structure of `D` and the
twenty-four scratch and output arrays at their lengths, with the nine
the passes never initialise — the three offset arrays a counting sort
accumulates into, the engine's own two, and the four stamps — required
zeroed, which is what the machine's memory already says.

The engine's arrays `tgt`, `itg`, `bv` and `bn` are cut to `nf`, the
fraternity graph's own slot count, and not to the width: `RamElim`'s
`ElimPre` pins them to exactly the slot count it is called at, so a
caller that materializes a graph of data-dependent size must allocate
them at that size. This is the one place where the engine's input
surface does not compose, and it is why `nf` is a parameter here with
`fratSlots D = nf` as a hypothesis rather than a number the round
picks. -/
def AugPre (n nf W : ℕ) (DO DT : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧
  σ.arrs "doff" = arrOf (n + 1) DO ∧ σ.arrs "dtg" = arrOf W DT ∧
  (∃ g, σ.arrs "ooff" = arrOf (n + 1) g ∧ ∀ j ≤ n, g j = 0) ∧
  (∃ g, σ.arrs "otg" = arrOf W g) ∧ (∃ g, σ.arrs "ofl" = arrOf n g) ∧
  (∃ g, σ.arrs "off" = arrOf (n + 1) g ∧ ∀ j ≤ n, g j = 0) ∧
  (∃ g, σ.arrs "tgt" = arrOf nf g) ∧ (∃ g, σ.arrs "ffl" = arrOf n g) ∧
  (∃ g, σ.arrs "alv" = arrOf n g) ∧ (∃ g, σ.arrs "deg" = arrOf n g) ∧
  (∃ g, σ.arrs "elm" = arrOf n g ∧ ∀ j < n, g j = 0) ∧
  (∃ g, σ.arrs "rnk" = arrOf n g) ∧ (∃ g, σ.arrs "idg" = arrOf n g) ∧
  (∃ g, σ.arrs "bh" = arrOf (n + 1) g ∧ ∀ j ≤ n, g j = 0) ∧
  (∃ g, σ.arrs "bv" = arrOf (n + nf + 1) g) ∧ (∃ g, σ.arrs "bn" = arrOf (n + nf + 1) g) ∧
  (∃ g, σ.arrs "ioff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "ifl" = arrOf n g) ∧
  (∃ g, σ.arrs "itg" = arrOf nf g) ∧
  (∃ g, σ.arrs "noff" = arrOf (n + 1) g ∧ ∀ j ≤ n, g j = 0) ∧
  (∃ g, σ.arrs "nfl" = arrOf n g) ∧ (∃ g, σ.arrs "ntg" = arrOf W g) ∧
  (∃ g, σ.arrs "stf" = arrOf n g ∧ ∀ j < n, g j = 0) ∧
  (∃ g, σ.arrs "sta" = arrOf n g ∧ ∀ j < n, g j = 0) ∧
  (∃ g, σ.arrs "std" = arrOf n g ∧ ∀ j < n, g j = 0) ∧
  (∃ g, σ.arrs "ste" = arrOf n g ∧ ∀ j < n, g j = 0)

/-- **What the round leaves**, in the vocabulary of the sections above:
the rank array carries a greedy elimination of the fraternity graph of
`D`, and the two output arrays carry the block structure of the
orientation the arc rule assembles from it. -/
def AugMem (n W : ℕ) (D : Orientation n) (_σ σ' : Env) : Prop :=
  ∃ (R NO NT : ℕ → ℕ) (k m' : ℕ),
    σ'.arrs "rnk" = arrOf n R ∧ σ'.vars "kmax" = k ∧
    σ'.arrs "noff" = arrOf (n + 1) NO ∧ σ'.arrs "ntg" = arrOf W NT ∧
    σ'.vars "mn" = m' ∧ m' ≤ W ∧
    ElimCert (fratGraph D) (fun v : Fin n => R (v : ℕ)) k ∧
    InCsr (augOr D (fun v : Fin n => R (v : ℕ))) m' NO NT

/-- **The postconditions**, spelled out: there is an orientation `D'`
that the round's arc rule produced, it is an augmentation step of `D`,
the output arrays are its block structure — so the next round reads
them as this one read its own — the reported bound is at most every
bound a density argument can produce of the fraternity graph, and the
greedy clause and the in-degree budget follow as soon as the arcs `D'`
inherited from `D` on fraternity edges point the way the ranking does.
The last — the running time — is the `Spec`'s own cost. -/
def AugPost (n W : ℕ) (D : Orientation n) (_σ σ' : Env) : Prop :=
  ∃ (R NO NT : ℕ → ℕ) (k m' : ℕ) (D' : Orientation n),
    σ'.arrs "rnk" = arrOf n R ∧ σ'.vars "kmax" = k ∧
    σ'.arrs "noff" = arrOf (n + 1) NO ∧ σ'.arrs "ntg" = arrOf W NT ∧
    σ'.vars "mn" = m' ∧ m' ≤ W ∧
    AugStep D D' ∧ InCsr D' m' NO NT ∧
    (∀ k', LowDegreeVertices (fratGraph D) k' → k ≤ k') ∧
    (FratForward D (fun v : Fin n => R (v : ℕ)) → GreedyFratRound D D') ∧
    (∀ d k', FratForward D (fun v : Fin n => R (v : ℕ)) → D.InDegLE d →
      LowDegreeVertices (fratGraph D) k' → D'.InDegLE (d + d * d + k'))

/-- **The postconditions come off the certificate and the arc rule.**
Nothing in this proof knows about the program: it is the assembly
section, read once. -/
theorem augPost_of_augMem {n W : ℕ} {D : Orientation n} {σ σ' : Env}
    (h : AugMem n W D σ σ') : AugPost n W D σ σ' := by
  obtain ⟨R, NO, NT, k, m', hrnk, hk, hnoff, hntg, hmn, hmW, hcert, harcs⟩ := h
  exact ⟨R, NO, NT, k, m', augOr D (fun v : Fin n => R (v : ℕ)), hrnk, hk, hnoff, hntg,
    hmn, hmW, augStep_augOr D hcert.inj, harcs,
    fun _ hk' => hcert.le_of_lowDegreeVertices hk',
    fun hf => greedyFratRound_augOr hcert hf,
    fun _ _ hf hd hk' => inDegLE_augOr hcert hf hd hk'⟩

/-- The engine, available at every slot count the round can call it
at. This is `RamElim.Implements` with the call's own data quantified
away, so that discharging that one obligation discharges this
hypothesis at every use. -/
def ElimAvail (B n : ℕ) (F : SimpleGraph (Fin n)) : Prop :=
  ∀ (ns : ℕ) (M O T : ℕ → ℕ), RamElim.Implements B n ns F M O T

/-- **The one thing this file leaves open.** `augCom` is exhibited,
compiled and run — the worked example below checks the block structure
it produces against the hand computation — and everything its answers
*mean* is proved above, in `augOr` and `inN_augOr_eq`. What is isolated
here is the Hoare triple itself: that the round's ten passes and its
one call leave memory in the state `AugMem` describes, within the cost
`augCost`. It is stated over the program text and the input surface a
caller has, so it is a self-contained obligation and not a hole in a
statement.

It splits along the passes.

* `outPass` is a counting sort, three flat loops, and it establishes
  the out-lists as `CsrGraph`-style blocks of `outSet D`.
* `fratPass` is the same shape with a stamped inner enumeration; its
  content is that a stamped walk emits each fraternal partner once,
  which is `CsrSimple` of `fratGraph D` and the slot count
  `fratSlots D`.
* `alvSet` is `Fill.loop_spec` with the constant one, and
  `RamElim.masked_of_all_alive` turns the arena it produces back into
  the fraternity graph.
* `elimCom` enters through `RamElim.elim_spec` at `ns = fratSlots D`,
  whose `Implements` is `ElimAvail`'s; its postcondition is
  `ElimCert (fratGraph D) ρ k` and the in-blocks of
  `ElimCert.elimOr (fratGraph D) ρ`.
* `asmPass` is the counting sort once more, and its content is
  `inN_augOr_eq`: the three enumerations under the arc rule, stamped,
  emit each member of `(augOr D ρ).inN v` exactly once.

The cost is flat: every pass is charged per slot of the block
structure it walks, and the walks of `fratScan` and of the assembly's
stamps are charged by `sum_card_outSet` — the out-degrees add up to the
arcs — so each is `O(n · d²)`, and the engine's is `elimCost`. -/
def Implements (B n d nf W m : ℕ) (D : Orientation n) (DO DT : ℕ → ℕ) : Prop :=
  ElimAvail B n (fratGraph D) →
  InCsr D m DO DT → D.InDegLE d → fratSlots D = nf → m ≤ W → augWidth n d ≤ W →
  n + W + 1 < B →
  Spec B (AugPre n nf W DO DT) augCom (AugMem n W D) (augCost n W)

/-- **One round of transitive–fraternal augmentation.** Handed the
in-neighbour block structure of an orientation `D` of in-degree at most
`d`, and the scratch arrays at their lengths, `augCom` leaves in
`noff`/`ntg` the block structure of an orientation `D'` with
`AugStep D D'`, in `kmax` the degeneracy bound the greedy elimination
of the fraternity graph achieved — at most every bound a density
argument can produce — and in `rnk` the ranking that bound belongs to,
along which every fraternal arc of `D'` points. -/
theorem augment_spec {B n d nf W m : ℕ} {D : Orientation n} {DO DT : ℕ → ℕ}
    (h : Implements B n d nf W m D DO DT) (he : ElimAvail B n (fratGraph D))
    (hcsr : InCsr D m DO DT) (hd : D.InDegLE d) (hnf : fratSlots D = nf)
    (hm : m ≤ W) (hW : augWidth n d ≤ W) (hB : n + W + 1 < B) :
    Spec B (AugPre n nf W DO DT) augCom (AugPost n W D) (augCost n W) :=
  (h he hcsr hd hnf hm hW hB).post fun _ _ _ hq => augPost_of_augMem hq

/-! ### The composition surface

What a driver does with the round. `AugPost` hands back an orientation
and an `AugStep`, and the two facts a chain is made of are carried by
the two lemmas here: `isAugChain_succ` grows the chain by the step, and
`greedyFratRound_succ` grows the list of greedy rounds by the
implication `AugPost` exports — so an `r`-round driver iterating
`augment_spec` and collecting the two ends up in the hypotheses of
`Augmentation.greedy_chain_inDegLE` exactly.

The memory side composes because the round's input and output block
structures have the *same shape*: the input is `doff`/`dtg` at lengths
`n+1` and `W` with `InCsr D m DO DT` and `m ≤ W`, and the output is
`noff`/`ntg` at the same two lengths with `InCsr D' m' NO NT` and
`m' ≤ W`. So a round is followed by a copy of `noff`/`ntg` into
`doff`/`dtg` and a re-zeroing of the six accumulator and stamp arrays,
both flat loops of `Fill.loop_spec`, and the width `W` is chosen once,
at `augWidth n d_r` for the largest in-degree the budget recursion
reaches. -/

/-- **The chain, one round longer.** -/
theorem isAugChain_succ {G : SimpleGraph (Fin n)} {D : ℕ → Orientation n} {r : ℕ}
    (h : IsAugChain G D r) (hstep : AugStep (D r) (D (r + 1))) : IsAugChain G D (r + 1) :=
  ⟨h.1, fun i hi => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact h.2 i hi
    · exact hstep⟩

/-- **The greedy rounds, one round longer.** -/
theorem greedyFratRound_succ {D : ℕ → Orientation n} {r : ℕ}
    (h : ∀ i < r, GreedyFratRound (D i) (D (i + 1)))
    (hstep : GreedyFratRound (D r) (D (r + 1))) :
    ∀ i < r + 1, GreedyFratRound (D i) (D (i + 1)) := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
  · exact h i hi
  · exact hstep

/-! ### The worked example

House discipline: what the specification says is also *seen*. The
orientation is the four-vertex one with arcs `0 → 1`, `0 → 2`,
`1 → 2`, `2 → 3` — in-lists `∅ | 0 | 0 1 | 2`, in-degree two — and it
exercises every clause of the arc rule at once.

Its fraternity graph is the single edge `{0,1}`, both in the block of
`2`; the engine peels `3, 2, 1, 0` off it, reports the bound one and
ranks `0, 1, 2, 3`, and orients the edge `0 → 1`. That arc is
*discarded* by the assembly, since `D` already carries `0 → 1` — the
first clause of the rule at work. The transitive links are `0 → 2`
(discarded, `D` carries it), `0 → 3` and `1 → 3`, neither demanded
backwards, so both are taken forward without consulting the ranking.

So the next in-lists are `∅ | 0 | 0 1 | 2 0 1`: the offsets
`0, 0, 1, 3, 6` and the six slots `0 | 0 1 | 2 0 1`, with `mn = 6`. -/

namespace Demo

/-- The offsets of the in-lists `∅ | 0 | 0 1 | 2`. -/
def demoDoff : Com :=
  .seq (.store "doff" (.lit 0) (.lit 0))
    (.seq (.store "doff" (.lit 1) (.lit 0))
      (.seq (.store "doff" (.lit 2) (.lit 1))
        (.seq (.store "doff" (.lit 3) (.lit 3))
          (.store "doff" (.lit 4) (.lit 4)))))

/-- Their targets: `| 0 | 0 1 | 2`. -/
def demoDtg : Com :=
  .seq (.store "dtg" (.lit 0) (.lit 0))
    (.seq (.store "dtg" (.lit 1) (.lit 0))
      (.seq (.store "dtg" (.lit 2) (.lit 1))
        (.store "dtg" (.lit 3) (.lit 2))))

/-- Four vertices, four arcs. -/
def demoSetup : Com := .seq (.assign "n" (.lit 4)) (.seq demoDoff demoDtg)

/-- The four ranks, the bound, the fraternity slot count, the five new
offsets, the six new slots and the new arc count, in that order. -/
def demoReport : Com :=
  ([.get "rnk" (.lit 0), .get "rnk" (.lit 1), .get "rnk" (.lit 2), .get "rnk" (.lit 3),
    .var "kmax", .var "mf",
    .get "noff" (.lit 0), .get "noff" (.lit 1), .get "noff" (.lit 2), .get "noff" (.lit 3),
    .get "noff" (.lit 4),
    .get "ntg" (.lit 0), .get "ntg" (.lit 1), .get "ntg" (.lit 2), .get "ntg" (.lit 3),
    .get "ntg" (.lit 4), .get "ntg" (.lit 5), .var "mn"] : List Expr).foldr
    (fun e c => .seq (.write e) c) .skip

/-- Build the orientation, run the round, report. -/
def demoWatched : Com := .seq demoSetup (.seq augCom demoReport)

/-- Twenty scalars, twenty-six arrays, four temporaries. -/
def demoLayout : Lax13Proofs.Compile.Layout :=
  ⟨["n", "i", "j", "jend", "q", "qe", "u", "w", "c", "s", "d", "sp", "ls", "mind", "cnt",
    "kmax", "p", "sc", "mf", "mn"],
   ["doff", "dtg", "ooff", "otg", "ofl", "off", "tgt", "ffl", "alv", "deg", "elm", "rnk",
    "idg", "bh", "bv", "bn", "ioff", "ifl", "itg", "noff", "nfl", "ntg", "stf", "sta",
    "std", "ste"],
   4⟩

/-- The machine program. -/
def demoProg : Lax13.Ram.Program :=
  Lax13Proofs.Compile.compileProgram demoLayout demoWatched

/-- The layout covers the round, so the compilation is the one the
simulation theorem is about and not an accident. -/
theorem demoWatched_ok : Lax13Proofs.Compile.Com.Ok demoLayout demoWatched := by
  simp [demoWatched, demoSetup, demoDoff, demoDtg, demoReport, augCom, outPass, outCount,
    outPrefix, outFill, fratPass, fratCount, fratPrefix, fratFill, fratScan, alvSet,
    asmPass, asmCount, asmPrefix, asmFill, asmRow, asmStamp, asmEmit, asmClearE,
    blockScan, forVerts, Csr.loadRow, Csr.scan, RamElim.elimCom, RamElim.initDeg,
    RamElim.degRow, RamElim.degSlot, RamElim.initBuck, RamElim.initBuckRow, RamElim.push,
    RamElim.elimLoop, RamElim.elimTurn, RamElim.elimVertex, RamElim.decSlot,
    RamElim.offPass, RamElim.offRow, RamElim.fillPass, RamElim.fillRow, RamElim.fillSlot,
    demoLayout, Lax13Proofs.Compile.Com.Ok, Lax13Proofs.Compile.Cond.Ok,
    Lax13Proofs.Compile.condExpr, Lax13Proofs.Compile.Expr.Ok]

/-- Run it at a word length that holds every number this round
produces. -/
def demoRun : Option (List ℕ × ℕ) :=
  runOut 16 4000000 demoProg (Lax13.Ram.initState []) 0

-- the ranks `0, 1, 2, 3` of the peeling `3, 2, 1, 0`, the bound `1`
-- that the single fraternal edge forces, the two slots that edge takes
-- symmetrized, the offsets `0, 0, 1, 3, 6` and the six slots
-- `| 0 | 0 1 | 2 0 1`, six arcs in all
#guard demoRun = some ([0, 1, 2, 3, 1, 2, 0, 0, 1, 3, 6, 0, 0, 1, 2, 0, 1, 6], 37489)

/-! And the arithmetic on the other side of the abstraction: the two
arrays the run reported really cut into the in-neighbour lists the next
orientation is supposed to have. -/

/-- The block of `v`, read off a pair of reported arrays. -/
def demoBlock (NO NT : List ℕ) (v : ℕ) : List ℕ :=
  (List.range (NO.getD (v + 1) 0 - NO.getD v 0)).map fun t => NT.getD (NO.getD v 0 + t) 0

-- the old arcs kept, the fraternal arc `0 → 1` discarded because `D`
-- carried it already, and the two transitive arcs `0 → 3`, `1 → 3`
-- taken forward: in-degrees `0, 1, 2, 3`
#guard demoBlock [0, 0, 1, 3, 6] [0, 0, 1, 2, 0, 1] 0 = []
#guard demoBlock [0, 0, 1, 3, 6] [0, 0, 1, 2, 0, 1] 1 = [0]
#guard demoBlock [0, 0, 1, 3, 6] [0, 0, 1, 2, 0, 1] 2 = [0, 1]
#guard demoBlock [0, 0, 1, 3, 6] [0, 0, 1, 2, 0, 1] 3 = [2, 0, 1]

end Demo

end Lax3Proofs.RamAugment
