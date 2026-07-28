import Lax3Proofs.SplitterWin

/-!
Splitter's win in the isolation splitter game, over an arbitrary source
of short walks: the parametric form of `Lax3Proofs.SplitterWin`.

# Why this file exists

`Lax3Proofs.SplitterWin` fixes Splitter's strategy once and for all with
`pathSet`, a `Classical.choice` walk of length at most `r` between two
vertices of one arena. The model-checking program cannot make that
choice: it computes its own shortest paths, by breadth-first search in
the arena it currently holds, and the walk it ends up with is whatever
its search found.

It does not have to make that choice. No proof of `SplitterWin` ever
looks at *which* walk `pathSet` returned. Everything is deduced from two
facts:

* `pathSet_spec` — between vertices at distance at most `r` the returned
  set is the support of a genuine walk of length at most `r`; and
* `pathSet_ncard_le` — the returned set has at most `r + 1` vertices.

Those are the fields `spec` and `card` of `PathOracle` below, and with
them alone the whole development goes through for an arbitrary oracle.
Nothing else about `pathSet` is needed. In particular the oracle is
asked for nothing when the two vertices are far apart: `pathSet` returns
`∅` there, but that clause is used only to bound its cardinality, which
the oracle asserts outright. The set an oracle returns is only ever
*used* through `spec`, never through membership on its own.

# What is here

This file is a deliberate transcription of the `pathSet`-dependent layer
of `SplitterWin` with `pathSet` replaced by `O.path`: `genSetO`,
`batchO`, `nextArenaO`, `ReachedO`, the invariants (`isolatedO_of_suffix`,
`mem_ball_of_suffixO`, `picksO_nodup`, `reachedO_entry`, `pairO_walk`,
`pairO_disjoint`), `no_full_survivalO` and `splitterWins_of_reachedO`
line up one for one with their unsuffixed originals and are proved the
same way. Everything generic is imported rather than repeated: the walk
helpers, the `Iff.rfl` lemmas opening the concept-side definitions,
`eq_of_mem_ball_of_isolated`, `eq_bot_of_isolated`, the list plumbing
(`entry_suffix`, `getElem_mem_drop`) and `exists_avoiding`.

`SplitterWin`'s concrete strategy is recovered as the instance
`defaultOracle`; `reachedO_defaultOracle` and
`splitterWins_of_reached_default` re-derive its consumable from this
file's, which is the sanity check that the generalization is faithful.

# What the program phase takes from here

A driver whose per-level data is its current arena `A` together with the
stack `rounds` of the `(connector vertex, arena)` pairs already played
maintains `ReachedO O G rounds A` as its invariant, with `O` the oracle
"the walk my breadth-first search found":

* it starts at `rounds = []`, `A = G`, where the invariant is
  `ReachedO.nil`;
* at each level it reads Connector's vertex `v` and plays the batch
  `batchO O rounds A v`; `reachedO_descend` says in one step that this
  batch is a legal move (inside the ball, and within the size bound
  `ℓ · (r + 1)` as long as fewer than `ℓ` rounds are on the stack) and
  that pushing `(v, A)` onto the stack and moving to
  `nextArenaO O A v rounds` restores the invariant;
* if `v` has no incident edge in `A` the round is over anyway, since the
  arena it leaves is edgeless (`nextArenaO_eq_bot_of_isolated`);
* the recursion terminates: `reachedO_length_lt` bounds the stack by
  `N (2·s + 2)`, since by `reachedO_no_survival` no play reaches that
  length.

`splitterWins_of_reachedO` is the same statement in the game's own terms,
available at every position the driver passes through.

No tactic in this file is handed a concept-side definition, exactly as in
`SplitterWin`: `WithinDist` and `DistIndependent` are opened by that
file's `Iff.rfl` lemmas, `SplitterWins` and `deleteVerts` by the clause
lemmas of `Lax3Proofs.SplitterBasics`, and balls by
`Lax3Proofs.WalkDistance`.
-/

namespace Lax3Proofs.SplitterWinOracle

open Lax3.ColoredGraphs Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax3Proofs.SplitterBasics Lax3Proofs.WalkDistance Lax3Proofs.SplitterWin

section Oracle

/-! ### The oracle -/

/-- A source of the short walks Splitter's strategy maintains: for a
recorded arena `A` and two of its vertices, a set of vertices meant to be
the support of a walk of length at most `r` between them.

`spec` is everything the strategy asks when the two vertices are close
enough to be joined: the returned set really is the support of such a
walk. `card` is the bound Splitter's batch size is computed from, and is
asked unconditionally — an oracle may return anything it likes between
far apart vertices, as long as it returns few vertices, because the
strategy only ever uses the returned set through `spec`. -/
structure PathOracle (n : ℕ) (r : ℕ) where
  /-- The vertex set the oracle offers for an arena and two vertices. -/
  path : SimpleGraph (Fin n) → Fin n → Fin n → Set (Fin n)
  /-- Between vertices within distance `r` the offered set is the support
  of a genuine walk of length at most `r`. -/
  spec : ∀ A u v, WithinDist A r u v →
    ∃ p : A.Walk u v, p.length ≤ r ∧ path A u v = {z | z ∈ p.support}
  /-- The offered set has at most `r + 1` vertices. -/
  card : ∀ A u v, (path A u v).ncard ≤ r + 1

/-- The strategy of `Lax3Proofs.SplitterWin` as an oracle: the chosen
walks of `pathSet`. -/
noncomputable def defaultOracle (n r : ℕ) : PathOracle n r where
  path A u v := pathSet A r u v
  spec _ _ _ h := pathSet_spec h
  card A u v := pathSet_ncard_le A r u v

/-- The default oracle offers exactly `pathSet`'s chosen walks. -/
theorem defaultOracle_path (n r : ℕ) (A : SimpleGraph (Fin n)) (u v : Fin n) :
    (defaultOracle n r).path A u v = pathSet A r u v := rfl

end Oracle

section Play

/-! ### Batches and arenas

Histories are `SplitterWin.Round` lists, newest first, exactly as in the
unparameterized development; the oracle only changes which vertices a
round isolates.
-/

variable {n r : ℕ}

/-- The vertices Splitter wants to isolate when Connector plays `v`: `v`
itself together with the oracle's paths from every earlier Connector
vertex to `v`, each taken in the arena that round was played in. -/
def genSetO (O : PathOracle n r) : List (Round n) → Fin n → Set (Fin n)
  | [], v => {v}
  | e :: rest, v => O.path e.2 e.1 v ∪ genSetO O rest v

/-- Connector's new vertex is among the vertices the strategy
isolates. -/
theorem self_mem_genSetO (O : PathOracle n r) (rounds : List (Round n)) (v : Fin n) :
    v ∈ genSetO O rounds v := by
  induction rounds with
  | nil => simp only [genSetO]; exact rfl
  | cons e rest ih => simp only [genSetO]; exact Or.inr ih

/-- The oracle's path from an earlier round's vertex is among the
vertices the strategy isolates. -/
theorem path_subset_genSetO {O : PathOracle n r} {rounds : List (Round n)} {e : Round n}
    (he : e ∈ rounds) (v : Fin n) : O.path e.2 e.1 v ⊆ genSetO O rounds v := by
  induction rounds with
  | nil => exact absurd he (by simp)
  | cons e' rest ih =>
    simp only [genSetO]
    rcases List.mem_cons.mp he with rfl | h
    · exact Set.subset_union_left
    · exact fun z hz => Or.inr (ih h hz)

/-- One vertex plus one path of at most `r + 1` vertices per earlier
round. -/
theorem genSetO_ncard_le (O : PathOracle n r) (rounds : List (Round n)) (v : Fin n) :
    (genSetO O rounds v).ncard ≤ 1 + rounds.length * (r + 1) := by
  induction rounds with
  | nil => simp only [genSetO, Set.ncard_singleton, List.length_nil]; omega
  | cons e rest ih =>
    have h1 : (genSetO O (e :: rest) v).ncard
        ≤ (O.path e.2 e.1 v).ncard + (genSetO O rest v).ncard := by
      simp only [genSetO]; exact Set.ncard_union_le _ _
    have h2 := O.card e.2 e.1 v
    have h3 : (rest.length + 1) * (r + 1) = rest.length * (r + 1) + (r + 1) :=
      Nat.succ_mul _ _
    simp only [List.length_cons]
    omega

/-- Splitter's batch after the history `rounds` when Connector plays `v`
in the arena `A`: the vertices of `genSetO` that are still in the ball
the round restricts to. -/
def batchO (O : PathOracle n r) (rounds : List (Round n)) (A : SimpleGraph (Fin n))
    (v : Fin n) : Set (Fin n) :=
  genSetO O rounds v ∩ ball A r v

/-- The batch is a legal move: it lies in the ball of the round. -/
theorem batchO_subset_ball (O : PathOracle n r) (rounds : List (Round n))
    (A : SimpleGraph (Fin n)) (v : Fin n) : batchO O rounds A v ⊆ ball A r v :=
  Set.inter_subset_right

/-- Membership in the batch is membership in `genSetO` and in the
ball. -/
theorem mem_batchO {O : PathOracle n r} {rounds : List (Round n)}
    {A : SimpleGraph (Fin n)} {v z : Fin n} (hg : z ∈ genSetO O rounds v)
    (hb : z ∈ ball A r v) : z ∈ batchO O rounds A v := ⟨hg, hb⟩

/-- The batch is bounded by one vertex per round and one path per
round. -/
theorem batchO_ncard_le (O : PathOracle n r) (rounds : List (Round n))
    (A : SimpleGraph (Fin n)) (v : Fin n) :
    (batchO O rounds A v).ncard ≤ 1 + rounds.length * (r + 1) :=
  le_trans (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _))
    (genSetO_ncard_le O rounds v)

/-- The batch bound in the form the game asks for: below a round budget
`ℓ`, a batch has at most `ℓ · (r + 1)` vertices. -/
theorem batchO_ncard_le_of_lt (O : PathOracle n r) (rounds : List (Round n))
    (A : SimpleGraph (Fin n)) (v : Fin n) {ℓ : ℕ} (h : rounds.length < ℓ) :
    (batchO O rounds A v).ncard ≤ ℓ * (r + 1) := by
  have h1 := batchO_ncard_le O rounds A v
  have h2 : (rounds.length + 1) * (r + 1) = rounds.length * (r + 1) + (r + 1) :=
    Nat.succ_mul _ _
  have h3 : (rounds.length + 1) * (r + 1) ≤ ℓ * (r + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- The arena after a round: restrict `A` to the ball around Connector's
vertex `v`, then isolate Splitter's batch. -/
def nextArenaO (O : PathOracle n r) (A : SimpleGraph (Fin n)) (v : Fin n)
    (rounds : List (Round n)) : SimpleGraph (Fin n) :=
  deleteVerts (deleteVerts A (ball A r v)ᶜ) (batchO O rounds A v)

/-- A round only removes edges. -/
theorem nextArenaO_le (O : PathOracle n r) (A : SimpleGraph (Fin n)) (v : Fin n)
    (rounds : List (Round n)) : nextArenaO O A v rounds ≤ A :=
  le_trans (deleteVerts_le _ _) (deleteVerts_le _ _)

/-- Every edge surviving a round has both ends in the ball the round
restricted to. -/
theorem mem_ball_of_nextArenaO_adj {O : PathOracle n r} {A : SimpleGraph (Fin n)}
    {v z w : Fin n} {rounds : List (Round n)} (h : (nextArenaO O A v rounds).Adj z w) :
    z ∈ ball A r v :=
  not_not.mp (deleteVerts_adj.mp (deleteVerts_adj.mp h).1).2.1

/-- No edge surviving a round touches the batch. -/
theorem not_mem_batchO_of_nextArenaO_adj {O : PathOracle n r} {A : SimpleGraph (Fin n)}
    {v z w : Fin n} {rounds : List (Round n)} (h : (nextArenaO O A v rounds).Adj z w) :
    z ∉ batchO O rounds A v :=
  (deleteVerts_adj.mp h).2.1

/-- Playing an isolated vertex loses at once: whatever the oracle offers,
the arena the round leaves is edgeless, since the ball around such a
vertex is a single vertex. -/
theorem nextArenaO_eq_bot_of_isolated (O : PathOracle n r) {A : SimpleGraph (Fin n)}
    {v : Fin n} (hv : ∀ z, ¬ A.Adj v z) (rounds : List (Round n)) :
    nextArenaO O A v rounds = ⊥ :=
  eq_bot_of_isolated hv _

/-! ### Reachable positions -/

variable {O : PathOracle n r} {G : SimpleGraph (Fin n)}

/-- The positions of a play from `G`, following the oracle's strategy, in
which every Connector move so far was a vertex that still had an incident
edge. This is `SplitterWin.Reached` with `pathSet` replaced by the
oracle; moves on isolated vertices are again not recorded, since they end
the play at once (`nextArenaO_eq_bot_of_isolated`). -/
inductive ReachedO (O : PathOracle n r) (G : SimpleGraph (Fin n)) :
    List (Round n) → SimpleGraph (Fin n) → Prop
  | nil : ReachedO O G [] G
  | step {rounds : List (Round n)} {A : SimpleGraph (Fin n)} {v : Fin n}
      (h : ReachedO O G rounds A) (hv : ∃ u, A.Adj v u) :
      ReachedO O G ((v, A) :: rounds) (nextArenaO O A v rounds)

variable {A : SimpleGraph (Fin n)} {rounds : List (Round n)}

/-- Inverting a played round: the arena an entry records is the position
its own older rounds reach, its vertex had an incident edge there, and
the position after it is the round's arena. -/
theorem reachedO_cons {v : Fin n} {A₀ : SimpleGraph (Fin n)}
    (h : ReachedO O G ((v, A₀) :: rounds) A) :
    ReachedO O G rounds A₀ ∧ (∃ u, A₀.Adj v u) ∧ A = nextArenaO O A₀ v rounds := by
  cases h with
  | step h hv => exact ⟨h, hv, rfl⟩

/-- Every reachable arena is a subgraph of the original: rounds only
delete edges. -/
theorem reachedO_le (h : ReachedO O G rounds A) : A ≤ G := by
  induction h with
  | nil => exact le_rfl
  | step _ _ ih => exact le_trans (nextArenaO_le ..) ih

/-- Every earlier stretch of a play is itself a play. -/
theorem reachedO_suffix (h : ReachedO O G rounds A) :
    ∀ t : List (Round n), t <:+ rounds → ∃ B, ReachedO O G t B := by
  induction h with
  | nil =>
    intro t ht
    rw [List.suffix_nil.mp ht]
    exact ⟨G, ReachedO.nil⟩
  | @step rounds A v hh hv ih =>
    intro t ht
    rcases List.suffix_cons_iff.mp ht with rfl | ht'
    · exact ⟨_, ReachedO.step hh hv⟩
    · exact ih t ht'

/-- **Isolation is permanent.** Every vertex the strategy meant to
isolate in a played round has no incident edge in any later arena: in the
arena right after the round it is either outside the ball the round
restricted to or inside the isolated batch, and later arenas only lose
further edges. -/
theorem isolatedO_of_suffix (h : ReachedO O G rounds A) :
    ∀ (e : Round n) (older : List (Round n)), e :: older <:+ rounds →
      ∀ z ∈ genSetO O older e.1, ∀ u, ¬ A.Adj z u := by
  induction h with
  | nil => intro e older he; exact absurd he (by simp)
  | @step rounds A v hh hv ih =>
    intro e older he z hz u hadj
    rcases List.suffix_cons_iff.mp he with heq | he'
    · injection heq with h1 h2
      subst h1
      subst h2
      exact not_mem_batchO_of_nextArenaO_adj hadj
        (mem_batchO hz (mem_ball_of_nextArenaO_adj hadj))
    · exact ih e older he' z hz u (nextArenaO_le O A v rounds hadj)

/-- A vertex that still carries an edge lies in the ball of every earlier
round: a round keeps only the edges inside that ball, and later rounds
keep fewer. -/
theorem mem_ball_of_suffixO (h : ReachedO O G rounds A) :
    ∀ (e : Round n) (older : List (Round n)), e :: older <:+ rounds →
      ∀ z u, A.Adj z u → z ∈ ball e.2 r e.1 := by
  induction h with
  | nil => intro e older he; exact absurd he (by simp)
  | @step rounds A v hh hv ih =>
    intro e older he z u hadj
    rcases List.suffix_cons_iff.mp he with heq | he'
    · injection heq with h1 h2
      subst h1
      exact mem_ball_of_nextArenaO_adj hadj
    · exact ih e older he' z u (nextArenaO_le O A v rounds hadj)

/-- Connector never repeats a vertex in a surviving play: an earlier
vertex is isolated from the round it was played on, while the current one
still carries an edge. -/
theorem picksO_nodup (h : ReachedO O G rounds A) : (rounds.map Prod.fst).Nodup := by
  induction h with
  | nil => simp
  | @step rounds A v hh hv ih =>
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, ih⟩
    obtain ⟨e, he, hev⟩ := List.mem_map.mp hmem
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem he
    obtain ⟨u, hu⟩ := hv
    refine isolatedO_of_suffix hh e post ?_ v ?_ u hu
    · rw [hsplit]; exact List.suffix_append pre (e :: post)
    · have hev' : e.1 = v := hev
      rw [← hev']
      exact self_mem_genSetO O post e.1

/-! ### Pairs of rounds -/

/-- The position at the round with index `b`, together with the incident
edge its vertex still had there. -/
theorem reachedO_entry (h : ReachedO O G rounds A) {b : ℕ} (hb : b < rounds.length) :
    ReachedO O G (rounds.drop (b + 1)) (rounds[b]).2 ∧
      ∃ u, (rounds[b]).2.Adj (rounds[b]).1 u := by
  obtain ⟨B, hB⟩ := reachedO_suffix h (rounds.drop b) (List.drop_suffix b rounds)
  rw [List.drop_eq_getElem_cons hb] at hB
  obtain ⟨h1, h2, -⟩ := reachedO_cons (v := (rounds[b]).1) (A₀ := (rounds[b]).2) hB
  exact ⟨h1, h2⟩

/-- The path the strategy maintains for a pair of rounds. The newer
round's vertex still had an edge, so it lies in the ball the older round
restricted to, and the oracle's set between them is therefore the support
of a genuine walk of length at most `r` in the older round's arena. Its
endpoints are distinct: the older vertex is already isolated when the
newer round is played. -/
theorem pairO_walk (h : ReachedO O G rounds A) {b a : ℕ}
    (hb : b < rounds.length) (ha : a < rounds.length) (hba : b < a) :
    ∃ p : (rounds[a]).2.Walk (rounds[a]).1 (rounds[b]).1,
      p.length ≤ r ∧
      O.path (rounds[a]).2 (rounds[a]).1 (rounds[b]).1 = {z | z ∈ p.support} ∧
      (rounds[a]).1 ≠ (rounds[b]).1 := by
  obtain ⟨hRb, u, hu⟩ := reachedO_entry h hb
  have hball : (rounds[b]).1 ∈ ball (rounds[a]).2 r (rounds[a]).1 :=
    mem_ball_of_suffixO hRb rounds[a] (rounds.drop (a + 1))
      (entry_suffix (j := b + 1) ha hba) _ u hu
  obtain ⟨p, hplen, hpset⟩ := O.spec _ _ _ (mem_ball.mp hball)
  refine ⟨p, hplen, hpset, fun hEq => ?_⟩
  refine isolatedO_of_suffix hRb rounds[a] (rounds.drop (a + 1))
    (entry_suffix (j := b + 1) ha hba) (rounds[a]).1
    (self_mem_genSetO O (rounds.drop (a + 1)) (rounds[a]).1) u ?_
  rw [hEq]
  exact hu

/-- **Distinct pairs' paths are disjoint.** A vertex on the older pair's
path is one the strategy isolated when the older pair's newer round was
played, hence has no edge in any arena from then on; but the newer pair's
path is the support of a walk of positive length in an arena strictly
later than that, so each of its vertices does carry an edge. -/
theorem pairO_disjoint (h : ReachedO O G rounds A) {bNew aNew bOld aOld : ℕ}
    (hbNew : bNew < rounds.length) (haNew : aNew < rounds.length)
    (hbOld : bOld < rounds.length) (haOld : aOld < rounds.length)
    (h1 : bNew < aNew) (h2 : aNew < bOld) (h3 : bOld < aOld) {z : Fin n}
    (hzOld : z ∈ O.path (rounds[aOld]).2 (rounds[aOld]).1 (rounds[bOld]).1)
    (hzNew : z ∈ O.path (rounds[aNew]).2 (rounds[aNew]).1 (rounds[bNew]).1) :
    False := by
  have hgen : z ∈ genSetO O (rounds.drop (bOld + 1)) (rounds[bOld]).1 :=
    path_subset_genSetO (getElem_mem_drop (j := bOld + 1) haOld h3) (rounds[bOld]).1 hzOld
  obtain ⟨hRa, -⟩ := reachedO_entry h haNew
  have hiso : ∀ u, ¬ (rounds[aNew]).2.Adj z u :=
    isolatedO_of_suffix hRa rounds[bOld] (rounds.drop (bOld + 1))
      (entry_suffix (j := aNew + 1) hbOld h2) z hgen
  obtain ⟨p, hplen, hpset, hne⟩ := pairO_walk h hbNew haNew h1
  rw [hpset] at hzNew
  have hlen0 : p.length ≠ 0 := fun h0 => hne (SimpleGraph.Walk.eq_of_length_eq_zero h0)
  obtain ⟨w, hw⟩ := exists_adj_of_mem_support p hlen0 hzNew
  exact hiso w hw

/-! ### No play lasts `N (2s + 2)` rounds -/

/-- **The extraction.** A play of `N (2·s + 2)` rounds cannot exist,
whatever the oracle. Connector's vertices are `N (2·s + 2)` distinct
vertices, so quasi-wideness returns a separator `S` of at most `s`
vertices and a distance-`r` independent set `B` of at least `2·s + 2` of
them. Pairing the selected rounds off chronologically gives `s + 1` pairs
whose maintained paths are pairwise disjoint, so one of them avoids `S`;
that path is a walk of length at most `r` between two distinct members of
`B` which survives the deletion of `S`, contradicting the
independence. -/
theorem no_full_survivalO {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B)
    (h : ReachedO O G rounds A) (hlen : rounds.length = N (2 * s + 2)) : False := by
  classical
  have hPcard : ({z | z ∈ rounds.map Prod.fst} : Set (Fin n)).ncard = rounds.length := by
    have hcoe : ({z | z ∈ rounds.map Prod.fst} : Set (Fin n))
        = ((rounds.map Prod.fst).toFinset : Set (Fin n)) := by ext z; simp
    rw [hcoe, Set.ncard_coe_finset, List.toFinset_card_of_nodup (picksO_nodup h),
      List.length_map]
  obtain ⟨S, B, hS, hBP, hBcard, hInd⟩ := hQ _ (by rw [hPcard, hlen])
  -- enumerate `2 * s + 2` selected rounds chronologically and pair them off
  obtain ⟨bi, ai, hbl, hal, hba, hcross, hbB, haB⟩ :
      ∃ bi ai : Fin (s + 1) → ℕ,
        ∃ hbl : ∀ t, bi t < rounds.length, ∃ hal : ∀ t, ai t < rounds.length,
          (∀ t, bi t < ai t) ∧ (∀ t t' : Fin (s + 1), t < t' → ai t < bi t') ∧
          (∀ t, (rounds[bi t]'(hbl t)).1 ∈ B) ∧ (∀ t, (rounds[ai t]'(hal t)).1 ∈ B) := by
    set I : Finset (Fin rounds.length) :=
      Finset.univ.filter (fun i => (rounds[(i : ℕ)]'i.isLt).1 ∈ B) with hI
    have hsub : B ⊆ (fun i : Fin rounds.length => (rounds[(i : ℕ)]'i.isLt).1) ''
        (I : Set (Fin rounds.length)) := by
      intro z hz
      obtain ⟨e, he, hez⟩ := List.mem_map.mp (hBP hz).1
      obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp he
      have hzi : (rounds[i]'hi).1 = z := by rw [hie]; exact hez
      refine ⟨⟨i, hi⟩, Finset.mem_coe.mpr ?_, hzi⟩
      rw [hI, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show (rounds[i]'hi).1 ∈ B
      rw [hzi]
      exact hz
    have hIcard : 2 * s + 2 ≤ I.card := by
      have h1 : B.ncard ≤ ((I : Set (Fin rounds.length))).ncard :=
        le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) (Set.ncard_image_le (Set.toFinite _))
      rw [Set.ncard_coe_finset] at h1
      omega
    obtain ⟨J, hJI, hJcard⟩ := Finset.exists_subset_card_eq hIcard
    have hmemB : ∀ k : Fin (2 * s + 2),
        (rounds[((J.orderEmbOfFin hJcard k : Fin rounds.length) : ℕ)]'
          (J.orderEmbOfFin hJcard k).isLt).1 ∈ B := by
      intro k
      have hk := hJI (J.orderEmbOfFin_mem hJcard k)
      rw [hI, Finset.mem_filter] at hk
      exact hk.2
    have hmono : ∀ k k' : Fin (2 * s + 2), k < k' →
        ((J.orderEmbOfFin hJcard k : Fin rounds.length) : ℕ) <
          ((J.orderEmbOfFin hJcard k' : Fin rounds.length) : ℕ) :=
      fun k k' hkk' => (J.orderEmbOfFin hJcard).strictMono hkk'
    refine ⟨fun t => ((J.orderEmbOfFin hJcard ⟨2 * (t : ℕ), by have := t.isLt; omega⟩ :
              Fin rounds.length) : ℕ),
            fun t => ((J.orderEmbOfFin hJcard ⟨2 * (t : ℕ) + 1, by have := t.isLt; omega⟩ :
              Fin rounds.length) : ℕ),
            fun t => Fin.isLt _, fun t => Fin.isLt _, fun t => ?_, fun t t' htt' => ?_,
            fun t => hmemB _, fun t => hmemB _⟩
    · exact hmono _ _ (by simp)
    · refine hmono _ _ ?_
      have : (t : ℕ) < (t' : ℕ) := htt'
      simp only [Fin.mk_lt_mk]
      omega
  -- distinct pairs' paths are disjoint, so one of them avoids `S`
  have hdisj : ∀ t t' : Fin (s + 1), t ≠ t' → ∀ z,
      z ∈ O.path (rounds[ai t]'(hal t)).2 (rounds[ai t]'(hal t)).1
            (rounds[bi t]'(hbl t)).1 →
      z ∈ O.path (rounds[ai t']'(hal t')).2 (rounds[ai t']'(hal t')).1
            (rounds[bi t']'(hbl t')).1 → False := by
    intro t t' hne z hz hz'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact pairO_disjoint h (hbl t) (hal t) (hbl t') (hal t') (hba t)
        (hcross t t' hlt) (hba t') hz' hz
    · exact pairO_disjoint h (hbl t') (hal t') (hbl t) (hal t) (hba t')
        (hcross t' t hlt) (hba t) hz hz'
  obtain ⟨t₀, ht₀⟩ := exists_avoiding hS
    (fun t => O.path (rounds[ai t]'(hal t)).2 (rounds[ai t]'(hal t)).1
      (rounds[bi t]'(hbl t)).1) hdisj
  -- that pair's path contradicts distance independence
  obtain ⟨p, hplen, hpset, hpne⟩ := pairO_walk h (hbl t₀) (hal t₀) (hba t₀)
  have hAle : (rounds[ai t₀]'(hal t₀)).2 ≤ G := reachedO_le (reachedO_entry h (hal t₀)).1
  have hsupp : ∀ z ∈ p.support, z ∉ S := fun z hz => ht₀ z (by rw [hpset]; exact hz)
  obtain ⟨q, hq⟩ := exists_walk_deleteVerts_of_le hAle p hsupp
  have hgt := distIndependent_iff.mp hInd (haB t₀) (hbB t₀) hpne q
  omega

/-! ### The main induction -/

/-- Splitter's oracle strategy wins, by downward induction on the
remaining round budget. From a reachable position with `b` rounds still
to play and `N (2·s + 2) − b` rounds played, Splitter wins within `b`
rounds: at budget zero the play would have lasted `N (2·s + 2)` rounds,
which `no_full_survivalO` excludes; with a round left, playing the
oracle's batch keeps the position reachable and playing an isolated
vertex ends the play at once. -/
theorem splitterWins_of_reachedO {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B) :
    ∀ (b : ℕ) (rounds : List (Round n)) (A : SimpleGraph (Fin n)),
      ReachedO O G rounds A → rounds.length + b = N (2 * s + 2) →
      SplitterWins (N (2 * s + 2) * (r + 1)) r b A := by
  intro b
  induction b with
  | zero =>
    intro rounds A hR hlen
    exact (no_full_survivalO hQ hR (by omega)).elim
  | succ b ih =>
    intro rounds A hR hlen
    rw [splitterWins_succ_iff]
    refine Or.inr fun v => ?_
    by_cases hv : ∃ u, A.Adj v u
    · exact ⟨batchO O rounds A v, batchO_subset_ball O rounds A v,
        batchO_ncard_le_of_lt O rounds A v (by omega),
        ih ((v, A) :: rounds) (nextArenaO O A v rounds) (ReachedO.step hR hv)
          (by simp only [List.length_cons]; omega)⟩
    · exact ⟨∅, Set.empty_subset _, by simp,
        splitterWins_of_eq_bot (eq_bot_of_isolated (fun z hz => hv ⟨z, hz⟩) ∅)⟩

/-! ### The driver-facing form

The three statements a program maintaining `ReachedO` needs: the
invariant is preserved by playing the oracle's batch, that batch is a
legal move, and the stack of played rounds is bounded.
-/

/-- **The descent step.** At a position reached with `b + 1` rounds of
the budget `ℓ` still to play, and at a vertex `v` that still carries an
edge, Splitter's batch is a legal move — inside the ball of the round and
of at most `ℓ · (r + 1)` vertices — and playing it lands on the position
reached by pushing `(v, A)` onto the history and moving to
`nextArenaO O A v rounds`. -/
theorem reachedO_descend {ℓ b : ℕ} {v : Fin n} (h : ReachedO O G rounds A)
    (hlen : rounds.length + b + 1 = ℓ) (hv : ∃ u, A.Adj v u) :
    ReachedO O G ((v, A) :: rounds) (nextArenaO O A v rounds) ∧
      batchO O rounds A v ⊆ ball A r v ∧
      (batchO O rounds A v).ncard ≤ ℓ * (r + 1) :=
  ⟨ReachedO.step h hv, batchO_subset_ball O rounds A v,
    batchO_ncard_le_of_lt O rounds A v (by omega)⟩

/-- **No play survives the round bound.** A history of `N (2·s + 2)`
rounds or more cannot be reached: its last `N (2·s + 2)` rounds would be
a full-length play, which `no_full_survivalO` excludes. -/
theorem reachedO_no_survival {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B)
    (h : ReachedO O G rounds A) (hlen : N (2 * s + 2) ≤ rounds.length) : False := by
  obtain ⟨B, hB⟩ := reachedO_suffix h (rounds.drop (rounds.length - N (2 * s + 2)))
    (List.drop_suffix _ _)
  exact no_full_survivalO hQ hB (by rw [List.length_drop]; omega)

/-- The termination measure of a driver maintaining `ReachedO`: the
history is always shorter than the round bound. -/
theorem reachedO_length_lt {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B)
    (h : ReachedO O G rounds A) : rounds.length < N (2 * s + 2) := by
  by_contra hcon
  exact reachedO_no_survival hQ h (by omega)

end Play

section Default

/-! ### The default oracle

`SplitterWin`'s strategy is the instance `defaultOracle`, and its
development is the special case of this one. Nothing below is used
elsewhere; it is the check that the generalization is faithful.
-/

variable {n r : ℕ} {G A : SimpleGraph (Fin n)} {rounds : List (Round n)}

/-- At the default oracle, `genSetO` is `SplitterWin.genSet`. -/
theorem genSetO_defaultOracle (rounds : List (Round n)) (v : Fin n) :
    genSetO (defaultOracle n r) rounds v = genSet r rounds v := by
  induction rounds with
  | nil => rfl
  | cons e rest ih => simp only [genSetO, genSet, defaultOracle_path, ih]

/-- At the default oracle, `batchO` is `SplitterWin.batch`. -/
theorem batchO_defaultOracle (rounds : List (Round n)) (A : SimpleGraph (Fin n))
    (v : Fin n) : batchO (defaultOracle n r) rounds A v = batch r rounds A v := by
  simp only [batchO, batch, genSetO_defaultOracle]

/-- At the default oracle, `nextArenaO` is `SplitterWin.nextArena`. -/
theorem nextArenaO_defaultOracle (A : SimpleGraph (Fin n)) (v : Fin n)
    (rounds : List (Round n)) :
    nextArenaO (defaultOracle n r) A v rounds = nextArena r A v rounds := by
  simp only [nextArenaO, nextArena, batchO_defaultOracle]

/-- A play of `SplitterWin`'s strategy is a play of the default oracle's
strategy. -/
theorem reachedO_defaultOracle (h : Reached r G rounds A) :
    ReachedO (defaultOracle n r) G rounds A := by
  induction h with
  | nil => exact ReachedO.nil
  | @step rounds A v _ hv ih =>
    rw [← nextArenaO_defaultOracle]
    exact ReachedO.step ih hv

/-- `SplitterWin.splitterWins_of_reached`, re-derived from the
parametric development at the default oracle. -/
theorem splitterWins_of_reached_default {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B) :
    ∀ (b : ℕ) (rounds : List (Round n)) (A : SimpleGraph (Fin n)),
      Reached r G rounds A → rounds.length + b = N (2 * s + 2) →
      SplitterWins (N (2 * s + 2) * (r + 1)) r b A :=
  fun b rounds A hR hlen =>
    splitterWins_of_reachedO (O := defaultOracle n r) hQ b rounds A
      (reachedO_defaultOracle hR) hlen

end Default

end Lax3Proofs.SplitterWinOracle
