import Lax3Proofs.SplitterWin

/-!
Splitter's win in the isolation splitter game when the short walks his
strategy maintains are **recorded** rather than computed: the
program-facing form of `Lax3Proofs.SplitterWin`.

# Why this file exists

`Lax3Proofs.SplitterWin` fixes Splitter's strategy once and for all with
`pathSet`, a `Classical.choice` walk of length at most `r` between two
vertices of one arena. The model-checking program cannot make that
choice: it computes its own shortest paths, by breadth-first search in
the arena it currently holds, and the walk it ends up with is whatever
its search found.

Nor can the program's walk be *named* by a function of the arena and the
two vertices, which is what an oracle interface would ask for. What the
machine leaves behind is pinned by `Lax3Proofs.RamBfsPaths.bfsPath_spec`
only up to `∃ p, p.length ≤ d ∧ bufSet n L Buf = {z | z ∈ p.support}` —
*some* walk of length at most the cap. Two independent solutions of that
existential may differ: in `C₄` at `r ≥ 2` the two antipodal vertices are
joined by two walks of length two, and which one comes back is decided by
the order of the block structure's rows on one side and by
`Classical.choice` on the other. So a game whose move at a round is a
*function* of the position cannot be the game the program plays.

It does not have to be. No proof of `SplitterWin` ever looks at *which*
walk `pathSet` returned; the whole development is deduced from the facts
that the isolated set contains, for every earlier connector, the support
of a genuine walk of length at most `r` to the new one, and that it is
small. So the game below **records** the isolated set as data of the
round and constrains it by exactly those facts.

# The recorded round

A `RoundR` is Connector's vertex, the arena it was played in, and a set
of vertices `gen` — the vertices Splitter *meant* to isolate. The round
isolates `batchR`, the part of `gen` inside the ball the round restricts
to; `ReachedR.step` asks of `gen` only that

* it contains Connector's own vertex, and
* for every earlier round `e` whose arena puts its connector within `r`
  of the new one, it contains the support of *some* walk of length at
  most `r` between them in that arena.

The second clause is *guarded*: an earlier connector the round's arena
does not reach within `r` contributes nothing. That costs the win
argument nothing, since a connector that still carries an edge lies in
the ball of every earlier round (`mem_ball_of_roundR`), so the pairs the
extraction actually uses always satisfy the guard. It is what lets the
program skip the walk back when its search did not reach the target.

No size clause is imposed on a recorded round: `no_full_survivalR`, the
extraction the driver consumes, never looks at the size of a batch, and
imposing one would oblige the program to prove a bound it does not need
there. The size *is* what makes a recorded round a legal move of the
game, and that is where it appears — `splitterWins_of_reachedR` bounds
the batches of the rounds it plays itself, and its continuation is
`SplitterWin`'s own `pathSet` strategy, which is where the recorded game
and the chosen one meet.

# What is here

`ReachedR` and the invariants (`isolatedR`, `selfR`,
`mem_ball_of_roundR`, `picksR_nodup`, `reachedR_entry`, `pairR_walk`,
`pairR_disjoint`), `no_full_survivalR` and `splitterWins_of_reachedR`
line up one for one with `SplitterWin`'s originals and are proved the
same way, with the round's own `gen`, `batchR` and `nextArenaR` in place
of `genSet`, `batch` and `nextArena`. Everything generic is imported
rather than repeated: the walk helpers, the `Iff.rfl` lemmas opening the
concept-side definitions, `eq_of_mem_ball_of_isolated`,
`eq_bot_of_isolated`, the list plumbing (`entry_suffix`,
`getElem_mem_drop`) and `exists_avoiding`.

Two simplifications come out of recording rather than computing. The
generating set of a round is on the round itself, so the invariants
quantify over `e ∈ rounds` where the originals quantified over suffixes
`e :: older <:+ rounds`; and `pairR_disjoint` takes the older pair's
vertex through `gen` directly, so nothing has to name the older pair's
walk twice.

# What the program phase takes from here

A driver whose per-level data is its current arena `A` together with the
stack `rounds` of the rounds already played maintains
`ReachedR r G rounds A` as its invariant:

* it starts at `rounds = []`, `A = G`, where the invariant is
  `ReachedR.nil`;
* at each level it reads Connector's vertex `v`, marks a set `W` inside
  the ball of the round which contains `v` and, for each earlier round
  its search reaches, the support of the walk that search found, and
  moves to the arena `W` isolates; `reachedR_descend` says in one step
  that this is a round of the recorded game — it produces the `gen` the
  round records, which is `W` together with the parts of those supports
  that ran out of the ball;
* if `v` has no incident edge in `A` the round is over anyway, since the
  arena it leaves is edgeless (`nextArenaR_eq_bot_of_isolated`);
* the recursion terminates: `reachedR_length_lt` bounds the stack by
  `N (2·s + 2)`, since by `reachedR_no_survival` no play reaches that
  length.

`splitterWins_of_reachedR` is the same statement in the game's own terms,
available at every position the driver passes through.

No tactic in this file is handed a concept-side definition, exactly as in
`SplitterWin`: `WithinDist` and `DistIndependent` are opened by that
file's `Iff.rfl` lemmas, `SplitterWins` and `deleteVerts` by the clause
lemmas of `Lax3Proofs.SplitterBasics`, and balls by
`Lax3Proofs.WalkDistance`.
-/

namespace Lax3Proofs.SplitterWinRec

open Lax3.ColoredGraphs Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax3Proofs.SplitterBasics Lax3Proofs.WalkDistance Lax3Proofs.SplitterWin

section Play

/-! ### Recorded rounds, batches and arenas -/

variable {n r : ℕ}

/-- One played round of the recorded game: the vertex Connector picked,
the arena it was picked in, and the set of vertices Splitter meant to
isolate. Histories are lists of rounds, newest first. -/
structure RoundR (n : ℕ) where
  /-- Connector's vertex. -/
  vtx : Fin n
  /-- The arena the round was played in. -/
  arena : SimpleGraph (Fin n)
  /-- The vertices Splitter meant to isolate. -/
  gen : Set (Fin n)

/-- What the round isolates: the part of its generating set inside the
ball it restricts to. -/
def batchR (r : ℕ) (e : RoundR n) : Set (Fin n) :=
  e.gen ∩ ball e.arena r e.vtx

/-- The batch is a legal move: it lies in the ball of the round. -/
theorem batchR_subset_ball (r : ℕ) (e : RoundR n) :
    batchR r e ⊆ ball e.arena r e.vtx := Set.inter_subset_right

/-- Membership in the batch is membership in the generating set and in
the ball. -/
theorem mem_batchR {e : RoundR n} {z : Fin n} (hg : z ∈ e.gen)
    (hb : z ∈ ball e.arena r e.vtx) : z ∈ batchR r e := ⟨hg, hb⟩

/-- The arena after a round: restrict to the ball around Connector's
vertex, then isolate what the round meant to isolate. -/
def nextArenaR (r : ℕ) (e : RoundR n) : SimpleGraph (Fin n) :=
  deleteVerts (deleteVerts e.arena (ball e.arena r e.vtx)ᶜ) (batchR r e)

/-- A round only removes edges. -/
theorem nextArenaR_le (r : ℕ) (e : RoundR n) : nextArenaR r e ≤ e.arena :=
  le_trans (deleteVerts_le _ _) (deleteVerts_le _ _)

/-- Every edge surviving a round has both ends in the ball the round
restricted to. -/
theorem mem_ball_of_nextArenaR_adj {e : RoundR n} {z w : Fin n}
    (h : (nextArenaR r e).Adj z w) : z ∈ ball e.arena r e.vtx :=
  not_not.mp (deleteVerts_adj.mp (deleteVerts_adj.mp h).1).2.1

/-- No edge surviving a round touches the batch. -/
theorem not_mem_batchR_of_nextArenaR_adj {e : RoundR n} {z w : Fin n}
    (h : (nextArenaR r e).Adj z w) : z ∉ batchR r e :=
  (deleteVerts_adj.mp h).2.1

/-- Playing an isolated vertex loses at once: whatever the round records,
the arena it leaves is edgeless, since the ball around such a vertex is a
single vertex. -/
theorem nextArenaR_eq_bot_of_isolated (r : ℕ) {e : RoundR n}
    (hv : ∀ z, ¬ e.arena.Adj e.vtx z) : nextArenaR r e = ⊥ :=
  eq_bot_of_isolated hv _

/-! ### Reachable positions -/

variable {G : SimpleGraph (Fin n)}

/-- The positions of a play from `G` in which every Connector move so far
was a vertex that still had an incident edge and every recorded
generating set is one Splitter's strategy could have meant: it contains
the round's own connector, and — for every earlier round whose arena puts
its connector within `r` of the new one — the support of a walk of length
at most `r` between them in that arena.

This is `SplitterWin.Reached` with the chosen walks replaced by recorded
ones; moves on isolated vertices are again not recorded, since they end
the play at once (`nextArenaR_eq_bot_of_isolated`). -/
inductive ReachedR (r : ℕ) (G : SimpleGraph (Fin n)) :
    List (RoundR n) → SimpleGraph (Fin n) → Prop
  | nil : ReachedR r G [] G
  | step {rounds : List (RoundR n)} {A : SimpleGraph (Fin n)} {v : Fin n} {S : Set (Fin n)}
      (h : ReachedR r G rounds A) (hv : ∃ u, A.Adj v u) (hself : v ∈ S)
      (hwalk : ∀ e ∈ rounds, WithinDist e.arena r e.vtx v →
        ∃ p : e.arena.Walk e.vtx v, p.length ≤ r ∧ {z | z ∈ p.support} ⊆ S) :
      ReachedR r G (⟨v, A, S⟩ :: rounds) (nextArenaR r ⟨v, A, S⟩)

variable {A : SimpleGraph (Fin n)} {rounds : List (RoundR n)}

/-- Inverting a played round: the arena an entry records is the position
its own older rounds reach, its vertex had an incident edge there, its
generating set is one the strategy could have meant, and the position
after it is the round's own next arena. -/
theorem reachedR_cons {v : Fin n} {A₀ : SimpleGraph (Fin n)} {S : Set (Fin n)}
    (h : ReachedR r G (⟨v, A₀, S⟩ :: rounds) A) :
    ReachedR r G rounds A₀ ∧ (∃ u, A₀.Adj v u) ∧ v ∈ S ∧
      (∀ e ∈ rounds, WithinDist e.arena r e.vtx v →
        ∃ p : e.arena.Walk e.vtx v, p.length ≤ r ∧ {z | z ∈ p.support} ⊆ S) ∧
      A = nextArenaR r ⟨v, A₀, S⟩ := by
  cases h with
  | step h hv hself hwalk => exact ⟨h, hv, hself, hwalk, rfl⟩

/-- Every reachable arena is a subgraph of the original: rounds only
delete edges. -/
theorem reachedR_le (h : ReachedR r G rounds A) : A ≤ G := by
  induction h with
  | nil => exact le_rfl
  | step _ _ _ _ ih => exact le_trans (nextArenaR_le ..) ih

/-- Every earlier stretch of a play is itself a play. -/
theorem reachedR_suffix (h : ReachedR r G rounds A) :
    ∀ t : List (RoundR n), t <:+ rounds → ∃ B, ReachedR r G t B := by
  induction h with
  | nil =>
    intro t ht
    rw [List.suffix_nil.mp ht]
    exact ⟨G, ReachedR.nil⟩
  | @step rounds A v S hh hv hself hwalk ih =>
    intro t ht
    rcases List.suffix_cons_iff.mp ht with rfl | ht'
    · exact ⟨_, ReachedR.step hh hv hself hwalk⟩
    · exact ih t ht'

/-- Every recorded round meant to isolate its own connector. -/
theorem selfR (h : ReachedR r G rounds A) : ∀ e ∈ rounds, e.vtx ∈ e.gen := by
  induction h with
  | nil => intro e he; exact absurd he (by simp)
  | @step rounds A v S hh hv hself hwalk ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact hself
    · exact ih e he'

/-- **Isolation is permanent.** Every vertex a played round meant to
isolate has no incident edge in any later arena: in the arena right after
the round it is either outside the ball the round restricted to or inside
the isolated batch, and later arenas only lose further edges. -/
theorem isolatedR (h : ReachedR r G rounds A) :
    ∀ e ∈ rounds, ∀ z ∈ e.gen, ∀ u, ¬ A.Adj z u := by
  induction h with
  | nil => intro e he; exact absurd he (by simp)
  | @step rounds A v S hh hv hself hwalk ih =>
    intro e he z hz u hadj
    rcases List.mem_cons.mp he with rfl | he'
    · exact not_mem_batchR_of_nextArenaR_adj hadj
        (mem_batchR hz (mem_ball_of_nextArenaR_adj hadj))
    · exact ih e he' z hz u (nextArenaR_le r _ hadj)

/-- A vertex that still carries an edge lies in the ball of every earlier
round: a round keeps only the edges inside that ball, and later rounds
keep fewer. -/
theorem mem_ball_of_roundR (h : ReachedR r G rounds A) :
    ∀ e ∈ rounds, ∀ z u, A.Adj z u → z ∈ ball e.arena r e.vtx := by
  induction h with
  | nil => intro e he; exact absurd he (by simp)
  | @step rounds A v S hh hv hself hwalk ih =>
    intro e he z u hadj
    rcases List.mem_cons.mp he with rfl | he'
    · exact mem_ball_of_nextArenaR_adj hadj
    · exact ih e he' z u (nextArenaR_le r _ hadj)

/-- Connector never repeats a vertex in a surviving play: an earlier
vertex is isolated from the round it was played on, while the current one
still carries an edge. -/
theorem picksR_nodup (h : ReachedR r G rounds A) : (rounds.map RoundR.vtx).Nodup := by
  induction h with
  | nil => simp
  | @step rounds A v S hh hv hself hwalk ih =>
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, ih⟩
    obtain ⟨e, he, hev⟩ := List.mem_map.mp hmem
    obtain ⟨u, hu⟩ := hv
    refine isolatedR hh e he e.vtx (selfR hh e he) u ?_
    show A.Adj e.vtx u
    rw [show e.vtx = v from hev]
    exact hu

/-! ### Pairs of rounds -/

/-- The position at the round with index `b`, together with the incident
edge its vertex still had there and the clause its generating set was
recorded under. -/
theorem reachedR_entry (h : ReachedR r G rounds A) {b : ℕ} (hb : b < rounds.length) :
    ReachedR r G (rounds.drop (b + 1)) (rounds[b]).arena ∧
      (∃ u, (rounds[b]).arena.Adj (rounds[b]).vtx u) ∧
      (∀ e ∈ rounds.drop (b + 1), WithinDist e.arena r e.vtx (rounds[b]).vtx →
        ∃ p : e.arena.Walk e.vtx (rounds[b]).vtx, p.length ≤ r ∧
          {z | z ∈ p.support} ⊆ (rounds[b]).gen) := by
  obtain ⟨B, hB⟩ := reachedR_suffix h (rounds.drop b) (List.drop_suffix b rounds)
  rw [List.drop_eq_getElem_cons hb] at hB
  obtain ⟨h1, h2, -, h4, -⟩ := reachedR_cons (v := (rounds[b]).vtx)
    (A₀ := (rounds[b]).arena) (S := (rounds[b]).gen) hB
  exact ⟨h1, h2, h4⟩

/-- The walk a pair of rounds recorded. The newer round's vertex still
had an edge, so it lies in the ball the older round restricted to — which
is the guard the newer round's clause is under — and the set the newer
round recorded therefore contains the support of a genuine walk of length
at most `r` in the older round's arena. Its endpoints are distinct: the
older vertex is already isolated when the newer round is played. -/
theorem pairR_walk (h : ReachedR r G rounds A) {b a : ℕ}
    (hb : b < rounds.length) (ha : a < rounds.length) (hba : b < a) :
    ∃ p : (rounds[a]).arena.Walk (rounds[a]).vtx (rounds[b]).vtx,
      p.length ≤ r ∧ {z | z ∈ p.support} ⊆ (rounds[b]).gen ∧
      (rounds[a]).vtx ≠ (rounds[b]).vtx := by
  obtain ⟨hRb, ⟨u, hu⟩, hwalkb⟩ := reachedR_entry h hb
  have hmem : rounds[a] ∈ rounds.drop (b + 1) := getElem_mem_drop (j := b + 1) ha hba
  have hball : (rounds[b]).vtx ∈ ball (rounds[a]).arena r (rounds[a]).vtx :=
    mem_ball_of_roundR hRb rounds[a] hmem _ u hu
  obtain ⟨p, hplen, hpsub⟩ := hwalkb rounds[a] hmem (mem_ball.mp hball)
  refine ⟨p, hplen, hpsub, fun hEq => ?_⟩
  refine isolatedR hRb rounds[a] hmem (rounds[a]).vtx (selfR hRb rounds[a] hmem) u ?_
  rw [hEq]
  exact hu

/-- **Distinct pairs' walks are disjoint.** A vertex an older round meant
to isolate has no edge in any arena from then on; but a walk recorded by
a pair of rounds strictly newer than it lives in a later arena and has
positive length, so each of its vertices does carry an edge.

The older pair enters only through the round that recorded it, so the
statement mentions three indices where the chosen strategy's needed
four. -/
theorem pairR_disjoint (h : ReachedR r G rounds A) {bNew aNew bOld : ℕ}
    (hbNew : bNew < rounds.length) (haNew : aNew < rounds.length)
    (hbOld : bOld < rounds.length) (hcross : aNew < bOld) {z : Fin n}
    (hzOld : z ∈ (rounds[bOld]).gen)
    {pNew : (rounds[aNew]).arena.Walk (rounds[aNew]).vtx (rounds[bNew]).vtx}
    (hne : (rounds[aNew]).vtx ≠ (rounds[bNew]).vtx) (hzNew : z ∈ pNew.support) :
    False := by
  obtain ⟨hRa, -, -⟩ := reachedR_entry h haNew
  have hiso : ∀ u, ¬ (rounds[aNew]).arena.Adj z u :=
    isolatedR hRa rounds[bOld] (getElem_mem_drop (j := aNew + 1) hbOld hcross) z hzOld
  have hlen0 : pNew.length ≠ 0 := fun h0 => hne (SimpleGraph.Walk.eq_of_length_eq_zero h0)
  obtain ⟨w, hw⟩ := exists_adj_of_mem_support pNew hlen0 hzNew
  exact hiso w hw

/-! ### No play lasts `N (2s + 2)` rounds -/

/-- **The extraction.** A play of `N (2·s + 2)` recorded rounds cannot
exist. Connector's vertices are `N (2·s + 2)` distinct vertices, so
quasi-wideness returns a separator `S` of at most `s` vertices and a
distance-`r` independent set `B` of at least `2·s + 2` of them. Pairing
the selected rounds off chronologically gives `s + 1` pairs whose
recorded walks are pairwise disjoint, so one of them avoids `S`; that
walk has length at most `r`, runs between two distinct members of `B` and
survives the deletion of `S`, contradicting the independence.

Nothing here looks at how large a batch is, which is why `ReachedR`
imposes no bound on one. -/
theorem no_full_survivalR {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B)
    (h : ReachedR r G rounds A) (hlen : rounds.length = N (2 * s + 2)) : False := by
  classical
  have hPcard : ({z | z ∈ rounds.map RoundR.vtx} : Set (Fin n)).ncard = rounds.length := by
    have hcoe : ({z | z ∈ rounds.map RoundR.vtx} : Set (Fin n))
        = ((rounds.map RoundR.vtx).toFinset : Set (Fin n)) := by ext z; simp
    rw [hcoe, Set.ncard_coe_finset, List.toFinset_card_of_nodup (picksR_nodup h),
      List.length_map]
  obtain ⟨S, B, hS, hBP, hBcard, hInd⟩ := hQ _ (by rw [hPcard, hlen])
  -- enumerate `2 * s + 2` selected rounds chronologically and pair them off
  obtain ⟨bi, ai, hbl, hal, hba, hcross, hbB, haB⟩ :
      ∃ bi ai : Fin (s + 1) → ℕ,
        ∃ hbl : ∀ t, bi t < rounds.length, ∃ hal : ∀ t, ai t < rounds.length,
          (∀ t, bi t < ai t) ∧ (∀ t t' : Fin (s + 1), t < t' → ai t < bi t') ∧
          (∀ t, (rounds[bi t]'(hbl t)).vtx ∈ B) ∧ (∀ t, (rounds[ai t]'(hal t)).vtx ∈ B) := by
    set I : Finset (Fin rounds.length) :=
      Finset.univ.filter (fun i => (rounds[(i : ℕ)]'i.isLt).vtx ∈ B) with hI
    have hsub : B ⊆ (fun i : Fin rounds.length => (rounds[(i : ℕ)]'i.isLt).vtx) ''
        (I : Set (Fin rounds.length)) := by
      intro z hz
      obtain ⟨e, he, hez⟩ := List.mem_map.mp (hBP hz).1
      obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp he
      have hzi : (rounds[i]'hi).vtx = z := by rw [hie]; exact hez
      refine ⟨⟨i, hi⟩, Finset.mem_coe.mpr ?_, hzi⟩
      rw [hI, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show (rounds[i]'hi).vtx ∈ B
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
          (J.orderEmbOfFin hJcard k).isLt).vtx ∈ B := by
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
  -- name the walk each pair recorded
  choose p hplen hpsub hpne using fun t : Fin (s + 1) => pairR_walk h (hbl t) (hal t) (hba t)
  -- distinct pairs' walks are disjoint, so one of them avoids `S`
  have hdisj : ∀ t t' : Fin (s + 1), t ≠ t' → ∀ z,
      z ∈ {z | z ∈ (p t).support} → z ∈ {z | z ∈ (p t').support} → False := by
    intro t t' hne z hz hz'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact pairR_disjoint h (hbl t) (hal t) (hbl t') (hcross t t' hlt)
        (hpsub t' hz') (hpne t) hz
    · exact pairR_disjoint h (hbl t') (hal t') (hbl t) (hcross t' t hlt)
        (hpsub t hz) (hpne t') hz'
  obtain ⟨t₀, ht₀⟩ := exists_avoiding hS (fun t => {z | z ∈ (p t).support}) hdisj
  -- that pair's walk contradicts distance independence
  have hAle : (rounds[ai t₀]'(hal t₀)).arena ≤ G := reachedR_le (reachedR_entry h (hal t₀)).1
  have hsupp : ∀ z ∈ (p t₀).support, z ∉ S := fun z hz => ht₀ z hz
  obtain ⟨q, hq⟩ := exists_walk_deleteVerts_of_le hAle (p t₀) hsupp
  have hgt := distIndependent_iff.mp hInd (haB t₀) (hbB t₀) (hpne t₀) q
  have hlt := hplen t₀
  omega

/-! ### The main induction -/

/-- Splitter wins from every recorded position, by downward induction on
the remaining round budget. From a reachable position with `b` rounds
still to play and `N (2·s + 2) − b` rounds recorded, Splitter wins within
`b` rounds: at budget zero the play would have `N (2·s + 2)` recorded
rounds, which `no_full_survivalR` excludes; with a round left, Splitter
plays `SplitterWin`'s own chosen batch — a legal recorded round, and the
one place a *choice* of walks is needed — and playing an isolated vertex
ends the play at once.

The continuation is `SplitterWin.genSet` at the recorded history read as
a list of `SplitterWin.Round`s, which is where the size of a batch is
paid for: one vertex plus one chosen walk of at most `r + 1` vertices per
recorded round. -/
theorem splitterWins_of_reachedR {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B) :
    ∀ (b : ℕ) (rounds : List (RoundR n)) (A : SimpleGraph (Fin n)),
      ReachedR r G rounds A → rounds.length + b = N (2 * s + 2) →
      SplitterWins (N (2 * s + 2) * (r + 1)) r b A := by
  intro b
  induction b with
  | zero =>
    intro rounds A hR hlen
    exact (no_full_survivalR hQ hR (by omega)).elim
  | succ b ih =>
    intro rounds A hR hlen
    rw [splitterWins_succ_iff]
    refine Or.inr fun v => ?_
    by_cases hv : ∃ u, A.Adj v u
    · -- the chosen batch of `SplitterWin`, recorded
      classical
      set l : List (Round n) := rounds.map (fun e => (e.vtx, e.arena)) with hl
      set S : Set (Fin n) := genSet r l v with hS
      have hwalk : ∀ e ∈ rounds, WithinDist e.arena r e.vtx v →
          ∃ p : e.arena.Walk e.vtx v, p.length ≤ r ∧ {z | z ∈ p.support} ⊆ S := by
        intro e he hwd
        obtain ⟨p, hplen, hpset⟩ := pathSet_spec hwd
        refine ⟨p, hplen, ?_⟩
        rw [← hpset]
        exact pathSet_subset_genSet (e := (e.vtx, e.arena))
          (List.mem_map_of_mem (f := fun e : RoundR n => (e.vtx, e.arena)) he) v
      have hcard : (batchR r ⟨v, A, S⟩).ncard ≤ N (2 * s + 2) * (r + 1) := by
        have h1 : (batchR r ⟨v, A, S⟩).ncard ≤ (genSet r l v).ncard :=
          Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
        have h2 := genSet_ncard_le r l v
        have h3 : l.length = rounds.length := by rw [hl, List.length_map]
        have h4 : (rounds.length + 1) * (r + 1) ≤ N (2 * s + 2) * (r + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have h5 : (rounds.length + 1) * (r + 1) = rounds.length * (r + 1) + (r + 1) :=
          Nat.succ_mul _ _
        rw [h3] at h2
        omega
      exact ⟨batchR r ⟨v, A, S⟩, batchR_subset_ball r _, hcard,
        ih (⟨v, A, S⟩ :: rounds) (nextArenaR r ⟨v, A, S⟩)
          (ReachedR.step hR hv (self_mem_genSet r l v) hwalk)
          (by simp only [List.length_cons]; omega)⟩
    · exact ⟨∅, Set.empty_subset _, by simp,
        splitterWins_of_eq_bot (eq_bot_of_isolated (fun z hz => hv ⟨z, hz⟩) ∅)⟩

/-! ### The driver-facing form

The three statements a program maintaining `ReachedR` needs: what a round
of the recorded game costs it, that the stack of played rounds is
bounded, and the measure that bound is.
-/

/-- **The descent step.** At a position reached with an edge still at the
connector `v`, a set `W` inside the ball of the round which contains `v`
and, for every earlier round the arena connects to `v`, the part of some
short walk's support that stays inside the ball, is the batch of a
recorded round: the round records `W` together with the parts of those
supports that ran out of the ball, and isolates exactly `W`.

This is the whole interface of the game to the program. The program owes
no equation between the walk it found and any other walk — only that the
support of the one it found is inside `W` where the ball keeps it. -/
theorem reachedR_descend {v : Fin n} {W : Set (Fin n)} (h : ReachedR r G rounds A)
    (hv : ∃ u, A.Adj v u) (hWball : W ⊆ ball A r v) (hself : v ∈ W)
    (hwalk : ∀ e ∈ rounds, WithinDist e.arena r e.vtx v →
      ∃ p : e.arena.Walk e.vtx v, p.length ≤ r ∧
        {z | z ∈ p.support} ∩ ball A r v ⊆ W) :
    ∃ S : Set (Fin n),
      ReachedR r G (⟨v, A, S⟩ :: rounds) (deleteVerts (deleteVerts A (ball A r v)ᶜ) W) := by
  classical
  set S : Set (Fin n) := W ∪ {z | ∃ e ∈ rounds, ∃ p : e.arena.Walk e.vtx v, p.length ≤ r ∧
      ({w | w ∈ p.support} ∩ ball A r v ⊆ W) ∧ z ∈ p.support} with hS
  have hbatch : batchR r ⟨v, A, S⟩ = W := by
    refine Set.eq_of_subset_of_subset (fun z hz => ?_) (fun z hz => ⟨Or.inl hz, hWball hz⟩)
    obtain ⟨hzg, hzb⟩ := hz
    rcases hzg with hzW | ⟨e, -, p, -, hpsub, hzp⟩
    · exact hzW
    · exact hpsub ⟨hzp, hzb⟩
  have hstep : ReachedR r G (⟨v, A, S⟩ :: rounds) (nextArenaR r ⟨v, A, S⟩) :=
    ReachedR.step h hv (Or.inl hself)
      (fun e he hwd => by
        obtain ⟨p, hplen, hpsub⟩ := hwalk e he hwd
        exact ⟨p, hplen, fun z hz => Or.inr ⟨e, he, p, hplen, hpsub, hz⟩⟩)
  refine ⟨S, ?_⟩
  rwa [nextArenaR, hbatch] at hstep

/-- **No play survives the round bound.** A history of `N (2·s + 2)`
recorded rounds or more cannot be reached: its last `N (2·s + 2)` rounds
would be a full-length play, which `no_full_survivalR` excludes. -/
theorem reachedR_no_survival {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B)
    (h : ReachedR r G rounds A) (hlen : N (2 * s + 2) ≤ rounds.length) : False := by
  obtain ⟨B, hB⟩ := reachedR_suffix h (rounds.drop (rounds.length - N (2 * s + 2)))
    (List.drop_suffix _ _)
  exact no_full_survivalR hQ hB (by rw [List.length_drop]; omega)

/-- The termination measure of a driver maintaining `ReachedR`: the
history is always shorter than the round bound. -/
theorem reachedR_length_lt {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B)
    (h : ReachedR r G rounds A) : rounds.length < N (2 * s + 2) := by
  by_contra hcon
  exact reachedR_no_survival hQ h (by omega)

end Play

/-! ### The worked example

A recorded round is *data*, so the one thing a reader cannot check by
staring at `ReachedR` is whether its clauses can all be met at once — a
game no play can enter would make `no_full_survivalR` vacuous and the
driver's descent unprovable. These are the instances that say they can.

The arena is the triangle on `Fin 3` and the radius is `2`. Round one is
played at `0`, round two at `1`, and round two's walk clause is *not*
vacuous: the guard `WithinDist ⊤ 2 0 1` holds, so the round really has to
record the support `{0, 1}` of a walk.

The last example is the shape the program produces. At round two the
machine marks `W = {1}` alone: the walk it found from the ancestor `0`
has support `{0, 1}`, but `0` carries no edge in the round's arena — it
was isolated when round one was played — so `0` is outside the ball and
the `andCom` with the ball drops it. `reachedR_descend` still produces a
recorded round, which is the clause weakening the whole repair turns on.
-/

namespace Demo

open Lax3Proofs.SplitterWin (exists_adj_of_mem_support)

/-- Depth zero is a position at every carrier and every radius,
including the empty one, where no round can ever be played. -/
example (n r : ℕ) (G : SimpleGraph (Fin n)) : ReachedR r G [] G := .nil

/-- The single-edge walk `0 — 1` of the triangle. -/
def w01 : (⊤ : SimpleGraph (Fin 3)).Walk 0 1 := SimpleGraph.Walk.cons (by decide) .nil

theorem w01_support : ∀ z : Fin 3, z ∈ w01.support ↔ (z = 0 ∨ z = 1) := by decide

/-- `1` is inside the radius-`2` ball of `0` in the triangle. -/
theorem one_mem_ball : (1 : Fin 3) ∈ ball (⊤ : SimpleGraph (Fin 3)) 2 0 :=
  mem_ball.mpr ⟨w01, by decide⟩

/-- `2` is inside the radius-`2` ball of `0` in the triangle. -/
theorem two_mem_ball : (2 : Fin 3) ∈ ball (⊤ : SimpleGraph (Fin 3)) 2 0 :=
  mem_ball.mpr ⟨SimpleGraph.Walk.cons (by decide) .nil, by decide⟩

/-- Round one: connector `0`, generating set `{0}`. -/
def rd1 : RoundR 3 := ⟨0, ⊤, {0}⟩

theorem reached1 : ReachedR 2 (⊤ : SimpleGraph (Fin 3)) [rd1] (nextArenaR 2 rd1) :=
  .step .nil ⟨1, by decide⟩ rfl (by simp)

/-- The edge `1 — 2` survives round one: both ends are in the ball and
neither is the isolated `0`. -/
theorem arena1_adj : (nextArenaR 2 rd1).Adj 1 2 :=
  deleteVerts_adj.mpr
    ⟨deleteVerts_adj.mpr
      ⟨show (⊤ : SimpleGraph (Fin 3)).Adj 1 2 from by decide,
        fun h => h one_mem_ball, fun h => h two_mem_ball⟩,
      fun h => absurd (show (1 : Fin 3) = 0 from h.1) (by decide),
      fun h => absurd (show (2 : Fin 3) = 0 from h.1) (by decide)⟩

/-- Round two: connector `1`, generating set `{0, 1}` — the support of
the walk round two's clause demands. -/
def rd2 : RoundR 3 := ⟨1, nextArenaR 2 rd1, {0, 1}⟩

/-- Two rounds, the second with a walk clause that bites. -/
theorem reached2 :
    ReachedR 2 (⊤ : SimpleGraph (Fin 3)) [rd2, rd1] (nextArenaR 2 rd2) := by
  refine .step reached1 ⟨2, arena1_adj⟩ (by simp) ?_
  intro e he _
  rw [List.mem_singleton] at he
  subst he
  exact ⟨w01, by decide, fun z hz => by rcases (w01_support z).mp hz with rfl | rfl <;> simp⟩

/-- Round one isolated `0` for good. -/
theorem zero_isolated1 : ∀ z, ¬ (nextArenaR 2 rd1).Adj z 0 := fun _ hz =>
  (deleteVerts_adj.mp hz).2.2
    ⟨rfl, not_not.mp (deleteVerts_adj.mp (deleteVerts_adj.mp hz).1).2.2⟩

/-- So `0` is outside the ball of round two, and the machine's `andCom`
drops it from the batch. -/
theorem zero_not_mem_ball1 : (0 : Fin 3) ∉ ball (nextArenaR 2 rd1) 2 1 := by
  intro h
  obtain ⟨p, -⟩ := mem_ball.mp h
  have hlen : p.length ≠ 0 := fun h0 =>
    absurd (SimpleGraph.Walk.eq_of_length_eq_zero h0) (by decide)
  obtain ⟨z, hz⟩ := exists_adj_of_mem_support p hlen p.end_mem_support
  exact zero_isolated1 z hz.symm

/-- The program's round two: it marks the connector alone, and the walk
clause is met because the part of the walk it dropped is the part the
ball dropped. -/
example : ∃ S : Set (Fin 3), ReachedR 2 (⊤ : SimpleGraph (Fin 3))
    [⟨1, nextArenaR 2 rd1, S⟩, rd1]
    (deleteVerts (deleteVerts (nextArenaR 2 rd1)
      (ball (nextArenaR 2 rd1) 2 1)ᶜ) {1}) := by
  refine reachedR_descend reached1 ⟨2, arena1_adj⟩ ?_ rfl ?_
  · intro z hz
    rw [show z = 1 from hz]
    exact mem_ball_self _ _ _
  · intro e he _
    rw [List.mem_singleton] at he
    subst he
    refine ⟨w01, by decide, ?_⟩
    rintro z ⟨hz1, hz2⟩
    rcases (w01_support z).mp hz1 with rfl | rfl
    · exact absurd hz2 zero_not_mem_ball1
    · rfl

end Demo

end Lax3Proofs.SplitterWinRec
