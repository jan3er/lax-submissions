import Lax3.NowhereDenseSplitter
import Lax12.NowhereDenseUQW
import Lax3Proofs.SplitterBasics
import Lax3Proofs.WalkDistance
import Mathlib.Data.Finset.Sort

/-!
Splitter wins the isolation splitter game on every member of a nowhere
dense class — the discharge of
`Lax3.NowhereDenseSplitter.splitterWins_of_nowhereDense`, Lemma 4.2 of
Chapter 4 of the source lecture notes (Theorem 4.2 of
Grohe–Kreutzer–Siebertz) transposed to the isolation variant.

Everything is driven by the quasi-wideness margins of the class at the
game radius `r`, taken from Lax12's endorsed
`uniformlyQuasiWide_of_nowhereDense`: a threshold function `N` and a
separator bound `s`. The bounds are `ℓ = N (2·s + 2)` rounds and
`m = ℓ · (r + 1)` vertices per batch.

# The strategy

Splitter maintains, towards every vertex Connector has played, a walk of
length at most `r` — chosen once and for all by `pathSet`, in the arena
that earlier round was played in — and in each round isolates the
vertices of those walks that are still in the current ball, together with
Connector's new vertex (`genSet`, cut down to the ball by `batch`). That
is one vertex plus one path of at most `r + 1` vertices per round played,
so at most `m` after fewer than `ℓ` rounds.

A play is a list of rounds, newest first, each recording Connector's
vertex together with the arena it was picked in; `Reached` collects the
positions of the plays in which every Connector move still had an
incident edge. Moves on isolated vertices need no history: the ball
around such a vertex is the vertex alone, so the round leaves an edgeless
arena and Splitter has already won (`eq_bot_of_isolated`).

# Why no play lasts `ℓ` rounds

This is `no_full_survival`, the heart of the file. After `ℓ` rounds
Connector has played `ℓ` distinct vertices (`picks_nodup`), so
quasi-wideness returns a separator `S` with at most `s` vertices and a
distance-`r` independent set `B` of at least `2·s + 2` of them. Pairing
the rounds that selected a vertex of `B` off chronologically gives
`s + 1` pairs, each with the strategy's walk between its two vertices,
inside the older round's arena (`pair_walk`).

Two ingredients replace the notes' "removed vertices are gone", which the
isolation variant cannot use.

* *Isolation is permanent* (`isolated_of_suffix`): arenas only ever lose
  edges, so a vertex the strategy isolated in some round has no incident
  edge in any later arena — either it left the ball the round restricted
  to, or it was in the batch, and both are forever.
* *Distinct pairs' walks are disjoint* (`pair_disjoint`): a vertex on an
  older pair's walk belongs to the batch-generating set of that pair's
  newer round, hence is isolated from then on; but every vertex of a
  newer pair's walk carries an edge in an arena strictly after that
  round, because the walk is not trivial — its endpoints are distinct,
  the older one being already isolated where the newer one still had an
  edge.

So the `s + 1` walks are pairwise disjoint and, `S` having at most `s`
vertices, one of them avoids `S` (`exists_avoiding`). Rebuilt inside
`deleteVerts G S` — a single induction on the walk, since the arena is a
subgraph of `G` and the walk avoids `S` — it is a walk of length at most
`r` between two distinct members of `B`, which is exactly what
`DistIndependent (deleteVerts G S) r B` forbids.

# The round bound

The notes state `ℓ = N (2·s + 1)`, but their own proof extracts `s + 1`
pairwise disjoint paths so that one avoids the separator, and that needs
`2·s + 2` selected rounds. The `+ 2` form is taken here, as the
formalization notes of `Lax3.NowhereDenseSplitter` record; nothing else
about the notes' argument changes.

No tactic in this file is handed a concept-side definition: `WithinDist`
and `DistIndependent` are opened by the `Iff.rfl` lemmas of the first
section, `SplitterWins` and `deleteVerts` by the clause lemmas of
`Lax3Proofs.SplitterBasics`, and balls by `Lax3Proofs.WalkDistance`.
-/

namespace Lax3Proofs.SplitterWin

open Lax3.ColoredGraphs Lax3.SplitterGame
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.UniformQuasiWideness
open Lax3Proofs.SplitterBasics Lax3Proofs.WalkDistance

section Generic

/-! ### Unfolding the concept-side definitions -/

variable {V : Type*} {G G' : SimpleGraph V} {S : Set V} {u v x y : V} {d r : ℕ}

/-- The walk bound `WithinDist` is defined by, as an `Iff`. -/
theorem withinDist_iff : WithinDist G d u v ↔ ∃ w : G.Walk u v, w.length ≤ d := Iff.rfl

/-- Distance independence is a pairwise condition on walks, as an
`Iff`. -/
theorem distIndependent_iff {A : Set V} :
    DistIndependent G r A ↔ A.Pairwise fun u v => ∀ p : G.Walk u v, r < p.length := Iff.rfl

/-! ### Walk helpers -/

/-- A walk of positive length leaves an edge at its starting point. -/
theorem exists_adj_of_length_ne_zero (p : G.Walk u v) (hp : p.length ≠ 0) :
    ∃ z, G.Adj u z := by
  cases p with
  | nil => simp at hp
  | cons h _ => exact ⟨_, h⟩

/-- Every vertex on a walk of positive length carries an edge of the
graph the walk lives in. -/
theorem exists_adj_of_mem_support (p : G.Walk u v) (hp : p.length ≠ 0)
    (hx : x ∈ p.support) : ∃ z, G.Adj x z := by
  classical
  have hspec := p.take_spec hx
  have hlen : (p.takeUntil x hx).length + (p.dropUntil x hx).length = p.length := by
    rw [← SimpleGraph.Walk.length_append, hspec]
  rcases Nat.eq_zero_or_pos (p.dropUntil x hx).length with h0 | hpos
  · refine exists_adj_of_length_ne_zero (p.takeUntil x hx).reverse ?_
    rw [SimpleGraph.Walk.length_reverse]
    omega
  · exact exists_adj_of_length_ne_zero (p.dropUntil x hx) (by omega)

/-- A walk of a subgraph whose support avoids `S` survives the isolation
of `S` in the ambient graph, at the same length. -/
theorem exists_walk_deleteVerts_of_le (hG : G ≤ G') (p : G.Walk u v)
    (hp : ∀ z ∈ p.support, z ∉ S) :
    ∃ q : (deleteVerts G' S).Walk u v, q.length = p.length := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons a b c hab p ih =>
    obtain ⟨q, hq⟩ := ih fun z hz => hp z (by simp [hz])
    exact ⟨SimpleGraph.Walk.cons ⟨hG hab, hp a (by simp), hp b (by simp)⟩ q, by simp [hq]⟩

/-- The ball around an isolated vertex is that vertex alone. -/
theorem eq_of_mem_ball_of_isolated (hv : ∀ z, ¬ G.Adj v z) (hx : x ∈ ball G r v) :
    x = v := by
  obtain ⟨w, -⟩ := withinDist_iff.mp (mem_ball.mp hx)
  cases w with
  | nil => rfl
  | cons h _ => exact absurd h (hv _)

/-! ### The strategy's chosen paths -/

open Classical in
/-- A chosen short walk from `u` to `v`, as the set of its vertices: the
support of some walk of length at most `r` if there is one, and the empty
set otherwise. This is the path the strategy maintains towards an earlier
Connector vertex. -/
noncomputable def pathSet (G : SimpleGraph V) (r : ℕ) (u v : V) : Set V :=
  if h : WithinDist G r u v then {z | z ∈ (withinDist_iff.mp h).choose.support} else ∅

/-- The chosen path is the support of a genuine walk of length at most
`r` whenever there is one. -/
theorem pathSet_spec (h : WithinDist G r u v) :
    ∃ p : G.Walk u v, p.length ≤ r ∧ pathSet G r u v = {z | z ∈ p.support} := by
  classical
  exact ⟨(withinDist_iff.mp h).choose, (withinDist_iff.mp h).choose_spec,
    by simp only [pathSet, dif_pos h]⟩

/-- The chosen path has at most `r + 1` vertices. -/
theorem pathSet_ncard_le (G : SimpleGraph V) (r : ℕ) (u v : V) :
    (pathSet G r u v).ncard ≤ r + 1 := by
  classical
  by_cases h : WithinDist G r u v
  · obtain ⟨p, hp, hset⟩ := pathSet_spec h
    have hcoe : {z | z ∈ p.support} = (p.support.toFinset : Set V) := by ext z; simp
    rw [hset, hcoe, Set.ncard_coe_finset]
    calc p.support.toFinset.card ≤ p.support.length := List.toFinset_card_le _
      _ = p.length + 1 := p.length_support
      _ ≤ r + 1 := by omega
  · have : pathSet G r u v = ∅ := by simp only [pathSet, dif_neg h]
    simp [this]

end Generic

section Play

/-! ### Histories, batches and arenas -/

/-- One played round: the vertex Connector picked together with the arena
it was picked in. Histories are lists of rounds, newest first. -/
abbrev Round (n : ℕ) : Type := Fin n × SimpleGraph (Fin n)

variable {n : ℕ}

/-- The vertices Splitter wants to isolate when Connector plays `v`: `v`
itself together with the chosen paths from every earlier Connector vertex
to `v`, each taken in the arena that round was played in. -/
noncomputable def genSet (r : ℕ) : List (Round n) → Fin n → Set (Fin n)
  | [], v => {v}
  | e :: rest, v => pathSet e.2 r e.1 v ∪ genSet r rest v

/-- Connector's new vertex is among the vertices the strategy isolates. -/
theorem self_mem_genSet (r : ℕ) (rounds : List (Round n)) (v : Fin n) :
    v ∈ genSet r rounds v := by
  induction rounds with
  | nil => simp only [genSet]; exact rfl
  | cons e rest ih => simp only [genSet]; exact Or.inr ih

/-- The chosen path from an earlier round's vertex is among the vertices
the strategy isolates. -/
theorem pathSet_subset_genSet {r : ℕ} {rounds : List (Round n)} {e : Round n}
    (he : e ∈ rounds) (v : Fin n) : pathSet e.2 r e.1 v ⊆ genSet r rounds v := by
  induction rounds with
  | nil => exact absurd he (by simp)
  | cons e' rest ih =>
    simp only [genSet]
    rcases List.mem_cons.mp he with rfl | h
    · exact Set.subset_union_left
    · exact fun z hz => Or.inr (ih h hz)

/-- One vertex plus one path of at most `r + 1` vertices per earlier
round. -/
theorem genSet_ncard_le (r : ℕ) (rounds : List (Round n)) (v : Fin n) :
    (genSet r rounds v).ncard ≤ 1 + rounds.length * (r + 1) := by
  induction rounds with
  | nil => simp only [genSet, Set.ncard_singleton, List.length_nil]; omega
  | cons e rest ih =>
    have h1 : (genSet r (e :: rest) v).ncard
        ≤ (pathSet e.2 r e.1 v).ncard + (genSet r rest v).ncard := by
      simp only [genSet]; exact Set.ncard_union_le _ _
    have h2 := pathSet_ncard_le e.2 r e.1 v
    have h3 : (rest.length + 1) * (r + 1) = rest.length * (r + 1) + (r + 1) :=
      Nat.succ_mul _ _
    simp only [List.length_cons]
    omega

/-- Splitter's batch after the history `rounds` when Connector plays `v`
in the arena `A`: the vertices of `genSet` that are still in the ball the
round restricts to. -/
noncomputable def batch (r : ℕ) (rounds : List (Round n)) (A : SimpleGraph (Fin n))
    (v : Fin n) : Set (Fin n) :=
  genSet r rounds v ∩ ball A r v

/-- The batch is a legal move: it lies in the ball of the round. -/
theorem batch_subset_ball (r : ℕ) (rounds : List (Round n)) (A : SimpleGraph (Fin n))
    (v : Fin n) : batch r rounds A v ⊆ ball A r v :=
  Set.inter_subset_right

/-- Membership in the batch is membership in `genSet` and in the ball. -/
theorem mem_batch {r : ℕ} {rounds : List (Round n)} {A : SimpleGraph (Fin n)}
    {v z : Fin n} (hg : z ∈ genSet r rounds v) (hb : z ∈ ball A r v) :
    z ∈ batch r rounds A v := ⟨hg, hb⟩

/-- The batch is bounded by one vertex per round and one path per round. -/
theorem batch_ncard_le (r : ℕ) (rounds : List (Round n)) (A : SimpleGraph (Fin n))
    (v : Fin n) : (batch r rounds A v).ncard ≤ 1 + rounds.length * (r + 1) :=
  le_trans (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _))
    (genSet_ncard_le r rounds v)

/-- The arena after a round: restrict `A` to the ball around Connector's
vertex `v`, then isolate Splitter's batch. -/
noncomputable def nextArena (r : ℕ) (A : SimpleGraph (Fin n)) (v : Fin n)
    (rounds : List (Round n)) : SimpleGraph (Fin n) :=
  deleteVerts (deleteVerts A (ball A r v)ᶜ) (batch r rounds A v)

/-- A round only removes edges. -/
theorem nextArena_le (r : ℕ) (A : SimpleGraph (Fin n)) (v : Fin n)
    (rounds : List (Round n)) : nextArena r A v rounds ≤ A :=
  le_trans (deleteVerts_le _ _) (deleteVerts_le _ _)

/-- Every edge surviving a round has both ends in the ball the round
restricted to. -/
theorem mem_ball_of_nextArena_adj {r : ℕ} {A : SimpleGraph (Fin n)} {v z w : Fin n}
    {rounds : List (Round n)} (h : (nextArena r A v rounds).Adj z w) :
    z ∈ ball A r v :=
  not_not.mp (deleteVerts_adj.mp (deleteVerts_adj.mp h).1).2.1

/-- No edge surviving a round touches the batch. -/
theorem not_mem_batch_of_nextArena_adj {r : ℕ} {A : SimpleGraph (Fin n)} {v z w : Fin n}
    {rounds : List (Round n)} (h : (nextArena r A v rounds).Adj z w) :
    z ∉ batch r rounds A v :=
  (deleteVerts_adj.mp h).2.1

/-- Playing an isolated vertex loses at once: its ball is a single
vertex, so the arena the round leaves is edgeless whatever Splitter
plays. -/
theorem eq_bot_of_isolated {r : ℕ} {A : SimpleGraph (Fin n)} {v : Fin n}
    (hv : ∀ z, ¬ A.Adj v z) (W : Set (Fin n)) :
    deleteVerts (deleteVerts A (ball A r v)ᶜ) W = ⊥ := by
  ext z w
  simp only [SimpleGraph.bot_adj, iff_false]
  intro hzw
  have h1 := (deleteVerts_adj.mp hzw).1
  have hz : z = v :=
    eq_of_mem_ball_of_isolated hv (not_not.mp (deleteVerts_adj.mp h1).2.1)
  have hw : w = v :=
    eq_of_mem_ball_of_isolated hv (not_not.mp (deleteVerts_adj.mp h1).2.2)
  subst hz
  subst hw
  exact hv _ (deleteVerts_adj.mp h1).1

/-! ### List plumbing

Histories are read through their suffixes: the rounds older than the
entry at index `i` are `rounds.drop (i + 1)`.
-/

/-- The entry at index `i` together with the rounds older than it is a
suffix of every list of rounds reaching back that far. -/
theorem entry_suffix {α : Type*} {l : List α} {i j : ℕ} (hi : i < l.length) (hij : j ≤ i) :
    l[i] :: l.drop (i + 1) <:+ l.drop j := by
  rw [← List.drop_eq_getElem_cons hi]
  exact List.drop_suffix_drop_left l hij

/-- The entry at index `i` is one of the rounds reaching back that
far. -/
theorem getElem_mem_drop {α : Type*} {l : List α} {i j : ℕ} (hi : i < l.length) (hij : j ≤ i) :
    l[i] ∈ l.drop j :=
  (entry_suffix hi hij).subset (List.mem_cons_self ..)

/-! ### Reachable positions -/

variable {r : ℕ} {G : SimpleGraph (Fin n)}

/-- The positions of a play from `G` in which every Connector move so far
was a vertex that still had an incident edge. A history records, newest
first, each Connector vertex together with the arena it was played in;
the arena reached is obtained by restricting and isolating one round at a
time. Moves on isolated vertices are not recorded: they end the play at
once (see `eq_bot_of_isolated`). -/
inductive Reached (r : ℕ) (G : SimpleGraph (Fin n)) :
    List (Round n) → SimpleGraph (Fin n) → Prop
  | nil : Reached r G [] G
  | step {rounds : List (Round n)} {A : SimpleGraph (Fin n)} {v : Fin n}
      (h : Reached r G rounds A) (hv : ∃ u, A.Adj v u) :
      Reached r G ((v, A) :: rounds) (nextArena r A v rounds)

variable {A : SimpleGraph (Fin n)} {rounds : List (Round n)}

/-- Inverting a played round: the arena an entry records is the position
its own older rounds reach, its vertex had an incident edge there, and
the position after it is the round's arena. -/
theorem reached_cons {v : Fin n} {A₀ : SimpleGraph (Fin n)}
    (h : Reached r G ((v, A₀) :: rounds) A) :
    Reached r G rounds A₀ ∧ (∃ u, A₀.Adj v u) ∧ A = nextArena r A₀ v rounds := by
  cases h with
  | step h hv => exact ⟨h, hv, rfl⟩

/-- Every reachable arena is a subgraph of the original: rounds only
delete edges. -/
theorem reached_le (h : Reached r G rounds A) : A ≤ G := by
  induction h with
  | nil => exact le_rfl
  | step _ _ ih => exact le_trans (nextArena_le ..) ih

/-- Every earlier stretch of a play is itself a play. -/
theorem reached_suffix (h : Reached r G rounds A) :
    ∀ t : List (Round n), t <:+ rounds → ∃ B, Reached r G t B := by
  induction h with
  | nil =>
    intro t ht
    rw [List.suffix_nil.mp ht]
    exact ⟨G, Reached.nil⟩
  | @step rounds A v hh hv ih =>
    intro t ht
    rcases List.suffix_cons_iff.mp ht with rfl | ht'
    · exact ⟨_, Reached.step hh hv⟩
    · exact ih t ht'

/-- **Isolation is permanent.** Every vertex the strategy meant to
isolate in a played round has no incident edge in any later arena: in the
arena right after the round it is either outside the ball the round
restricted to or inside the isolated batch, and later arenas only lose
further edges. -/
theorem isolated_of_suffix (h : Reached r G rounds A) :
    ∀ (e : Round n) (older : List (Round n)), e :: older <:+ rounds →
      ∀ z ∈ genSet r older e.1, ∀ u, ¬ A.Adj z u := by
  induction h with
  | nil => intro e older he; exact absurd he (by simp)
  | @step rounds A v hh hv ih =>
    intro e older he z hz u hadj
    rcases List.suffix_cons_iff.mp he with heq | he'
    · injection heq with h1 h2
      subst h1
      subst h2
      exact not_mem_batch_of_nextArena_adj hadj (mem_batch hz (mem_ball_of_nextArena_adj hadj))
    · exact ih e older he' z hz u (nextArena_le r A v rounds hadj)

/-- A vertex that still carries an edge lies in the ball of every earlier
round: a round keeps only the edges inside that ball, and later rounds
keep fewer. -/
theorem mem_ball_of_suffix (h : Reached r G rounds A) :
    ∀ (e : Round n) (older : List (Round n)), e :: older <:+ rounds →
      ∀ z u, A.Adj z u → z ∈ ball e.2 r e.1 := by
  induction h with
  | nil => intro e older he; exact absurd he (by simp)
  | @step rounds A v hh hv ih =>
    intro e older he z u hadj
    rcases List.suffix_cons_iff.mp he with heq | he'
    · injection heq with h1 h2
      subst h1
      exact mem_ball_of_nextArena_adj hadj
    · exact ih e older he' z u (nextArena_le r A v rounds hadj)

/-- Connector never repeats a vertex in a surviving play: an earlier
vertex is isolated from the round it was played on, while the current one
still carries an edge. -/
theorem picks_nodup (h : Reached r G rounds A) : (rounds.map Prod.fst).Nodup := by
  induction h with
  | nil => simp
  | @step rounds A v hh hv ih =>
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, ih⟩
    obtain ⟨e, he, hev⟩ := List.mem_map.mp hmem
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem he
    obtain ⟨u, hu⟩ := hv
    refine isolated_of_suffix hh e post ?_ v ?_ u hu
    · rw [hsplit]; exact List.suffix_append pre (e :: post)
    · have hev' : e.1 = v := hev
      rw [← hev']
      exact self_mem_genSet r post e.1

/-! ### Pairs of rounds -/

/-- The position at the round with index `b`, together with the incident
edge its vertex still had there. -/
theorem reached_entry (h : Reached r G rounds A) {b : ℕ} (hb : b < rounds.length) :
    Reached r G (rounds.drop (b + 1)) (rounds[b]).2 ∧
      ∃ u, (rounds[b]).2.Adj (rounds[b]).1 u := by
  obtain ⟨B, hB⟩ := reached_suffix h (rounds.drop b) (List.drop_suffix b rounds)
  rw [List.drop_eq_getElem_cons hb] at hB
  obtain ⟨h1, h2, -⟩ := reached_cons (v := (rounds[b]).1) (A₀ := (rounds[b]).2) hB
  exact ⟨h1, h2⟩

/-- The path the strategy maintains for a pair of rounds. The newer
round's vertex still had an edge, so it lies in the ball the older round
restricted to, and the strategy's chosen walk between them is a genuine
walk of length at most `r` in the older round's arena. Its endpoints are
distinct: the older vertex is already isolated when the newer round is
played. -/
theorem pair_walk (h : Reached r G rounds A) {b a : ℕ}
    (hb : b < rounds.length) (ha : a < rounds.length) (hba : b < a) :
    ∃ p : (rounds[a]).2.Walk (rounds[a]).1 (rounds[b]).1,
      p.length ≤ r ∧
      pathSet (rounds[a]).2 r (rounds[a]).1 (rounds[b]).1 = {z | z ∈ p.support} ∧
      (rounds[a]).1 ≠ (rounds[b]).1 := by
  obtain ⟨hRb, u, hu⟩ := reached_entry h hb
  have hball : (rounds[b]).1 ∈ ball (rounds[a]).2 r (rounds[a]).1 :=
    mem_ball_of_suffix hRb rounds[a] (rounds.drop (a + 1))
      (entry_suffix (j := b + 1) ha hba) _ u hu
  obtain ⟨p, hplen, hpset⟩ := pathSet_spec (mem_ball.mp hball)
  refine ⟨p, hplen, hpset, fun hEq => ?_⟩
  refine isolated_of_suffix hRb rounds[a] (rounds.drop (a + 1))
    (entry_suffix (j := b + 1) ha hba) (rounds[a]).1
    (self_mem_genSet r (rounds.drop (a + 1)) (rounds[a]).1) u ?_
  rw [hEq]
  exact hu

/-- **Distinct pairs' paths are disjoint.** A vertex on the older pair's
path is one the strategy isolated when the older pair's newer round was
played, hence has no edge in any arena from then on; but the newer pair's
path is a walk of positive length in an arena strictly later than that,
so each of its vertices does carry an edge. -/
theorem pair_disjoint (h : Reached r G rounds A) {bNew aNew bOld aOld : ℕ}
    (hbNew : bNew < rounds.length) (haNew : aNew < rounds.length)
    (hbOld : bOld < rounds.length) (haOld : aOld < rounds.length)
    (h1 : bNew < aNew) (h2 : aNew < bOld) (h3 : bOld < aOld) {z : Fin n}
    (hzOld : z ∈ pathSet (rounds[aOld]).2 r (rounds[aOld]).1 (rounds[bOld]).1)
    (hzNew : z ∈ pathSet (rounds[aNew]).2 r (rounds[aNew]).1 (rounds[bNew]).1) :
    False := by
  have hgen : z ∈ genSet r (rounds.drop (bOld + 1)) (rounds[bOld]).1 :=
    pathSet_subset_genSet (getElem_mem_drop (j := bOld + 1) haOld h3) (rounds[bOld]).1 hzOld
  obtain ⟨hRa, -⟩ := reached_entry h haNew
  have hiso : ∀ u, ¬ (rounds[aNew]).2.Adj z u :=
    isolated_of_suffix hRa rounds[bOld] (rounds.drop (bOld + 1))
      (entry_suffix (j := aNew + 1) hbOld h2) z hgen
  obtain ⟨p, hplen, hpset, hne⟩ := pair_walk h hbNew haNew h1
  rw [hpset] at hzNew
  have hlen0 : p.length ≠ 0 := fun h0 => hne (SimpleGraph.Walk.eq_of_length_eq_zero h0)
  obtain ⟨w, hw⟩ := exists_adj_of_mem_support p hlen0 hzNew
  exact hiso w hw

/-- Pairwise disjoint sets, one more of them than a bound on `S`, cannot
all meet `S`. -/
theorem exists_avoiding {s : ℕ} {S : Set (Fin n)} (hS : S.ncard ≤ s)
    (T : Fin (s + 1) → Set (Fin n))
    (hdisj : ∀ t t' : Fin (s + 1), t ≠ t' → ∀ z, z ∈ T t → z ∈ T t' → False) :
    ∃ t, ∀ z ∈ T t, z ∉ S := by
  by_contra hcon
  have hcon' : ∀ t : Fin (s + 1), ∃ z, z ∈ T t ∧ z ∈ S := fun t => by
    by_contra hct
    exact hcon ⟨t, fun z hz hzS => hct ⟨z, hz, hzS⟩⟩
  choose g hg1 hg2 using hcon'
  have hinj : Function.Injective g := by
    intro t t' hgg
    by_contra hne
    refine hdisj t t' hne (g t) (hg1 t) ?_
    rw [hgg]
    exact hg1 t'
  have hrange : Set.range g ⊆ S := by rintro _ ⟨t, rfl⟩; exact hg2 t
  have hle : (Set.range g).ncard ≤ S.ncard := Set.ncard_le_ncard hrange (Set.toFinite _)
  have heq : (Set.range g).ncard = s + 1 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

/-! ### No play lasts `N (2s + 2)` rounds -/

/-- **The extraction.** A play of `N (2·s + 2)` rounds cannot exist.
Connector's vertices are `N (2·s + 2)` distinct vertices, so
quasi-wideness returns a separator `S` of at most `s` vertices and a
distance-`r` independent set `B` of at least `2·s + 2` of them. Pairing
the selected rounds off chronologically gives `s + 1` pairs whose
maintained paths are pairwise disjoint, so one of them avoids `S`; that
path is a walk of length at most `r` between two distinct members of `B`
which survives the deletion of `S`, contradicting the independence. -/
theorem no_full_survival {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B)
    (h : Reached r G rounds A) (hlen : rounds.length = N (2 * s + 2)) : False := by
  classical
  have hPcard : ({z | z ∈ rounds.map Prod.fst} : Set (Fin n)).ncard = rounds.length := by
    have hcoe : ({z | z ∈ rounds.map Prod.fst} : Set (Fin n))
        = ((rounds.map Prod.fst).toFinset : Set (Fin n)) := by ext z; simp
    rw [hcoe, Set.ncard_coe_finset, List.toFinset_card_of_nodup (picks_nodup h),
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
      z ∈ pathSet (rounds[ai t]'(hal t)).2 r (rounds[ai t]'(hal t)).1
            (rounds[bi t]'(hbl t)).1 →
      z ∈ pathSet (rounds[ai t']'(hal t')).2 r (rounds[ai t']'(hal t')).1
            (rounds[bi t']'(hbl t')).1 → False := by
    intro t t' hne z hz hz'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact pair_disjoint h (hbl t) (hal t) (hbl t') (hal t') (hba t)
        (hcross t t' hlt) (hba t') hz' hz
    · exact pair_disjoint h (hbl t') (hal t') (hbl t) (hal t) (hba t')
        (hcross t' t hlt) (hba t) hz hz'
  obtain ⟨t₀, ht₀⟩ := exists_avoiding hS
    (fun t => pathSet (rounds[ai t]'(hal t)).2 r (rounds[ai t]'(hal t)).1
      (rounds[bi t]'(hbl t)).1) hdisj
  -- that pair's path contradicts distance independence
  obtain ⟨p, hplen, hpset, hpne⟩ := pair_walk h (hbl t₀) (hal t₀) (hba t₀)
  have hAle : (rounds[ai t₀]'(hal t₀)).2 ≤ G := reached_le (reached_entry h (hal t₀)).1
  have hsupp : ∀ z ∈ p.support, z ∉ S := fun z hz => ht₀ z (by rw [hpset]; exact hz)
  obtain ⟨q, hq⟩ := exists_walk_deleteVerts_of_le hAle p hsupp
  have hgt := distIndependent_iff.mp hInd (haB t₀) (hbB t₀) hpne q
  omega

/-! ### The main induction -/

/-- Splitter's strategy, by downward induction on the remaining round
budget. From a reachable position with `b` rounds still to play and
`N (2·s + 2) − b` rounds played, Splitter wins within `b` rounds: at
budget zero the play would have lasted `N (2·s + 2)` rounds, which
`no_full_survival` excludes; with a round left, playing the batch keeps
the position reachable and playing an isolated vertex ends the play at
once. -/
theorem splitterWins_of_reached {N : ℕ → ℕ} {s : ℕ}
    (hQ : ∀ P : Set (Fin n), N (2 * s + 2) ≤ P.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ P \ S ∧ 2 * s + 2 ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B) :
    ∀ (b : ℕ) (rounds : List (Round n)) (A : SimpleGraph (Fin n)),
      Reached r G rounds A → rounds.length + b = N (2 * s + 2) →
      SplitterWins (N (2 * s + 2) * (r + 1)) r b A := by
  intro b
  induction b with
  | zero =>
    intro rounds A hR hlen
    exact (no_full_survival hQ hR (by omega)).elim
  | succ b ih =>
    intro rounds A hR hlen
    rw [splitterWins_succ_iff]
    refine Or.inr fun v => ?_
    by_cases hv : ∃ u, A.Adj v u
    · refine ⟨batch r rounds A v, batch_subset_ball r rounds A v, ?_, ?_⟩
      · have h1 := batch_ncard_le r rounds A v
        have h2 : rounds.length + 1 ≤ N (2 * s + 2) := by omega
        have h3 : (rounds.length + 1) * (r + 1) = rounds.length * (r + 1) + (r + 1) :=
          Nat.succ_mul _ _
        have h4 : (rounds.length + 1) * (r + 1) ≤ N (2 * s + 2) * (r + 1) :=
          Nat.mul_le_mul_right _ h2
        omega
      · exact ih ((v, A) :: rounds) (nextArena r A v rounds) (Reached.step hR hv)
          (by simp only [List.length_cons]; omega)
    · exact ⟨∅, Set.empty_subset _, by simp,
        splitterWins_of_eq_bot (eq_bot_of_isolated (fun z hz => hv ⟨z, hz⟩) ∅)⟩

end Play

/-! ### The theorem -/

/--
---
conclusion: Lax3.NowhereDenseSplitter.splitterWins_of_nowhereDense
---
**Splitter wins on nowhere dense classes** (Lemma 4.2 of Chapter 4 of the
source lecture notes, Theorem 4.2 of Grohe–Kreutzer–Siebertz, in the
isolation variant): on a nowhere dense class, for every radius `r` there
are a round bound `ℓ` and a batch bound `m`, depending only on the class
and `r`, with which Splitter wins the `(ℓ, m, r)`-game on every member.

# Proof strategy

Take the quasi-wideness margins `N, s` of the class at radius `r` from
the endorsed `Lax12.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense`
and put `ℓ := N (2·s + 2)` and `m := ℓ · (r + 1)`. Splitter's strategy
isolates, in each round, Connector's new vertex `v` together with the
still-active vertices of a chosen walk of length at most `r` from every
earlier Connector vertex to `v`, taken in the arena that earlier round
was played in — one vertex plus one path of at most `r + 1` vertices per
round played, which is the bound `m`. A play in which every Connector
move still had an incident edge is recorded by `Reached`; moves on
isolated vertices end the play at once, since the ball around such a
vertex is the vertex alone.

The whole content is that no play lasts `ℓ` rounds. Connector's vertices
are then `ℓ` distinct vertices, so quasi-wideness returns a separator `S`
of at most `s` vertices and a distance-`r` independent set `B` of at
least `2·s + 2` of them. Pairing the rounds that selected a vertex of `B`
off chronologically gives `s + 1` pairs, and for each the strategy's
maintained walk between the pair's two vertices, in the older round's
arena. Two ingredients replace the notes' "removed vertices are gone".
*Isolation is permanent*: arenas only lose edges, so a vertex the
strategy isolated in some round has no incident edge in any later arena.
*Distinct pairs' walks are disjoint*: a vertex of an older pair's walk
was isolated when that pair's newer round was played, while every vertex
of a newer pair's walk carries an edge in an arena from strictly after
that round. So the `s + 1` walks are pairwise disjoint and one of them
avoids `S`; rebuilding it inside `deleteVerts G S` gives a walk of length
at most `r` between two distinct members of `B`, contradicting the
independence.

The round bound is `N (2·s + 2)`, not the notes' `N (2·s + 1)`: their own
proof needs `s + 1` pairwise disjoint paths so that one avoids the
separator, which is `2·s + 2` selected rounds. See the module docstring.
-/
theorem splitterWins_of_nowhereDense (C : GraphClass) (h : NowhereDense C)
    (r : ℕ) :
    ∃ ℓ m : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      SplitterWins m r ℓ G := by
  obtain ⟨N, s, hUQW⟩ :=
    Lax12.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense C h r
  exact ⟨N (2 * s + 2), N (2 * s + 2) * (r + 1), fun n G hG =>
    splitterWins_of_reached (hUQW (2 * s + 2) n G hG) (N (2 * s + 2)) [] G
      Reached.nil (by simp)⟩

end Lax3Proofs.SplitterWin
