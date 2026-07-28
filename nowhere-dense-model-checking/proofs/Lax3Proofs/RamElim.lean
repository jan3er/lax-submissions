import Lax3Proofs.RamBfs
import Lax3Proofs.Augmentation

/-!
Greedy minimum-degree elimination over a masked block structure, as a
word-RAM program with its correctness and its running time.

This is the one *ordering* the campaign ever computes. It is asked for
three times: to orient the input graph before the augmentation starts,
to orient each round's fraternity graph, and to order the augmented
graph for the cover pass. All three hand the engine the same thing — a
graph already materialized in compressed-row form, plus one bit per
vertex saying which vertices are in play — and all three read back the
same three answers: an elimination ranking, the degeneracy bound the
run achieved, and the orientation of every edge towards the endpoint
that was eliminated *first*.

### The algorithm

Classical Matula–Beck: keep the current degree of every vertex — its
number of neighbours that are alive and not yet eliminated — keep the
vertices bucketed by that degree, and keep a pointer `mind` at the
smallest bucket that can still be nonempty. A turn either moves the
pointer up over an empty bucket, or takes a vertex out of the bucket it
points at. A vertex taken out is eliminated: it is stamped with the
next rank, its extraction degree is recorded, and its row is scanned,
every surviving neighbour losing one from its degree and being
re-bucketed. The pointer then drops by one, since a decrement can only
have created a vertex one below the degree just extracted.

The buckets are **lazily deleted** singly-linked stacks in one arena.
Re-bucketing pushes a new slot and never unlinks the old one, so a
popped slot may be stale — its vertex already eliminated, or already
moved to a smaller bucket — and is simply discarded. This is what buys
the program its simplicity: no doubly-linked list, no back pointers,
one push and one pop, and the arena is bounded because a push happens
once per vertex at the start and once per scanned slot afterwards.

### One `k` serves both facts, and what that forces on the rank

The bound the run achieves is `k`, the largest degree at which any
extraction happened. Two facts are wanted of it, and they point in
opposite directions unless the rank is chosen with care.

* The orientation should have **in-degree at most `k`**, and the
  in-neighbours of `w` should be the neighbours the run had to look at
  when it eliminated `w` — for that is the set whose size is `w`'s
  extraction degree, and nothing else about `w` is bounded by `k`.
  Those are the neighbours eliminated **after** `w`.
* The rank should be **`BackDegLE`-good** for the same `k`, and
  `BackDegLE` counts neighbours of *smaller* rank.

So the rank must count **down**: the vertex extracted first gets the
largest rank. Then "eliminated after `w`" is "rank below `w`", the two
sets coincide, and one number is both the in-degree bound and the
back-degree bound. The engine therefore stamps the `c`-th vertex it
extracts with `n - 1 - c`, and `elimCert_orients`, `elimCert_inDegLE`
and `elimCert_backDegLE` all read off the same field of the
certificate. Getting this backwards would leave `InDegLE` true of the
extraction degrees and `BackDegLE` true of nothing.

### The mask, and the vertices it kills

Killing is not deletion: the arena is `RamBfs.masked G M`, which is
Lax12's `deleteVerts` — the carrier stays and the edges incident to a
dead vertex go away. A dead vertex is therefore *isolated* in the
arena, its current degree is zero at every moment of the run, and the
engine needs no case for it at all: it sits in bucket zero, is
extracted at some point contributing nothing to `k`, gets a rank like
everything else, and has no arcs. That is the whole of the mask's
effect on this program, and it is why the ranking is stated as a
bijection of *all* `n` vertices rather than of the alive ones.

### What is proved

`ElimCert A ρ k` is what a run leaves behind, stated on `Fin n` and
with no program in it: `ρ` is injective, no vertex sees more than `k`
neighbours at its own extraction, `k` is attained, and every extraction
took a vertex of minimum current degree. Everything the campaign wants
is derived from that certificate alone —

* `elimOr A ρ`, the orientation, with `Orients`, `InDegLE k` and the
  membership characterization `u ∈ inN w ↔ A.Adj u w ∧ ρ u < ρ w`;
* `BackDegLE A ρ k` and hence `DegeneracyLE A k`, and the same on
  `(elimOr A ρ).toGraph`, which is `A` on the nose;
* **the greedy guarantee** `k ≤ k'` for every `k'` with
  `LowDegreeVertices A k'` — the one clause that turns a density bound
  on a nowhere dense class into a bound on the engine's output.

The run is stated against `Elim`, the loop invariant: the degrees are
the true current degrees of the arena, the pointer is a lower bound on
all of them, the ranks handed out so far are the top `cnt` numbers in
extraction order, and `kmax` is the largest extraction degree so far.
Its three turns are proved — `Elim.init` starts it, `Elim.bump` moves
the pointer up over an empty bucket, `Elim.extract` is the one turn
that does anything — and `Elim.cert` reads the certificate off the
state the loop exits in. `card_liveSlots`, which says that the live
slots of a row are in bijection with the neighbours in the arena, is
what a degree count is worth, and it is the reason the input surface is
`CsrSimple` — `CsrGraph` with "a row names each neighbour once" added,
which a search does not need and a count does.

### What is left

`elim_spec` is the specification, and `Implements` is the single
obligation it is proved from: the Hoare triple for `elimCom` itself,
stated over the program text, the input surface a caller has, and the
linear cost. Everything that triple's postcondition *means* —
`elimPost_of_elimMem`, and behind it the whole of `ElimCert` and
`InCsr` — is proved here unconditionally, and the program is exhibited,
compiled and run: the worked example checks its three answers on a
five-vertex graph, with and without the mask, against the hand
computation.

Of the five phase walks `Implements` splits into, **two are
discharged** — `initDeg_spec`, the degree pass with its amortized outer
loop, and `offPass_spec`, the running sum — and three remain:
`initBuck`, `elimLoop` and `fillPass`. The first two of those wait on
one missing piece, a reachability relation for the lazily deleted
bucket stacks; `Implements`' own docstring says what each owes.
-/

namespace Lax3Proofs.RamElim

open Lax3Proofs.Augmentation
open Lax3Proofs.RamBfs (masked masked_adj CsrGraph MAdj)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n ns : ℕ} {G : SimpleGraph (Fin n)} {M O T : ℕ → ℕ}

/-! ### The survivors, and the degree a vertex is extracted at

The rank counts down, so the vertices still present when the vertex of
rank `r` is taken are those of rank at most `r`, and a vertex's
neighbours among them are the ones its extraction degree counts. Under
an injective rank that set is also its set of neighbours of *smaller*
rank, which is what `BackDegLE` asks about — the two readings the whole
design turns on. -/

/-- The vertices still present when the vertex of rank `r` is taken. -/
noncomputable def surv {n : ℕ} (ρ : Fin n → ℕ) (r : ℕ) : Finset (Fin n) :=
  pick (fun u => ρ u ≤ r)

theorem mem_surv {ρ : Fin n → ℕ} {r : ℕ} {u : Fin n} : u ∈ surv ρ r ↔ ρ u ≤ r := mem_pick

/-- The neighbours a vertex still has when it is extracted: its
extraction degree is the size of this set. -/
noncomputable def curNbrs {n : ℕ} (A : SimpleGraph (Fin n)) (ρ : Fin n → ℕ) (w : Fin n) :
    Finset (Fin n) := nbrsIn A (surv ρ (ρ w)) w

theorem mem_curNbrs {A : SimpleGraph (Fin n)} {ρ : Fin n → ℕ} {w u : Fin n} :
    u ∈ curNbrs A ρ w ↔ ρ u ≤ ρ w ∧ A.Adj u w := by
  rw [curNbrs, mem_nbrsIn]
  exact and_congr mem_surv Iff.rfl

/-- **The two readings coincide.** Under an injective rank a neighbour
never has the same rank, so the neighbours a vertex still sees at its
extraction are exactly its neighbours of smaller rank. This is the one
observation that lets a single `k` bound both the in-degrees of the
orientation and the back-degrees of the rank. -/
theorem mem_curNbrs_iff {A : SimpleGraph (Fin n)} {ρ : Fin n → ℕ}
    (hinj : Function.Injective ρ) {w u : Fin n} :
    u ∈ curNbrs A ρ w ↔ A.Adj u w ∧ ρ u < ρ w := by
  rw [mem_curNbrs]
  constructor
  · rintro ⟨hle, hadj⟩
    refine ⟨hadj, lt_of_le_of_ne hle fun hc => ?_⟩
    exact A.ne_of_adj hadj (hinj hc)
  · rintro ⟨hadj, hlt⟩
    exact ⟨le_of_lt hlt, hadj⟩

/-- The set of neighbours of smaller rank, as a `Finset`. -/
noncomputable def backNbrs {n : ℕ} (A : SimpleGraph (Fin n)) (ρ : Fin n → ℕ) (w : Fin n) :
    Finset (Fin n) := pick (fun u => A.Adj u w ∧ ρ u < ρ w)

theorem mem_backNbrs {A : SimpleGraph (Fin n)} {ρ : Fin n → ℕ} {w u : Fin n} :
    u ∈ backNbrs A ρ w ↔ A.Adj u w ∧ ρ u < ρ w := mem_pick

/-- The two `Finset`s of the previous two lemmas are one. -/
theorem curNbrs_eq_backNbrs {A : SimpleGraph (Fin n)} {ρ : Fin n → ℕ}
    (hinj : Function.Injective ρ) (w : Fin n) : curNbrs A ρ w = backNbrs A ρ w := by
  ext u
  rw [mem_curNbrs_iff hinj, mem_backNbrs]

/-- The coercion of a filtered `Finset.univ` is the set it filters by;
this is what carries a `Finset.card` bound to the `Set.ncard` bound
`BackDegLE` is stated with. -/
theorem coe_pick {p : Fin n → Prop} : (↑(pick p) : Set (Fin n)) = {u | p u} := by
  ext u; simpa using (mem_pick (p := p) (u := u))

/-! ### The certificate

What a run of the engine leaves behind, with no program in it. The
first three clauses are the bookkeeping of the extraction degrees; the
fourth is the greedy choice, and it is the only one that says the
engine picked a *minimum*. -/

/-- `ElimCert A ρ k`: the ranking `ρ` is one greedy minimum-degree
elimination of `A`, whose largest extraction degree is `k`. -/
structure ElimCert {n : ℕ} (A : SimpleGraph (Fin n)) (ρ : Fin n → ℕ) (k : ℕ) : Prop where
  /-- The rank is a ranking. -/
  inj : Function.Injective ρ
  /-- No vertex saw more than `k` neighbours at its own extraction. -/
  deg_le : ∀ w, (curNbrs A ρ w).card ≤ k
  /-- And some vertex saw exactly `k` — so `k` is the run's own bound
  and not a number handed to it. -/
  attained : k = 0 ∨ ∃ w, (curNbrs A ρ w).card = k
  /-- **The greedy choice**: at every extraction the vertex taken had
  the smallest current degree among the vertices still present. -/
  min_deg : ∀ w u : Fin n, ρ u ≤ ρ w →
    (curNbrs A ρ w).card ≤ (nbrsIn A (surv ρ (ρ w)) u).card

namespace ElimCert

variable {A : SimpleGraph (Fin n)} {ρ : Fin n → ℕ} {k : ℕ}

/-! ### The orientation

Every edge points at the endpoint eliminated first, which — the rank
counting down — is the endpoint of *larger* rank. -/

/-- The orientation the rank induces: the in-neighbours of `w` are its
neighbours of smaller rank, that is, the ones still present when `w`
was extracted. -/
noncomputable def elimOr {n : ℕ} (A : SimpleGraph (Fin n)) (ρ : Fin n → ℕ) : Orientation n where
  inN w := backNbrs A ρ w
  not_mem_self v hv := A.irrefl (mem_backNbrs.1 hv).1
  asymm u v huv hvu := by
    have h₁ := (mem_backNbrs.1 huv).2
    have h₂ := (mem_backNbrs.1 hvu).2
    omega

@[simp] theorem mem_elimOr {A : SimpleGraph (Fin n)} {ρ : Fin n → ℕ} {w u : Fin n} :
    u ∈ (elimOr A ρ).inN w ↔ A.Adj u w ∧ ρ u < ρ w := mem_backNbrs

/-- **The orientation is one.** Every arc is an edge, and every edge
carries an arc: adjacent vertices are distinct, so their ranks are, so
one of them is the smaller. -/
theorem orients (h : ElimCert A ρ k) : (elimOr A ρ).Orients A := by
  intro u v
  constructor
  · intro hadj
    rcases lt_trichotomy (ρ u) (ρ v) with hlt | heq | hgt
    · exact Or.inl (mem_elimOr.2 ⟨hadj, hlt⟩)
    · exact absurd (h.inj heq) (A.ne_of_adj hadj)
    · exact Or.inr (mem_elimOr.2 ⟨hadj.symm, hgt⟩)
  · rintro (hin | hin)
    · exact (mem_elimOr.1 hin).1
    · exact ((mem_elimOr.1 hin).1).symm

/-- **The in-degrees are the extraction degrees**, and so are bounded by
`k`. -/
theorem inDegLE (h : ElimCert A ρ k) : (elimOr A ρ).InDegLE k := by
  intro v
  have : (elimOr A ρ).inN v = curNbrs A ρ v := (curNbrs_eq_backNbrs h.inj v).symm
  rw [this]
  exact h.deg_le v

/-- The underlying graph of the orientation is the arena itself, which
is what lets a statement about `BackDegLE` of one be read on the
other. -/
theorem toGraph_eq (h : ElimCert A ρ k) : (elimOr A ρ).toGraph = A := by
  ext u v
  exact (h.orients u v).symm

/-- **The back-degrees are the extraction degrees too.** This is the
`Set.ncard` reading `BackDegLE` is stated in. -/
theorem backDegLE (h : ElimCert A ρ k) : BackDegLE A ρ k := by
  intro v
  have hset : {u | A.Adj u v ∧ ρ u < ρ v} = (↑(backNbrs A ρ v) : Set (Fin n)) := by
    rw [backNbrs, coe_pick]
  rw [hset, Set.ncard_coe_finset, ← curNbrs_eq_backNbrs h.inj]
  exact h.deg_le v

/-- The same fact on the orientation's own graph. -/
theorem backDegLE_toGraph (h : ElimCert A ρ k) : BackDegLE (elimOr A ρ).toGraph ρ k := by
  rw [h.toGraph_eq]; exact h.backDegLE

/-- **The arena is `k`-degenerate**, with the engine's own ranking as
the witness. -/
theorem degeneracyLE (h : ElimCert A ρ k) : DegeneracyLE A k :=
  ⟨ρ, h.inj, h.backDegLE⟩

/-! ### The greedy guarantee

The clause the analysis is spent against: the engine's `k` is at most
any bound that holds for *every* vertex set, so a density argument on a
nowhere dense class bounds the engine's output without knowing anything
about the order it produced. -/

/-- **The greedy guarantee.** If every nonempty set of vertices of the
arena contains a vertex with at most `k'` neighbours inside it, then
the engine's bound is at most `k'`: the extraction that attained `k`
was made in some such set, and it took a vertex of minimum degree
there. -/
theorem le_of_lowDegreeVertices (h : ElimCert A ρ k) {k' : ℕ}
    (hk' : LowDegreeVertices A k') : k ≤ k' := by
  rcases h.attained with rfl | ⟨w, hw⟩
  · exact Nat.zero_le _
  · obtain ⟨u, huS, hu⟩ := hk' (surv ρ (ρ w)) ⟨w, mem_surv.2 le_rfl⟩
    calc k = (curNbrs A ρ w).card := hw.symm
      _ ≤ (nbrsIn A (surv ρ (ρ w)) u).card := h.min_deg w u (mem_surv.1 huS)
      _ ≤ k' := hu

/-- The contrapositive reading, which is how a `DegeneracyLE` bound on
the arena reaches the engine. -/
theorem le_of_degeneracyLE (h : ElimCert A ρ k) {k' : ℕ} (hk' : DegeneracyLE A k') : k ≤ k' :=
  h.le_of_lowDegreeVertices (lowDegreeVertices_of_degeneracyLE hk')

end ElimCert

/-! ### The call surface

Two readings the campaign uses verbatim: a round that orients a whole
graph hands the engine an all-alive mask and gets its graph back, and a
fraternity round hands it the fraternity graph and gets
`Augmentation.GreedyFratRound` — the greedy guarantee is exactly the
`∀ k` that definition quantifies over. -/

/-- A back-degree bound may be loosened. -/
theorem backDegLE_mono {F : SimpleGraph (Fin n)} {σ : Fin n → ℕ} {k k' : ℕ}
    (h : BackDegLE F σ k) (hk : k ≤ k') : BackDegLE F σ k' := fun v => (h v).trans hk

/-- **With nothing killed the arena is the graph itself.** This is what
a caller that materializes a whole graph — the input graph at round
zero, a fraternity graph at a later round — hands the engine. -/
theorem masked_of_all_alive (G : SimpleGraph (Fin n)) {M : ℕ → ℕ} (hM : ∀ v < n, M v ≠ 0) :
    masked G M = G := by
  ext u v
  rw [masked_adj]
  exact ⟨fun h => h.1, fun h => ⟨h, hM (u : ℕ) u.isLt, hM (v : ℕ) v.isLt⟩⟩

/-- **What a fraternity round consumes.** The engine's ranking is a
witness for *every* degeneracy bound the analysis can prove of the
fraternity graph, because the greedy guarantee says the run's own bound
is below all of them. What is left to the caller is the one thing the
engine cannot know: that the round's orientation put its fraternal arcs
the way the ranking says. -/
theorem greedyFratRound_of_cert {D D' : Orientation n} {ρ : Fin n → ℕ} {k : ℕ}
    (h : ElimCert (fratGraph D) ρ k)
    (hor : ∀ u v : Fin n, u ∈ D'.inN v → (fratGraph D).Adj u v → ρ u < ρ v) :
    GreedyFratRound D D' :=
  fun _ hk' => ⟨ρ, backDegLE_mono h.backDegLE (h.le_of_lowDegreeVertices hk'), hor⟩

/-! ### The state of the elimination, as sets

Everything the loop knows is a statement about two `Finset`s of the
arena: the vertices it has not eliminated yet, and — for a vertex it
*has* eliminated — the vertices that were still there at that moment.
The second is recovered from the ranks, which is the point of ranking
downwards: a vertex was present when `w` was taken exactly when it is
still uneliminated, or was eliminated with a smaller rank. -/

/-- The vertices the loop has not eliminated yet. -/
noncomputable def aliveF {n : ℕ} (E : ℕ → ℕ) : Finset (Fin n) :=
  pick (fun v => E (v : ℕ) = 0)

theorem mem_aliveF {E : ℕ → ℕ} {v : Fin n} : v ∈ aliveF E ↔ E (v : ℕ) = 0 := mem_pick

/-- The vertices that were still present when the vertex of rank
`r - 1` was taken: the ones not eliminated yet, and the ones eliminated
at a rank below `r`. -/
noncomputable def survOf {n : ℕ} (E R : ℕ → ℕ) (r : ℕ) : Finset (Fin n) :=
  pick (fun u => E (u : ℕ) = 0 ∨ (E (u : ℕ) = 1 ∧ R (u : ℕ) < r))

theorem mem_survOf {E R : ℕ → ℕ} {r : ℕ} {u : Fin n} :
    u ∈ survOf E R r ↔ E (u : ℕ) = 0 ∨ (E (u : ℕ) = 1 ∧ R (u : ℕ) < r) := mem_pick

/-- Killing a vertex removes it from every neighbourhood. -/
theorem nbrsIn_erase {A : SimpleGraph (Fin n)} (S : Finset (Fin n)) (x w : Fin n) :
    nbrsIn A (S.erase x) w = (nbrsIn A S w).erase x := by
  ext u
  simp only [Finset.mem_erase, mem_nbrsIn]
  tauto
/-- Eliminating a vertex erases it from the surviving set. -/
theorem aliveF_upd {E : ℕ → ℕ} {v : ℕ} (hv : v < n) :
    aliveF (n := n) (upd E v 1) = (aliveF E).erase ⟨v, hv⟩ := by
  ext u
  simp only [mem_aliveF, Finset.mem_erase]
  by_cases h : (u : ℕ) = v
  · have hu : u = ⟨v, hv⟩ := Fin.ext h
    subst hu
    simp
  · rw [upd_of_ne _ h]
    exact ⟨fun h0 => ⟨fun hc => h (by rw [hc]), h0⟩, fun hh => hh.2⟩

/-- A vertex is one of its neighbour's neighbours in the arena; this is
the `Fin`-level reading of the number-level `MAdj` the program speaks
in. -/
theorem madj_iff {u : Fin n} {v : ℕ} (hv : v < n) :
    MAdj G M (u : ℕ) v ↔ (masked G M).Adj u ⟨v, hv⟩ :=
  ⟨fun h => by simpa using h.2.2, fun h => ⟨u.isLt, hv, by simpa using h⟩⟩

/-- No vertex is its own neighbour, so a current degree is smaller than
the number of vertices. -/
theorem card_nbrsIn_lt {A : SimpleGraph (Fin n)} (S : Finset (Fin n)) (w : Fin n) :
    (nbrsIn A S w).card < n := by
  have hsub : nbrsIn A S w ⊆ Finset.univ.erase w := fun u hu =>
    Finset.mem_erase.2 ⟨A.ne_of_adj (mem_nbrsIn.1 hu).2, Finset.mem_univ _⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcard
  have := w.isLt
  omega

/-! Two rewritings of the survivor set, which are the whole content of
"the rank counts down": eliminating a vertex at the next rank down
changes no *earlier* survivor set, and the survivor set it creates for
itself is the set that was alive a moment ago. -/

/-- An extraction leaves the survivor set of every earlier extraction
alone. -/
theorem survOf_upd_of_lt {E R : ℕ → ℕ} {v r s : ℕ} (hE : E v = 0) (hrs : r < s) :
    survOf (n := n) (upd E v 1) (upd R v r) s = survOf E R s := by
  ext u
  simp only [mem_survOf]
  by_cases h : (u : ℕ) = v
  · rw [h, upd_self, upd_self, hE]
    simp [hrs]
  · rw [upd_of_ne _ h, upd_of_ne _ h]

/-- And the survivor set it creates for itself is exactly what was
alive. -/
theorem survOf_upd_self {E R : ℕ → ℕ} {v r : ℕ} (hE : E v = 0)
    (hbit : ∀ u < n, E u ≤ 1) (hge : ∀ u < n, E u = 1 → r + 1 ≤ R u) :
    survOf (n := n) (upd E v 1) (upd R v r) (r + 1) = aliveF E := by
  ext u
  simp only [mem_survOf, mem_aliveF]
  by_cases h : (u : ℕ) = v
  · rw [h, upd_self, upd_self, hE]; simp
  · rw [upd_of_ne _ h, upd_of_ne _ h]
    have hb := hbit (u : ℕ) u.isLt
    constructor
    · rintro (h0 | ⟨h1, hlt⟩)
      · exact h0
      · exact absurd hlt (by have := hge (u : ℕ) u.isLt h1; omega)
    · exact Or.inl

/-! ### The invariant of the elimination loop

Twelve clauses, and every one of them is here because some step asks
for it. The three about the ranks say that the ranks handed out so far
are the top `cnt` numbers, in extraction order; `deg` says the degree
array is the truth about the arena; `min_le` is what makes an
extraction at the pointer a *minimum*; and `rec` and `mini` are the two
facts about a past extraction that have to outlive it. -/

/-- What holds of the arrays and the scalars at every point of the
elimination. -/
structure Elim {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (E D R ID : ℕ → ℕ)
    (cnt mind kmax : ℕ) : Prop where
  /-- The elimination flags are bits. -/
  bit : ∀ v < n, E v ≤ 1
  /-- Not everything can have been eliminated twice. -/
  cnt_le : cnt ≤ n
  /-- `cnt` counts the vertices eliminated. -/
  card_elim : (pick (fun v : Fin n => E (v : ℕ) = 1)).card = cnt
  /-- A rank is a vertex number. -/
  rank_lt : ∀ v < n, E v = 1 → R v < n
  /-- The ranks handed out so far are the top `cnt` of them. -/
  rank_ge : ∀ v < n, E v = 1 → n - cnt ≤ R v
  /-- And no two are equal. -/
  rank_inj : ∀ v < n, ∀ w < n, E v = 1 → E w = 1 → R v = R w → v = w
  /-- The degree array holds the true current degrees of the arena. -/
  deg : ∀ v : Fin n, D (v : ℕ) = (nbrsIn (masked G M) (aliveF E) v).card
  /-- The pointer is a lower bound on every surviving degree: this is
  what makes the vertex it points at a minimum. -/
  min_le : ∀ v < n, E v = 0 → mind ≤ D v
  /-- Every extraction degree recorded is the degree its vertex really
  had, in the arena, at the moment it was taken. -/
  taken : ∀ w : Fin n, E (w : ℕ) = 1 →
    ID (w : ℕ) = (nbrsIn (masked G M) (survOf E R (R (w : ℕ) + 1)) w).card
  /-- And nothing still present then had a smaller degree. -/
  mini : ∀ w : Fin n, E (w : ℕ) = 1 → ∀ u : Fin n, u ∈ survOf E R (R (w : ℕ) + 1) →
    ID (w : ℕ) ≤ (nbrsIn (masked G M) (survOf E R (R (w : ℕ) + 1)) u).card
  /-- `kmax` bounds every extraction degree so far. -/
  kmax_le : ∀ w < n, E w = 1 → ID w ≤ kmax
  /-- And is one of them, so it is the run's own bound. -/
  kmax_att : kmax = 0 ∨ ∃ w < n, E w = 1 ∧ ID w = kmax

namespace Elim

variable {E D R ID : ℕ → ℕ} {cnt mind kmax : ℕ}

/-- Every degree is smaller than the number of vertices. -/
theorem deg_lt (h : Elim G M E D R ID cnt mind kmax) {v : ℕ} (hv : v < n) : D v < n := by
  rw [show v = ((⟨v, hv⟩ : Fin n) : ℕ) from rfl, h.deg]
  exact card_nbrsIn_lt _ _

/-- The pointer never passes the last possible degree. -/
theorem mind_lt (h : Elim G M E D R ID cnt mind kmax) {v : ℕ} (hv : v < n) (hE : E v = 0) :
    mind < n := lt_of_le_of_lt (h.min_le v hv hE) (h.deg_lt hv)

/-- **The engine has work left exactly while `cnt < n`.** -/
theorem exists_alive (h : Elim G M E D R ID cnt mind kmax) (hcnt : cnt < n) :
    ∃ v < n, E v = 0 := by
  by_contra hc
  simp only [not_exists, not_and] at hc
  have huniv : (pick (fun v : Fin n => E (v : ℕ) = 1)) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun v => mem_pick.2 ?_
    have := hc (v : ℕ) v.isLt
    have := h.bit (v : ℕ) v.isLt
    omega
  have := h.card_elim
  rw [huniv, Finset.card_univ, Fintype.card_fin] at this
  omega

/-- **The one turn that does anything.** The vertex the pointer names
is eliminated: it is stamped with the next rank down, its extraction
degree is recorded, and every neighbour it still had in the arena loses
one from its degree. The pointer drops by one, since a decrement can
only have produced a degree one below the one just extracted.

The new degree array is not written out here; it is described, since
the program produces it by a row scan and only the two cases matter —
a neighbour in the arena goes down by one, everything else stays. -/
theorem extract (h : Elim G M E D R ID cnt mind kmax) (hcnt : cnt < n)
    {v : ℕ} (hv : v < n) (hE : E v = 0) (hDv : D v = mind) {D' : ℕ → ℕ}
    (hdec : ∀ u < n, MAdj G M u v → D' u = D u - 1)
    (hkeep : ∀ u < n, ¬ MAdj G M u v → D' u = D u) :
    Elim G M (upd E v 1) D' (upd R v (n - 1 - cnt)) (upd ID v mind)
      (cnt + 1) (mind - 1) (max kmax mind) := by
  classical
  set r := n - 1 - cnt with hr
  have hrn : r < n := by omega
  have hrsucc : r + 1 = n - cnt := by omega
  -- every rank handed out so far is above the one being handed out now
  have hold : ∀ u < n, E u = 1 → r + 1 ≤ R u := fun u hu hEu => by
    have := h.rank_ge u hu hEu; omega
  have hne : ∀ u : Fin n, E (u : ℕ) = 1 → (u : ℕ) ≠ v := fun u hEu hc => by
    rw [hc] at hEu; omega
  -- the two survivor sets the extraction touches
  have hself : survOf (n := n) (upd E v 1) (upd R v r) (r + 1) = aliveF E :=
    survOf_upd_self hE h.bit hold
  have hearlier : ∀ s, r < s →
      survOf (n := n) (upd E v 1) (upd R v r) s = survOf E R s :=
    fun s hs => survOf_upd_of_lt hE hs
  -- what the elimination does to the surviving set
  have halive : aliveF (n := n) (upd E v 1) = (aliveF E).erase ⟨v, hv⟩ := aliveF_upd hv
  have hmemv : ∀ u : Fin n, (⟨v, hv⟩ : Fin n) ∈ nbrsIn (masked G M) (aliveF E) u ↔
      MAdj G M (u : ℕ) v := by
    intro u
    rw [mem_nbrsIn, mem_aliveF, madj_iff hv]
    exact ⟨fun hh => hh.2.symm, fun hh => ⟨hE, hh.symm⟩⟩
  -- the degree array after the scan
  have hdeg' : ∀ u : Fin n, D' (u : ℕ) = (nbrsIn (masked G M) (aliveF (upd E v 1)) u).card := by
    intro u
    rw [halive, nbrsIn_erase]
    by_cases hadj : MAdj G M (u : ℕ) v
    · rw [hdec (u : ℕ) u.isLt hadj, h.deg u,
        Finset.card_erase_of_mem ((hmemv u).2 hadj)]
    · rw [hkeep (u : ℕ) u.isLt hadj, h.deg u,
        Finset.erase_eq_of_notMem (fun hc => hadj ((hmemv u).1 hc))]
  refine ⟨fun u hu => ?_, by omega, ?_, fun u hu hEu => ?_, fun u hu hEu => ?_,
    fun u hu w hw hEu hEw hR => ?_, hdeg', fun u hu hEu => ?_, fun w hEw => ?_,
    fun w hEw u huS => ?_, fun u hu hEu => ?_, ?_⟩
  · by_cases huv : u = v
    · rw [huv, upd_self]
    · rw [upd_of_ne _ huv]; exact h.bit u hu
  · -- the eliminated set gains exactly the vertex just taken
    have hins : (pick (fun u : Fin n => (upd E v 1) (u : ℕ) = 1))
        = insert (⟨v, hv⟩ : Fin n) (pick (fun u : Fin n => E (u : ℕ) = 1)) := by
      ext u
      simp only [mem_pick, Finset.mem_insert]
      by_cases huv : (u : ℕ) = v
      · have : u = (⟨v, hv⟩ : Fin n) := Fin.ext huv
        subst this
        simp
      · rw [upd_of_ne _ huv]
        exact ⟨fun hh => Or.inr hh, fun hh => hh.resolve_left fun hc => huv (by rw [hc])⟩
    rw [hins, Finset.card_insert_of_notMem (by simp [mem_pick, hE]), h.card_elim]
  · by_cases huv : u = v
    · rw [huv, upd_self]; omega
    · rw [upd_of_ne _ huv]; exact h.rank_lt u hu (by rwa [upd_of_ne _ huv] at hEu)
  · by_cases huv : u = v
    · rw [huv, upd_self]; omega
    · rw [upd_of_ne _ huv]
      have := hold u hu (by rwa [upd_of_ne _ huv] at hEu)
      omega
  · by_cases huv : u = v <;> by_cases hwv : w = v
    · rw [huv, hwv]
    · rw [huv, upd_self, upd_of_ne _ hwv] at hR
      have := hold w hw (by rwa [upd_of_ne _ hwv] at hEw)
      omega
    · rw [hwv, upd_self, upd_of_ne _ huv] at hR
      have := hold u hu (by rwa [upd_of_ne _ huv] at hEu)
      omega
    · rw [upd_of_ne _ huv, upd_of_ne _ hwv] at hR
      exact h.rank_inj u hu w hw (by rwa [upd_of_ne _ huv] at hEu)
        (by rwa [upd_of_ne _ hwv] at hEw) hR
  · -- a surviving degree drops by at most one
    have huv : u ≠ v := fun hc => by rw [hc, upd_self] at hEu; omega
    have hEu' : E u = 0 := by rwa [upd_of_ne _ huv] at hEu
    have hmin := h.min_le u hu hEu'
    by_cases hadj : MAdj G M u v
    · rw [hdec u hu hadj]; omega
    · rw [hkeep u hu hadj]; omega
  · -- the vertex just taken records the degree it had
    by_cases hwv : (w : ℕ) = v
    · have hwe : w = (⟨v, hv⟩ : Fin n) := Fin.ext hwv
      subst hwe
      rw [upd_self, upd_self, hself]
      rw [← h.deg ⟨v, hv⟩]
      exact hDv.symm
    · have hEw' : E (w : ℕ) = 1 := by rwa [upd_of_ne _ hwv] at hEw
      rw [upd_of_ne _ hwv, upd_of_ne _ hwv,
        hearlier _ (by have := hold (w : ℕ) w.isLt hEw'; omega)]
      exact h.taken w hEw'
  · -- and it was a minimum there
    by_cases hwv : (w : ℕ) = v
    · have hwe : w = (⟨v, hv⟩ : Fin n) := Fin.ext hwv
      subst hwe
      rw [upd_self] at huS
      rw [hself] at huS
      rw [upd_self, upd_self, hself, ← h.deg u]
      exact h.min_le (u : ℕ) u.isLt (mem_aliveF.1 huS)
    · have hEw' : E (w : ℕ) = 1 := by rwa [upd_of_ne _ hwv] at hEw
      have hlt : r < R (w : ℕ) + 1 := by have := hold (w : ℕ) w.isLt hEw'; omega
      rw [upd_of_ne _ hwv] at huS
      rw [hearlier _ hlt] at huS
      rw [upd_of_ne _ hwv, upd_of_ne _ hwv, hearlier _ hlt]
      exact h.mini w hEw' u huS
  · by_cases huv : u = v
    · rw [huv, upd_self]; exact le_max_right _ _
    · rw [upd_of_ne _ huv]
      exact le_trans (h.kmax_le u hu (by rwa [upd_of_ne _ huv] at hEu)) (le_max_left _ _)
  · rcases Nat.lt_or_ge mind kmax with hlt | hle
    · rcases h.kmax_att with h0 | ⟨w, hw, hEw, hIDw⟩
      · omega
      · have hwv : w ≠ v := fun hc => by rw [hc] at hEw; omega
        exact Or.inr ⟨w, hw, by rw [upd_of_ne _ hwv]; exact hEw,
          by rw [upd_of_ne _ hwv, hIDw, max_eq_left (le_of_lt hlt)]⟩
    · exact Or.inr ⟨v, hv, upd_self .., by rw [upd_self, max_eq_right hle]⟩

/-- **Moving the pointer up.** The bucket the pointer names is empty —
no surviving vertex has that degree — so the lower bound it carries
improves by one. Nothing else in the state changes. -/
theorem bump (h : Elim G M E D R ID cnt mind kmax)
    (hno : ∀ v < n, E v = 0 → D v ≠ mind) :
    Elim G M E D R ID cnt (mind + 1) kmax :=
  { h with
    min_le := fun v hv hE => by
      have := h.min_le v hv hE
      have := hno v hv hE
      omega }

/-! ### The exit

Once `cnt` has reached `n` every vertex carries a rank, the survivor
set of an extraction is a sublevel set of the rank, and the three
clauses of the certificate are the three clauses of the invariant read
at that point. -/

variable {mind kmax : ℕ}

/-- At the exit nothing is left. -/
theorem all_elim (h : Elim G M E D R ID n mind kmax) (v : Fin n) : E (v : ℕ) = 1 := by
  have huniv : pick (fun u : Fin n => E (u : ℕ) = 1) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [h.card_elim, Fintype.card_fin]
  exact mem_pick.1 (huniv ▸ Finset.mem_univ v)

/-- And the survivor set of an extraction is a sublevel set of the
rank, which is what the certificate speaks in. -/
theorem survOf_eq_surv (h : Elim G M E D R ID n mind kmax) (w : Fin n) :
    survOf (n := n) E R (R (w : ℕ) + 1) = surv (fun v : Fin n => R (v : ℕ)) (R (w : ℕ)) := by
  ext u
  rw [mem_survOf, mem_surv]
  have hu := h.all_elim u
  constructor
  · rintro (h0 | ⟨-, hlt⟩)
    · omega
    · omega
  · intro hle; exact Or.inr ⟨hu, by omega⟩

/-- **The certificate of the run.** Every clause of it is a clause of
the invariant, read once the loop has emptied. -/
theorem cert (h : Elim G M E D R ID n mind kmax) :
    ElimCert (masked G M) (fun v : Fin n => R (v : ℕ)) kmax := by
  have hcur : ∀ w : Fin n,
      curNbrs (masked G M) (fun v : Fin n => R (v : ℕ)) w
        = nbrsIn (masked G M) (survOf E R (R (w : ℕ) + 1)) w := by
    intro w; rw [curNbrs, h.survOf_eq_surv w]
  refine ⟨fun u v huv => ?_, fun w => ?_, ?_, fun w u hle => ?_⟩
  · exact Fin.ext (h.rank_inj (u : ℕ) u.isLt (v : ℕ) v.isLt (h.all_elim u) (h.all_elim v) huv)
  · rw [hcur w, ← h.taken w (h.all_elim w)]
    exact h.kmax_le (w : ℕ) w.isLt (h.all_elim w)
  · rcases h.kmax_att with h0 | ⟨w, hw, -, hIDw⟩
    · exact Or.inl h0
    · refine Or.inr ⟨⟨w, hw⟩, ?_⟩
      rw [hcur ⟨w, hw⟩, ← h.taken ⟨w, hw⟩ (h.all_elim ⟨w, hw⟩)]
      exact hIDw
  · rw [hcur w, ← h.taken w (h.all_elim w), ← h.survOf_eq_surv w]
    exact h.mini w (h.all_elim w) u (by rw [h.survOf_eq_surv w]; exact mem_surv.2 hle)

/-! ### Starting -/

/-- **The state the engine starts in**: nothing eliminated, the degree
array holding the true degrees of the arena, and both the pointer and
the bound at zero. -/
theorem init {E D R ID : ℕ → ℕ} (hE : ∀ v < n, E v = 0)
    (hD : ∀ v : Fin n, D (v : ℕ) = (nbrsIn (masked G M) Finset.univ v).card) :
    Elim G M E D R ID 0 0 0 := by
  have hal : aliveF (n := n) E = Finset.univ :=
    Finset.eq_univ_of_forall fun v => mem_aliveF.2 (hE (v : ℕ) v.isLt)
  refine ⟨fun v hv => by rw [hE v hv]; omega, Nat.zero_le _, ?_,
    fun v hv hEv => ?_, fun v hv hEv => ?_, fun v hv w hw hEv => ?_,
    fun v => by rw [hal]; exact hD v, fun v hv hEv => Nat.zero_le _,
    fun w hEw => ?_, fun w hEw => ?_, fun w hw hEw => ?_, Or.inl rfl⟩
  · rw [Finset.card_eq_zero]
    exact Finset.eq_empty_of_forall_notMem fun v hv => by
      have := mem_pick.1 hv
      rw [hE (v : ℕ) v.isLt] at this
      omega
  all_goals first
    | (exfalso; rw [hE v hv] at hEv; omega)
    | (exfalso; rw [hE w hw] at hEw; omega)
    | (exfalso; rw [hE (w : ℕ) w.isLt] at hEw; omega)

end Elim

/-! ### The in-neighbour lists

The third output. `InCsr` is `RamBfs.CsrGraph` for a *directed*
structure and with the block lengths pinned: the block of `w` names the
in-neighbours of `w`, and names each of them once, so the block length
is the in-degree and the whole array is as long as the number of
arcs. -/

/-- `InCsr D m IO IT`: the offsets `IO` and the targets `IT` list, block
by block, the in-neighbours of the orientation `D`, with `m` arcs in
all. -/
structure InCsr {n : ℕ} (D : Orientation n) (m : ℕ) (IO IT : ℕ → ℕ) : Prop where
  /-- The first block starts at the start of the arc array. -/
  zero : IO 0 = 0
  /-- The last block ends at its end. -/
  last : IO n = m
  /-- The offsets do not decrease, so they cut the array into blocks. -/
  mono : ∀ i < n, IO i ≤ IO (i + 1)
  /-- Every arc names a vertex. -/
  target_lt : ∀ j < m, IT j < n
  /-- The block of `w` names exactly the in-neighbours of `w`. -/
  mem_iff : ∀ w u : Fin n, u ∈ D.inN w ↔
    ∃ j, IO (w : ℕ) ≤ j ∧ j < IO ((w : ℕ) + 1) ∧ IT j = (u : ℕ)
  /-- And names each of them once, so the block length is the
  in-degree. -/
  len : ∀ w : Fin n, IO ((w : ℕ) + 1) - IO (w : ℕ) = (D.inN w).card

namespace InCsr

variable {D : Orientation n} {m : ℕ} {IO IT : ℕ → ℕ}

/-- The in-degree bound is visible in the offsets, which is the form a
consumer walking the blocks wants it in. -/
theorem block_le (h : InCsr D m IO IT) {k : ℕ} (hk : D.InDegLE k) (w : Fin n) :
    IO ((w : ℕ) + 1) - IO (w : ℕ) ≤ k := by
  rw [h.len w]; exact hk w

end InCsr

/-! ### The program

Thirteen arrays and sixteen scalars. Three of the arrays are the input
— the block structure `off`/`tgt` and the mask `alv` — three are the
output — `rnk`, `ioff`/`itg` — and the rest is the engine: the current
degrees `deg`, the elimination flags `elm`, the recorded extraction
degrees `idg`, the bucket heads `bh`, the arena `bv`/`bn` the bucket
stacks live in, and the fill pointers `ifl`.

Slot `0` of the arena is the sentinel, so `sp` starts at `1` and an
empty bucket reads `0` — which is what the machine's zeroed memory
already says, so no bucket has to be initialised. -/

/-- Push the vertex held in `x` onto the bucket the scalar `d` names:
one fresh slot of the arena, linked in front of the bucket's head. -/
def push (x : String) : Com :=
  .seq (.store "bv" (.var "sp") (.var x))
    (.seq (.store "bn" (.var "sp") (.get "bh" (.var "d")))
      (.seq (.store "bh" (.var "d") (.var "sp"))
        (.seq (.assign "sp" (.add (.var "sp") (.lit 1)))
          (.assign "ls" (.add (.var "ls") (.lit 1))))))

/-! #### The initial degrees

One pass over the block structure. A dead vertex is isolated in the
arena, so its degree is zero whatever its row says, and a live vertex
counts only its live neighbours. -/

/-- One slot of the counting scan. -/
def degSlot : Com :=
  .seq (.assign "u" (.get "tgt" (.var "j")))
    (.seq (.ite (.lt (.lit 0) (.get "alv" (.var "u")))
            (.assign "c" (.add (.var "c") (.lit 1))) .skip)
      (.assign "j" (.add (.var "j") (.lit 1))))

/-- One vertex's degree in the arena. -/
def degRow : Com :=
  .seq (.assign "c" (.lit 0))
    (.seq (Csr.loadRow "off" "i" "j" "jend")
      (.seq (Csr.scan "j" "jend" degSlot)
        (.seq (.ite (.lt (.lit 0) (.get "alv" (.var "i")))
                (.store "deg" (.var "i") (.var "c"))
                (.store "deg" (.var "i") (.lit 0)))
          (.assign "i" (.add (.var "i") (.lit 1))))))

/-- Every vertex's degree in the arena. -/
def initDeg : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "n")) degRow)

/-! #### The buckets, filled -/

/-- One vertex, put in the bucket of its degree. -/
def initBuckRow : Com :=
  .seq (.assign "d" (.get "deg" (.var "i")))
    (.seq (push "i") (.assign "i" (.add (.var "i") (.lit 1))))

/-- Every vertex, put in the bucket of its degree. -/
def initBuck : Com :=
  .seq (.assign "sp" (.lit 1))
    (.seq (.assign "ls" (.lit 0))
      (.seq (.assign "i" (.lit 0))
        (.while (.lt (.var "i") (.var "n")) initBuckRow)))

/-! #### The elimination -/

/-- One slot of the row of the vertex being eliminated: a neighbour
still in the arena loses one from its degree and is pushed into its new
bucket. The old slot is left where it is — that is what makes it a
lazily deleted queue — and `sc` counts the slots looked at, so that the
running time is a function of the environment. -/
def decSlot : Com :=
  .seq (.assign "u" (.get "tgt" (.var "j")))
    (.seq (.ite (.lt (.lit 0) (.get "alv" (.var "u")))
            (.ite (.lt (.get "elm" (.var "u")) (.lit 1))
              (.seq (.store "deg" (.var "u") (.sub (.get "deg" (.var "u")) (.lit 1)))
                (.seq (.assign "d" (.get "deg" (.var "u"))) (push "u")))
              .skip)
            .skip)
      (.seq (.assign "sc" (.add (.var "sc") (.lit 1)))
        (.assign "j" (.add (.var "j") (.lit 1)))))

/-- Eliminate the vertex held in `w`: stamp it with the next rank
*down*, record its extraction degree, and scan its row. A dead vertex
has no row to scan, since it is isolated in the arena. The pointer then
drops by one, since a decrement can only have produced a degree one
below the one just extracted. -/
def elimVertex : Com :=
  .seq (.store "elm" (.var "w") (.lit 1))
    (.seq (.store "rnk" (.var "w") (.sub (.sub (.var "n") (.lit 1)) (.var "cnt")))
      (.seq (.store "idg" (.var "w") (.var "mind"))
        (.seq (.assign "cnt" (.add (.var "cnt") (.lit 1)))
          (.seq (.ite (.lt (.var "kmax") (.var "mind"))
                  (.assign "kmax" (.var "mind")) .skip)
            (.seq (.ite (.lt (.lit 0) (.get "alv" (.var "w")))
                    (.seq (Csr.loadRow "off" "w" "j" "jend")
                      (Csr.scan "j" "jend" decSlot))
                    .skip)
              (.assign "mind" (.sub (.var "mind") (.lit 1))))))))

/-- One turn: move the pointer up over an empty bucket, or take the
head slot of the bucket it names and eliminate its vertex — unless the
slot is stale, its vertex having been eliminated already or moved to a
smaller bucket since, in which case the slot is simply dropped. -/
def elimTurn : Com :=
  .ite (.eq (.get "bh" (.var "mind")) (.lit 0))
    (.assign "mind" (.add (.var "mind") (.lit 1)))
    (.seq (.assign "p" (.get "bh" (.var "mind")))
      (.seq (.assign "w" (.get "bv" (.var "p")))
        (.seq (.store "bh" (.var "mind") (.get "bn" (.var "p")))
          (.seq (.assign "ls" (.sub (.var "ls") (.lit 1)))
            (.ite (.lt (.get "elm" (.var "w")) (.lit 1))
              (.ite (.eq (.get "deg" (.var "w")) (.var "mind")) elimVertex .skip)
              .skip)))))

/-- The elimination itself: turn after turn until every vertex has a
rank. -/
def elimLoop : Com :=
  .seq (.assign "mind" (.lit 0))
    (.seq (.assign "cnt" (.lit 0))
      (.seq (.assign "kmax" (.lit 0))
        (.seq (.assign "sc" (.lit 0))
          (.while (.lt (.var "cnt") (.var "n")) elimTurn))))

/-! #### The in-neighbour lists

Two more passes. The first turns the recorded extraction degrees into
offsets by a running sum, opening each vertex's block at the sum before
it; the second walks the whole block structure once more and writes
each arc into the block of the endpoint of *larger* rank, which is the
one eliminated first. -/

/-- One vertex's block, opened. -/
def offRow : Com :=
  .seq (.store "ifl" (.var "i") (.var "s"))
    (.seq (.assign "s" (.add (.var "s") (.get "idg" (.var "i"))))
      (.seq (.store "ioff" (.add (.var "i") (.lit 1)) (.var "s"))
        (.assign "i" (.add (.var "i") (.lit 1)))))

/-- The offsets of the in-neighbour lists. -/
def offPass : Com :=
  .seq (.store "ioff" (.lit 0) (.lit 0))
    (.seq (.assign "s" (.lit 0))
      (.seq (.assign "i" (.lit 0))
        (.while (.lt (.var "i") (.var "n")) offRow)))

/-- One slot of the fill: an arc of the arena is written into the block
of its endpoint of larger rank. -/
def fillSlot : Com :=
  .seq (.assign "u" (.get "tgt" (.var "j")))
    (.seq (.ite (.lt (.lit 0) (.get "alv" (.var "u")))
            (.ite (.lt (.get "rnk" (.var "u")) (.get "rnk" (.var "i")))
              (.seq (.store "itg" (.get "ifl" (.var "i")) (.var "u"))
                (.store "ifl" (.var "i") (.add (.get "ifl" (.var "i")) (.lit 1))))
              .skip)
            .skip)
      (.assign "j" (.add (.var "j") (.lit 1))))

/-- One vertex's in-neighbours, written out. -/
def fillRow : Com :=
  .seq (.ite (.lt (.lit 0) (.get "alv" (.var "i")))
          (.seq (Csr.loadRow "off" "i" "j" "jend") (Csr.scan "j" "jend" fillSlot))
          .skip)
    (.assign "i" (.add (.var "i") (.lit 1)))

/-- Every vertex's in-neighbours, written out. -/
def fillPass : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "n")) fillRow)

/-- **The whole engine**: the degrees, the buckets, the elimination, the
offsets, the fill. -/
def elimCom : Com :=
  .seq initDeg (.seq initBuck (.seq elimLoop (.seq offPass fillPass)))

/-! ### The specification

The block structure a *degree* is read off has to say one thing more
than the one a search reads: that a row lists each neighbour once. A
breadth-first search does not care — it relaxes the same vertex twice
and nothing happens — but a count does, so the engine's input surface
is `CsrGraph` with that clause added, and every caller that
materializes a graph in memory has it for nothing. -/

/-- A block structure that lists each neighbour once. -/
structure CsrSimple {n : ℕ} (G : SimpleGraph (Fin n)) (ns : ℕ) (O T : ℕ → ℕ) : Prop where
  /-- It is a block structure. -/
  csr : CsrGraph G ns O T
  /-- And no row names the same vertex twice. -/
  nodup : ∀ u < n, ∀ j₁ j₂, O u ≤ j₁ → j₁ < O (u + 1) → O u ≤ j₂ → j₂ < O (u + 1) →
    T j₁ = T j₂ → j₁ = j₂

/-- The slots of the row of `v` whose target is alive: what the
counting pass adds up. -/
def liveSlots (O T M : ℕ → ℕ) (v : ℕ) : Finset ℕ :=
  (Finset.Ico (O v) (O (v + 1))).filter (fun j => M (T j) ≠ 0)

theorem mem_liveSlots {O T M : ℕ → ℕ} {v j : ℕ} :
    j ∈ liveSlots O T M v ↔ (O v ≤ j ∧ j < O (v + 1)) ∧ M (T j) ≠ 0 := by
  rw [liveSlots, Finset.mem_filter, Finset.mem_Ico]

/-- **A dead vertex is isolated in the arena**, which is why the engine
needs no case for it: its degree is zero at every moment of the run,
and its row is never looked at. -/
theorem nbrsIn_of_dead {v : ℕ} (hv : v < n) (hM : M v = 0) :
    nbrsIn (masked G M) Finset.univ (⟨v, hv⟩ : Fin n) = ∅ :=
  Finset.eq_empty_of_forall_notMem fun u hu => by
    have := (masked_adj.1 (mem_nbrsIn.1 hu).2).2.2
    exact this hM

/-- **The row of a live vertex counts its degree in the arena.** The
slot-to-target map is a bijection from the live slots of the row onto
the neighbours in the arena: onto because a neighbour is named by some
slot, and injective because the row names each neighbour once — which
is the whole reason the input surface is `CsrSimple` and not
`CsrGraph`. -/
theorem card_liveSlots (h : CsrSimple G ns O T) {v : ℕ} (hv : v < n) (hM : M v ≠ 0) :
    (liveSlots O T M v).card = (nbrsIn (masked G M) Finset.univ (⟨v, hv⟩ : Fin n)).card := by
  classical
  refine Finset.card_bij (fun j hj => (⟨T j, h.csr.target_lt' hv (mem_liveSlots.1 hj).1.2⟩ : Fin n))
    (fun j hj => ?_) (fun j₁ hj₁ j₂ hj₂ he => ?_) (fun u hu => ?_)
  · obtain ⟨⟨h₁, h₂⟩, h₃⟩ := mem_liveSlots.1 hj
    exact mem_nbrsIn.2 ⟨Finset.mem_univ _,
      (h.csr.madj_of_slot hv h₁ h₂ hM h₃).symm.2.2⟩
  · exact h.nodup v hv j₁ j₂ (mem_liveSlots.1 hj₁).1.1 (mem_liveSlots.1 hj₁).1.2
      (mem_liveSlots.1 hj₂).1.1 (mem_liveSlots.1 hj₂).1.2 (congrArg Fin.val he)
  · obtain ⟨j, h₁, h₂, h₃⟩ :=
      h.csr.slot_of_madj (M := M) (((madj_iff (u := u) hv).2 (mem_nbrsIn.1 hu).2).symm)
    refine ⟨j, mem_liveSlots.2 ⟨⟨h₁, h₂⟩, ?_⟩, Fin.ext h₃⟩
    rw [h₃]
    exact (masked_adj.1 (mem_nbrsIn.1 hu).2).2.1

/-- **What the engine is handed.** The block structure, the mask, and
the eleven scratch arrays at their lengths — with the two the program
never initialises, the bucket heads and the elimination flags, required
zeroed, which is what the machine's own memory already says. -/
def ElimPre (n ns : ℕ) (O T M : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧
  σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧ σ.arrs "alv" = arrOf n M ∧
  (∃ g, σ.arrs "deg" = arrOf n g) ∧
  (∃ g, σ.arrs "elm" = arrOf n g ∧ ∀ j < n, g j = 0) ∧
  (∃ g, σ.arrs "rnk" = arrOf n g) ∧ (∃ g, σ.arrs "idg" = arrOf n g) ∧
  (∃ g, σ.arrs "bh" = arrOf (n + 1) g ∧ ∀ j ≤ n, g j = 0) ∧
  (∃ g, σ.arrs "bv" = arrOf (n + ns + 1) g) ∧ (∃ g, σ.arrs "bn" = arrOf (n + ns + 1) g) ∧
  (∃ g, σ.arrs "ioff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "ifl" = arrOf n g) ∧
  (∃ g, σ.arrs "itg" = arrOf ns g)

/-- **What the engine leaves**, in the vocabulary of the sections
above: the rank array carries a greedy elimination of the arena whose
bound is the scalar `kmax`, and the two in-list arrays carry the
orientation that elimination induces. -/
structure ElimOut {n : ℕ} (G : SimpleGraph (Fin n)) (M R IO IT : ℕ → ℕ) (k m : ℕ) : Prop where
  /-- The rank array is a greedy elimination with bound `k`. -/
  cert : ElimCert (masked G M) (fun v : Fin n => R (v : ℕ)) k
  /-- The in-lists are the elimination orientation. -/
  arcs : InCsr (ElimCert.elimOr (masked G M) (fun v : Fin n => R (v : ℕ))) m IO IT

/-- The memory postcondition: the three answers, at their lengths, with
`ElimOut` saying what they are. -/
def ElimMem {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (ns : ℕ) (_σ σ' : Env) : Prop :=
  ∃ (R IO IT : ℕ → ℕ) (k m : ℕ), σ'.arrs "rnk" = arrOf n R ∧ σ'.vars "kmax" = k ∧
    σ'.arrs "ioff" = arrOf (n + 1) IO ∧ σ'.arrs "itg" = arrOf ns IT ∧ m ≤ ns ∧
    ElimOut G M R IO IT k m

/-- **The five postconditions**, spelled out: the rank is a ranking;
there is an orientation of the arena with in-degree at most `k` whose
in-neighbours are the neighbours of smaller rank and whose underlying
graph is the arena itself; the rank is `BackDegLE`-good for the same
`k`, on the arena and on the orientation's graph alike, so the arena is
`k`-degenerate; `k` is at most every bound a `LowDegreeVertices`
argument can produce; and the in-lists encode the orientation. The
fifth — the running time — is the `Spec`'s own cost. -/
def ElimPost {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (ns : ℕ) (_σ σ' : Env) : Prop :=
  ∃ (R IO IT : ℕ → ℕ) (k m : ℕ) (E : Orientation n),
    σ'.arrs "rnk" = arrOf n R ∧ σ'.vars "kmax" = k ∧
    σ'.arrs "ioff" = arrOf (n + 1) IO ∧ σ'.arrs "itg" = arrOf ns IT ∧ m ≤ ns ∧
    Function.Injective (fun v : Fin n => R (v : ℕ)) ∧
    E.Orients (masked G M) ∧ E.InDegLE k ∧
    (∀ u w : Fin n, u ∈ E.inN w ↔ (masked G M).Adj u w ∧ R (u : ℕ) < R (w : ℕ)) ∧
    E.toGraph = masked G M ∧
    BackDegLE (masked G M) (fun v : Fin n => R (v : ℕ)) k ∧
    BackDegLE E.toGraph (fun v : Fin n => R (v : ℕ)) k ∧
    DegeneracyLE (masked G M) k ∧
    (∀ k', LowDegreeVertices (masked G M) k' → k ≤ k') ∧
    InCsr E m IO IT

/-- **The five postconditions come off the certificate.** Nothing in
this proof knows about the program: it is `ElimCert`'s section, read
once. -/
theorem elimPost_of_elimMem {σ σ' : Env} (h : ElimMem G M ns σ σ') : ElimPost G M ns σ σ' := by
  obtain ⟨R, IO, IT, k, m, hrnk, hk, hioff, hitg, hm, hout⟩ := h
  exact ⟨R, IO, IT, k, m, ElimCert.elimOr (masked G M) (fun v : Fin n => R (v : ℕ)),
    hrnk, hk, hioff, hitg, hm, hout.cert.inj, hout.cert.orients, hout.cert.inDegLE,
    fun u w => ElimCert.mem_elimOr, hout.cert.toGraph_eq, hout.cert.backDegLE,
    hout.cert.backDegLE_toGraph, hout.cert.degeneracyLE,
    fun _ hk' => hout.cert.le_of_lowDegreeVertices hk', hout.arcs⟩

/-- The running time: five passes over the block structure and the
buckets, each linear. The constants are generous — the shape is what
the campaign's budget is spent against, and the sharp charging is a
later phase's business. -/
def elimCost (n ns : ℕ) : ℕ := 600 * n + 600 * ns + 100

/-! ### The phases, walked

Each phase is a `Spec` of its own, proved by `run_vcg` against an
invariant of its own. The mathematics is already done — `Elim`'s three
turns, `card_liveSlots`, `Elim.cert` — so what is left in this section
is symbolic execution and the arithmetic of the array bounds. -/

/-! #### The degrees

One pass over the block structure, its inner loop the kit's row scan.
What the scan counts is `liveUpto`, the live slots of the row seen so
far; what `card_liveSlots` then says is that the whole row's count is
the arena degree, which is exactly `Elim.init`'s second hypothesis. -/

/-- The arena degree of a vertex, at the number level the program
speaks. -/
noncomputable def adeg {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (v : ℕ) : ℕ :=
  if h : v < n then (nbrsIn (masked G M) Finset.univ ⟨v, h⟩).card else 0

theorem adeg_eq {v : ℕ} (hv : v < n) :
    adeg G M v = (nbrsIn (masked G M) Finset.univ (⟨v, hv⟩ : Fin n)).card := dif_pos hv

/-- A dead vertex has degree zero, being isolated in the arena. -/
theorem adeg_of_dead {v : ℕ} (hv : v < n) (hM : M v = 0) : adeg G M v = 0 := by
  rw [adeg_eq hv, nbrsIn_of_dead hv hM, Finset.card_empty]

/-- And a live one has as many as its row has live slots. -/
theorem adeg_of_alive (h : CsrSimple G ns O T) {v : ℕ} (hv : v < n) (hM : M v ≠ 0) :
    adeg G M v = (liveSlots O T M v).card := by
  rw [adeg_eq hv, card_liveSlots h hv hM]

/-- The live slots of the row of `v` strictly below `j`: what the
counting scan has added up when its pointer stands at `j`. -/
def liveUpto (O T M : ℕ → ℕ) (v j : ℕ) : ℕ :=
  ((Finset.Ico (O v) j).filter (fun t => M (T t) ≠ 0)).card

@[simp] theorem liveUpto_start (O T M : ℕ → ℕ) (v : ℕ) : liveUpto O T M v (O v) = 0 := by
  simp [liveUpto]

theorem liveUpto_succ (O T M : ℕ → ℕ) {v j : ℕ} (h : O v ≤ j) :
    liveUpto O T M v (j + 1) = liveUpto O T M v j + (if M (T j) ≠ 0 then 1 else 0) := by
  classical
  have hins : Finset.Ico (O v) (j + 1) = insert j (Finset.Ico (O v) j) := by
    ext x; simp only [Finset.mem_insert, Finset.mem_Ico]; omega
  rw [liveUpto, liveUpto, hins, Finset.filter_insert]
  by_cases hm : M (T j) ≠ 0
  · rw [if_pos hm, if_pos hm,
      Finset.card_insert_of_notMem (by simp [Finset.mem_filter])]
  · rw [if_neg hm, if_neg hm, Nat.add_zero]

theorem liveUpto_last (O T M : ℕ → ℕ) (v : ℕ) :
    liveUpto O T M v (O (v + 1)) = (liveSlots O T M v).card := rfl

/-- The invariant of the degree pass: the input arrays are untouched,
the counter has not passed the end, and every degree below it is the
arena degree. -/
def DegInv (n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
    σ.arrs "alv" = arrOf n M ∧ σ.vars "i" ≤ n ∧
    ∃ g, σ.arrs "deg" = arrOf n g ∧ ∀ j < σ.vars "i", g j = adeg G M j

/-- The invariant of the counting scan: a degree pass in progress, and
the row of `v` counted as far as the pointer. -/
def DegScanInv (n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M : ℕ → ℕ) (v : ℕ) (σ : Env) : Prop :=
  DegInv n ns G O T M σ ∧ σ.vars "i" = v ∧ σ.vars "jend" = O (v + 1) ∧
    O v ≤ σ.vars "j" ∧ σ.vars "j" ≤ O (v + 1) ∧
    σ.vars "c" = liveUpto O T M v (σ.vars "j")

/-- One slot of the counting scan: a live target is counted, a dead one
passed over. Written in the `_run` form the kit's row scan consumes,
with every obligation of the walk pre-loaded as a named hypothesis —
`RamBfs.scanSlot_run`'s shape, and for its reason. -/
theorem degSlot_run {B n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ} {v : ℕ}
    (hcsr : CsrGraph G ns O T) (hv : v < n) (hnB : n < B) (hnsB : ns < B)
    (hMB : ∀ z < n, M z < B) {σ : Env}
    (hI : DegScanInv n ns G O T M v σ) (hjlt : σ.vars "j" < O (v + 1)) :
    ∃ σ' K, Run B degSlot σ σ' K ∧ K ≤ 40 ∧
      DegScanInv n ns G O T M v σ' ∧ σ'.vars "j" = σ.vars "j" + 1 := by
  obtain ⟨⟨hn, hoff, htgt, halv, hile, ⟨g, hdeg, hg⟩⟩, hi, hje, hj₁, hj₂, hc⟩ := hI
  have hns : O (v + 1) ≤ ns := hcsr.le_ns (by omega)
  have hjns : σ.vars "j" < ns := by omega
  have htv : (σ.arrs "tgt").getD (σ.vars "j") 0 = T (σ.vars "j") := by
    rw [htgt, getD_arrOf T hjns]
  have htv' : (σ.arrs "tgt")[σ.vars "j"]?.getD 0 = T (σ.vars "j") := by
    rw [← List.getD_eq_getElem?_getD]; exact htv
  have htn : T (σ.vars "j") < n := hcsr.target_lt _ hjns
  have hjlen : σ.vars "j" < (σ.arrs "tgt").length := by rw [htgt, length_arrOf]; omega
  have htB : (σ.arrs "tgt").getD (σ.vars "j") 0 < B := by rw [htv]; exact lt_trans htn hnB
  -- the mask read, in the environment the branch tests it in
  have halvlen : ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).vars "u")
      < ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).arrs "alv").length := by
    rw [arrs_setVar, vars_setVar, halv, length_arrOf]; simpa [htv'] using htn
  have hbrAlv : ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).arrs "alv").getD
      ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).vars "u") 0
      = M (T (σ.vars "j")) := by
    rw [arrs_setVar, vars_setVar]; simpa [htv', halv] using getD_arrOf M htn
  have hbrAlvB : ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).arrs "alv").getD
      ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).vars "u") 0 < B := by
    rw [hbrAlv]; exact hMB _ htn
  -- the counter stays inside the target array, so it is a word
  have hcns : σ.vars "c" < ns := by
    rw [hc, liveUpto]
    calc ({t ∈ Finset.Ico (O v) (σ.vars "j") | M (T t) ≠ 0} : Finset ℕ).card
        ≤ (Finset.Ico (O v) (σ.vars "j")).card := Finset.card_filter_le _ _
      _ < ns := by rw [Nat.card_Ico]; omega
  have hcB : σ.vars "c" + 1 < B := by omega
  have hjB : σ.vars "j" + 1 < B := by omega
  run_vcg
  · -- a live target is counted
    have hm : M (T (σ.vars "j")) ≠ 0 := by omega
    exact ⟨⟨⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv], by simp [hile],
      ⟨g, by simp [hdeg], by simpa using hg⟩⟩, by simp [hi], by simp [hje], by simp; omega,
      by simp; omega, by simp [hc, liveUpto_succ O T M hj₁, hm]⟩, by simp⟩
  · -- a dead target is passed over
    have hm : M (T (σ.vars "j")) = 0 := by omega
    exact ⟨⟨⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv], by simp [hile],
      ⟨g, by simp [hdeg], by simpa using hg⟩⟩, by simp [hi], by simp [hje], by simp; omega,
      by simp; omega, by simp [hc, liveUpto_succ O T M hj₁, hm]⟩, by simp⟩

/-- **One vertex's degree.** The row is walked by the kit's row scan —
the caller says what a slot does and the combinator supplies the loop
condition, the exit fact and the cost — and what the row counted is the
arena degree by `card_liveSlots`, or zero if the vertex is dead. -/
theorem degRow_run {B n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ} {v : ℕ}
    (hcsr : CsrSimple G ns O T) (hv : v < n) (hnB : n + 1 < B) (hnsB : ns < B)
    (hMB : ∀ z < n, M z < B) {σ : Env}
    (hI : DegInv n ns G O T M σ) (hiv : σ.vars "i" = v) :
    ∃ σ' K, Run B degRow σ σ' K ∧ K ≤ 44 * Csr.rowLen O v + 40 ∧
      DegInv n ns G O T M σ' ∧ σ'.vars "i" = v + 1 := by
  obtain ⟨hn, hoff, htgt, halv, hile, ⟨g, hdeg, hg⟩⟩ := id hI
  have hns : O (v + 1) ≤ ns := hcsr.csr.le_ns (by omega)
  have hov : O v ≤ O (v + 1) := hcsr.csr.mono v hv
  have hrow : Csr.rowLen O v = O (v + 1) - O v := rfl
  have hMv : M v < B := hMB v hv
  have hcsrRel : Csr "off" "tgt" n ns n O T σ :=
    ⟨hoff, htgt, fun i hi => hcsr.csr.mono i hi, hcsr.csr.last,
      fun p hp => hcsr.csr.target_lt p hp⟩
  -- the count the row ends at, and that it is the arena degree
  have hcard : (liveSlots O T M v).card ≤ ns := by
    calc (liveSlots O T M v).card ≤ (Finset.Ico (O v) (O (v + 1))).card :=
          Finset.card_filter_le _ _
      _ ≤ ns := by rw [Nat.card_Ico]; omega
  -- the scan, stated so that what it hands back is what the rest of the block owes
  have hscanSpec : Spec B
      (fun τ => DegScanInv n ns G O T M v τ ∧ τ.vars "j" = O v)
      (Csr.scan "j" "jend" degSlot)
      (fun _ τ' => (∃ f, τ'.arrs "deg" = arrOf n f ∧ ∀ j < v, f j = adeg G M j) ∧
        τ'.vars "n" = n ∧ τ'.arrs "off" = arrOf (n + 1) O ∧ τ'.arrs "tgt" = arrOf ns T ∧
        τ'.arrs "alv" = arrOf n M ∧ τ'.vars "i" = v ∧
        τ'.vars "c" = (liveSlots O T M v).card ∧
        τ'.vars "i" < (τ'.arrs "alv").length ∧
        (τ'.arrs "alv").getD (τ'.vars "i") 0 = M v ∧
        (τ'.arrs "alv").getD (τ'.vars "i") 0 < B ∧
        τ'.vars "i" < (τ'.arrs "deg").length ∧
        τ'.vars "c" < B ∧ τ'.vars "i" + 1 < B ∧ τ'.vars "i" < B)
      (44 * Csr.rowLen O v + 4) := by
    refine (Csr.rowScan_spec B (44 * Csr.rowLen O v + 4) (O (v + 1)) 40 "j" "jend" degSlot
      (DegScanInv n ns G O T M v) (by omega) (fun τ hτ => ⟨hτ.2.2.1, hτ.2.2.2.2.1⟩)
      (fun τ hτ hlt => ?_) (fun _ hτ => hτ.1)
      (fun τ hτ => by rw [hτ.2]; omega)).post (fun _ τ' _ hQ => ?_)
    · obtain ⟨τ', K', hr, hK', hI', hj'⟩ :=
        degSlot_run hcsr.csr hv (by omega) hnsB hMB hτ hlt
      exact ⟨τ', K', hr, hI', hj', hK'⟩
    · obtain ⟨⟨hn', hoff', htgt', halv', hile', ⟨f, hdeg', hf'⟩⟩, hi', -, -, -, hc'⟩ := hQ.1
      have hjend := hQ.2
      rw [hjend, liveUpto_last] at hc'
      have hivn : τ'.vars "i" < n := by rw [hi']; exact hv
      exact ⟨⟨f, hdeg', fun j hj => hf' j (by rw [hi']; exact hj)⟩, hn', hoff', htgt', halv',
        hi', hc', by rw [halv', length_arrOf]; exact hivn,
        by rw [halv', getD_arrOf M hivn, hi'], by rw [halv', getD_arrOf M hivn, hi']; exact hMv,
        by rw [hdeg', length_arrOf]; exact hivn, by rw [hc']; omega,
        by rw [hi']; omega, by rw [hi']; omega⟩
  run_vcg [Csr.loadRow_spec B n ns n "off" "tgt" "i" "j" "jend" O T (by decide) (by decide),
    hscanSpec]
  · -- a live vertex records what its row counted
    obtain ⟨⟨f, hdeg', hf'⟩, hn', hoff', htgt', halv', hi', hc', -, hav, -, -, -, -, -⟩ :=
      ‹(∃ f, _) ∧ _›
    have hMvne : M v ≠ 0 := by
      have := ‹0 < (_ : List ℕ).getD _ 0›
      omega
    refine ⟨⟨by simp [hn'], by simp [hoff'], by simp [htgt'], by simp [halv'],
      by simp [hi']; omega, ⟨upd f v (adeg G M v), ?_, fun j hj => ?_⟩⟩, by simp [hi']⟩
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, hdeg', hi', hc',
        ← adeg_of_alive hcsr hv hMvne, set_arrOf_eq_upd]
    · simp only [vars_setVar, if_true, vars_setArr, hi'] at hj
      rcases Nat.lt_or_ge j v with hj' | hj'
      · rw [upd_of_ne _ (by omega)]; exact hf' j hj'
      · rw [show j = v by omega, upd_self]
  · -- a dead vertex is isolated, and records nothing
    obtain ⟨⟨f, hdeg', hf'⟩, hn', hoff', htgt', halv', hi', hc', -, hav, -, -, -, -, -⟩ :=
      ‹(∃ f, _) ∧ _›
    have hMv0 : M v = 0 := by
      have := ‹¬ (0 < (_ : List ℕ).getD _ 0)›
      omega
    refine ⟨⟨by simp [hn'], by simp [hoff'], by simp [htgt'], by simp [halv'],
      by simp [hi']; omega, ⟨upd f v (adeg G M v), ?_, fun j hj => ?_⟩⟩, by simp [hi']⟩
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, hdeg', hi',
        show (0 : ℕ) = adeg G M v from (adeg_of_dead hv hMv0).symm, set_arrOf_eq_upd]
    · simp only [vars_setVar, if_true, vars_setArr, hi'] at hj
      rcases Nat.lt_or_ge j v with hj' | hj'
      · rw [upd_of_ne _ (by omega)]; exact hf' j hj'
      · rw [show j = v by omega, upd_self]
  · -- the two offset reads: a row of the structure, and its number a word
    exact ⟨⟨by simpa using hcsrRel, by omega, hnsB⟩, by simp [hiv]; omega,
      by simp [hiv]; omega⟩
  · -- the scan starts at the top of the row, in the state the reads left
    obtain ⟨-, hj', hje', rfl⟩ :=
      ‹Csr.LoadRowPost "off" "tgt" "i" "j" "jend" n ns n O T _ _›
    refine ⟨⟨⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv],
      by simp [hile], ⟨g, by simp [hdeg], by simpa [hiv] using hg⟩⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp [hiv, hov]

/-- **Every vertex's degree in the arena.** The pass is amortized, not
counted: a turn costs the length of the row it walks, and the rows tile
the target array, so the potential is "so much per slot left, so much
per vertex left" and the whole pass is linear. -/
theorem initDeg_spec (B n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M : ℕ → ℕ)
    (hcsr : CsrSimple G ns O T) (hnB : n + 1 < B) (hnsB : ns < B) (hMB : ∀ z < n, M z < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧
        σ.arrs "tgt" = arrOf ns T ∧ σ.arrs "alv" = arrOf n M ∧
        (∃ g, σ.arrs "deg" = arrOf n g))
      initDeg
      (fun _ σ' => DegInv n ns G O T M σ' ∧ σ'.vars "i" = n)
      (48 * n + 44 * ns + 10) := by
  have hOle : ∀ i ≤ n, O i ≤ ns := fun i hi => hcsr.csr.le_ns hi
  have hloop : Spec B (DegInv n ns G O T M)
      (.while (.lt (.var "i") (.var "n")) degRow)
      (fun _ σ' => DegInv n ns G O T M σ' ∧
        (Cond.lt (Expr.var "i") (Expr.var "n")).evalB B σ' = some false)
      (48 * n + 44 * ns + 8) := by
    refine Spec.while_potential (DegInv n ns G O T M)
      (fun σ => 44 * (ns - O (σ.vars "i")) + 48 * (n - σ.vars "i"))
      (fun σ hσ => evalB_condLt_vars (by have := hσ.2.2.2.2.1; omega)
        (by rw [hσ.1]; omega))
      (fun σ hσ hb => ?_) (fun _ h => h)
      (fun σ _ => by simp only [size_condLt, size_var]; omega)
    have hlt : σ.vars "i" < n := by
      have := lt_of_condLt_true hb
      rw [hσ.1] at this; exact this
    obtain ⟨σ', K, hrun, hK, hI', hi'⟩ :=
      degRow_run hcsr hlt hnB hnsB hMB hσ rfl
    refine ⟨σ', K, hrun, hI', ?_⟩
    have h₁ : O (σ.vars "i") ≤ O (σ.vars "i" + 1) := hcsr.csr.mono _ hlt
    have h₂ : O (σ.vars "i" + 1) ≤ ns := hOle _ (by omega)
    have hrow : Csr.rowLen O (σ.vars "i") = O (σ.vars "i" + 1) - O (σ.vars "i") := rfl
    simp only [size_condLt, size_var, hi']
    omega
  run_vcg [hloop]
  · -- the loop's exit reading
    obtain ⟨hI', hfalse⟩ := ‹DegInv n ns G O T M _ ∧ _›
    have h₁ := le_of_condLt_false hfalse
    exact ⟨hI', by have := hI'.1; have := hI'.2.2.2.2.1; omega⟩
  · -- the pass starts with nothing filled in
    obtain ⟨g, hdeg⟩ := ‹∃ g, σ.arrs "deg" = arrOf n g›
    exact ⟨by simpa using ‹σ.vars "n" = n›, by simpa using ‹σ.arrs "off" = arrOf (n + 1) O›,
      by simpa using ‹σ.arrs "tgt" = arrOf ns T›, by simpa using ‹σ.arrs "alv" = arrOf n M›,
      by simp, ⟨g, by simpa using hdeg, fun j hj => absurd hj (by simp)⟩⟩

/-- Where the block of vertex `i` starts: the recorded extraction
degrees of everything before it. -/
def psum (ID : ℕ → ℕ) (i : ℕ) : ℕ := ∑ t ∈ Finset.range i, ID t

@[simp] theorem psum_zero (ID : ℕ → ℕ) : psum ID 0 = 0 := by simp [psum]

theorem psum_succ (ID : ℕ → ℕ) (i : ℕ) : psum ID (i + 1) = psum ID i + ID i :=
  Finset.sum_range_succ ID i

theorem psum_mono (ID : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : psum ID i ≤ psum ID j := by
  refine Finset.sum_le_sum_of_subset ?_
  exact Finset.range_subset_range.2 h

/-- The invariant of the offset pass: the running sum is in `s`, the
blocks up to the counter are opened in `ioff`, and the fill pointers
below it are at the starts of their blocks. -/
def OffInv (n : ℕ) (ID : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs "idg" = arrOf n ID ∧ σ.vars "i" ≤ n ∧
    σ.vars "s" = psum ID (σ.vars "i") ∧
    (∃ g, σ.arrs "ioff" = arrOf (n + 1) g ∧ ∀ j ≤ σ.vars "i", g j = psum ID j) ∧
    (∃ g, σ.arrs "ifl" = arrOf n g ∧ ∀ j < σ.vars "i", g j = psum ID j)

/-- One vertex's block, opened. -/
theorem offRow_spec (B n : ℕ) (ID : ℕ → ℕ) (hnB : n + 1 < B) (hsB : psum ID n < B) :
    Spec B (fun σ => OffInv n ID σ ∧ σ.vars "i" < n) offRow
      (fun σ σ' => OffInv n ID σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 20 := by
  refine Spec.pre (P := fun σ => (OffInv n ID σ ∧ σ.vars "i" < n) ∧
      σ.vars "i" < (σ.arrs "ifl").length ∧ σ.vars "i" < (σ.arrs "idg").length ∧
      σ.vars "i" + 1 < (σ.arrs "ioff").length ∧
      (σ.arrs "idg").getD (σ.vars "i") 0 = ID (σ.vars "i") ∧
      (σ.arrs "idg").getD (σ.vars "i") 0 < B ∧
      σ.vars "i" + 1 < B ∧ σ.vars "s" < B ∧
      σ.vars "s" + (σ.arrs "idg").getD (σ.vars "i") 0 < B) ?_ ?_
  · run_vcg
    · obtain ⟨hn, hidg, -, hs, ⟨g, hioff, hg⟩, ⟨f, hifl, hf⟩⟩ := ‹OffInv n ID σ›
      have hlt : σ.vars "i" < n := ‹σ.vars "i" < n›
      have hv : (σ.arrs "idg").getD (σ.vars "i") 0 = ID (σ.vars "i") := ‹_›
      have hv' : (σ.arrs "idg")[σ.vars "i"]?.getD 0 = ID (σ.vars "i") := by
        rw [← List.getD_eq_getElem?_getD]; exact hv
      refine ⟨⟨by simp [hn], by simp [hidg], by simp; omega,
        by simp [hs, hv', psum_succ],
        ⟨upd g (σ.vars "i" + 1) (psum ID (σ.vars "i" + 1)),
          by simp [hioff, hs, hv', psum_succ, set_arrOf_eq_upd], fun j hj => ?_⟩,
        ⟨upd f (σ.vars "i") (psum ID (σ.vars "i")),
          by simp [hifl, hs, set_arrOf_eq_upd], fun j hj => ?_⟩⟩, by simp⟩
      · simp at hj
        rcases Nat.lt_or_ge j (σ.vars "i" + 1) with hj' | hj'
        · rw [upd_of_ne _ (by omega)]; exact hg j (by omega)
        · rw [show j = σ.vars "i" + 1 by omega, upd_self]
      · simp at hj
        rcases Nat.lt_or_ge j (σ.vars "i") with hj' | hj'
        · rw [upd_of_ne _ (by omega)]; exact hf j hj'
        · rw [show j = σ.vars "i" by omega, upd_self]
    · simpa using ‹(σ.arrs "idg").getD (σ.vars "i") 0 < B›
    · simpa using ‹σ.vars "s" + (σ.arrs "idg").getD (σ.vars "i") 0 < B›
    · simpa using ‹σ.vars "s" + (σ.arrs "idg").getD (σ.vars "i") 0 < B›
  · rintro σ ⟨⟨hn, hidg, hile, hs, ⟨g, hioff, hg⟩, ⟨f, hifl, hf⟩⟩, hlt⟩
    -- (the pre-loading of the walk's obligations; see shape note 5)
    have hidgv : (σ.arrs "idg").getD (σ.vars "i") 0 = ID (σ.vars "i") := by
      rw [hidg, getD_arrOf ID hlt]
    have hstep : psum ID (σ.vars "i") + ID (σ.vars "i") = psum ID (σ.vars "i" + 1) :=
      (psum_succ ID _).symm
    have hle1 : psum ID (σ.vars "i" + 1) ≤ psum ID n := psum_mono ID (by omega)
    refine ⟨⟨⟨hn, hidg, hile, hs, ⟨g, hioff, hg⟩, ⟨f, hifl, hf⟩⟩, hlt⟩,
      by rw [hifl, length_arrOf]; omega, by rw [hidg, length_arrOf]; omega,
      by rw [hioff, length_arrOf]; omega, hidgv, ?_, by omega, ?_, ?_⟩
    · rw [hidgv]
      have : ID (σ.vars "i") ≤ psum ID (σ.vars "i" + 1) := by rw [psum_succ]; omega
      omega
    · rw [hs]; have := psum_mono ID (le_of_lt hlt : σ.vars "i" ≤ n); omega
    · rw [hidgv, hs]; omega

/-- What the offset pass is handed: the recorded extraction degrees and
the two arrays it writes, at their lengths. -/
def OffPre (n : ℕ) (ID : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs "idg" = arrOf n ID ∧
    (∃ g, σ.arrs "ioff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "ifl" = arrOf n g)

/-- **The offsets of the in-neighbour lists.** A running sum: every
block is opened at the sum of the extraction degrees before it, and
every fill pointer starts at the start of its own block. -/
theorem offPass_spec (B n : ℕ) (ID : ℕ → ℕ) (hnB : n + 1 < B) (hsB : psum ID n < B) :
    Spec B (OffPre n ID) offPass
      (fun _ σ' => σ'.vars "n" = n ∧ σ'.vars "s" = psum ID n ∧
        (∃ g, σ'.arrs "ioff" = arrOf (n + 1) g ∧ ∀ j ≤ n, g j = psum ID j) ∧
        (∃ g, σ'.arrs "ifl" = arrOf n g ∧ ∀ j < n, g j = psum ID j))
      (24 * n + 12) := by
  have hloop : Spec B (fun σ => OffInv n ID (σ.setVar "i" 0))
      (.seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "n")) offRow))
      (fun _ σ' => OffInv n ID σ' ∧ σ'.vars "i" = n) ((20 + 4) * n + 6) :=
    Spec.forRangeZero "i" "n" (OffInv n ID) n 20 (by omega)
      (fun _ h => h.2.2.1) (fun _ h => h.1) (offRow_spec B n ID hnB hsB)
  run_vcg [hloop]
  · -- the loop's exit, read as this phase's answer
    obtain ⟨⟨hn, -, -, hs, hio, hif⟩, hi⟩ := ‹OffInv n ID _ ∧ _›
    rw [hi] at hs hio hif
    exact ⟨hn, hs, hio, hif⟩
  · -- the one store is inside the offsets array
    obtain ⟨-, -, ⟨g, hioff⟩, -⟩ := ‹OffPre n ID σ›
    rw [hioff, length_arrOf]; omega
  · -- the loop starts with an empty sum and the first block opened
    obtain ⟨hn, hidg, ⟨g, hioff⟩, ⟨f, hifl⟩⟩ := ‹OffPre n ID σ›
    refine ⟨by simp [hn], by simp [hidg], by simp, by simp,
      ⟨upd g 0 0, by simp [hioff, set_arrOf_eq_upd], fun j hj => ?_⟩,
      ⟨f, by simp [hifl], fun j hj => absurd hj (by simp)⟩⟩
    simp at hj
    rw [hj, upd_self, psum_zero]

/-- **The one thing this file leaves open.** `elimCom` is exhibited,
compiled and run — the worked example below checks its answers against
the arithmetic on the other side of the abstraction — and everything
its answers *mean* is proved above, in `ElimCert` and `InCsr`. What is
isolated here is the Hoare triple itself: that the five phases of the
program leave memory in the state `ElimMem` describes, within the cost
`elimCost`. It is stated over the program text and the input surface a
caller has, so it is a self-contained obligation and not a hole in a
statement: the invariant it is to be proved against is `Elim`, its
three turns are `Elim.init`, `Elim.bump` and `Elim.extract`, and its
exit reading is `Elim.cert`.

It splits along the program's five phases, each a `Spec` of its own.
**Two of the five are discharged** in the section above and are no
longer part of this obligation; the three that remain are named here
with what each of them needs.

* `initDeg` — **done**, `initDeg_spec`: it leaves `deg v` at the arena
  degree of `v`, at a cost of `48 n + 44 ns + 10`. Its content is
  `card_liveSlots` — the row's live slots biject with the arena
  neighbours — and `adeg_of_dead` for the other branch, and its result
  is exactly `Elim.init`'s second hypothesis. The outer loop is
  amortized against `44 (ns − off i) + 48 (n − i)`, the rows tiling the
  target array.
* `offPass` — **done**, `offPass_spec`: a running sum, at a cost of
  `24 n + 12`, leaving `ioff j = psum ID j` for every `j ≤ n` and every
  fill pointer at the start of its own block. It establishes `InCsr`'s
  `zero`, `last`, `mono` and `len`.
* `initBuck` — **open**: fills the buckets and leaves `sp = n + 1`,
  `ls = n`. Its content is the bucket relation, which the elimination
  loop then carries.
* `elimLoop` — **open**: the loop, against `Elim` plus that bucket
  relation; its exit is `cnt = n`, where `Elim.cert` applies.
* `fillPass` — **open**: a second walk of the block structure whose
  content is a counting sort — each arc lands in the block of its
  larger-ranked endpoint — giving `InCsr`'s `mem_iff` and `target_lt`.

The two open bucket phases both wait on the same missing piece: a
reachability relation for the lazily deleted stacks (`q` is on the
chain of `bh d` under `bn`), with the invariant that an allocated slot
points strictly downwards, so that a push in front of a head and a pop
of a head can both be shown to preserve "every uneliminated vertex has
a slot in the bucket of its degree" — the clause `Elim.bump` consumes.
Nothing above depends on it.

The cost is amortized, with the potential

    c_m · (n + 1 − mind) + c_p · ls + c_s · (ns − sc) + c_e · (n − cnt)

for the loop: a pointer bump is paid out of the first term, a stale pop
out of the second, an extraction's row scan out of the third, and the
extraction itself out of the fourth, which also refunds the one the
pointer's drop costs. The pointer never runs away because `Elim.min_le`
plus an empty bucket forces it below every surviving degree, and the
arena never overflows because a slot is pushed once per vertex and once
per scanned slot. -/
def Implements (B n ns : ℕ) (G : SimpleGraph (Fin n)) (M O T : ℕ → ℕ) : Prop :=
  CsrSimple G ns O T → n + ns + 1 < B → (∀ z < n, M z < B) →
    Spec B (ElimPre n ns O T M) elimCom (ElimMem G M ns) (elimCost n ns)

/-- **Greedy minimum-degree elimination over a masked block
structure.** Handed a block structure for `G` that lists each
neighbour once, a mask, and the scratch arrays at their lengths,
`elimCom` leaves in `rnk` a ranking of the arena, in `kmax` the
degeneracy bound the greedy run achieved — at most every bound a
density argument can produce — and in `ioff`/`itg` the orientation of
the arena towards the endpoint eliminated first, whose in-degrees that
same bound bounds. -/
theorem elim_spec {B : ℕ} (h : Implements B n ns G M O T) (hcsr : CsrSimple G ns O T)
    (hB : n + ns + 1 < B) (hMB : ∀ z < n, M z < B) :
    Spec B (ElimPre n ns O T M) elimCom (ElimPost G M ns) (elimCost n ns) :=
  (h hcsr hB hMB).post fun _ _ _ hq => elimPost_of_elimMem hq

/-! ### The worked example

House discipline: what the specification says is also *seen*. The graph
is the triangle `0—1—2` with the path `2—3—4` hanging off it — five
vertices, five edges, degeneracy two — and the mask on vertex `2` is
the parameter, so the same program shows both sides of the isolation.

With `2` alive the engine peels `4, 3, 2, 1, 0` and reports `k = 2`,
the triangle being what forces it; the ranks come out `0, 1, 2, 3, 4`
and the in-lists are `∅, {0}, {0,1}, {2}, {3}` — in-degrees `0, 1, 2,
1, 1`, the largest of them the reported `k`.

With `2` dead the arena falls apart into the edges `0—1` and `3—4`, the
engine reports `k = 1`, and the in-lists are `∅, {0}, ∅, ∅, {3}` —
vertex `2` isolated, ranked, and carrying nothing, which is the whole
of what the mask does to this program. -/

namespace Demo

/-- The offsets of the triangle `0—1—2` with the path `2—3—4`. -/
def demoOff : Com :=
  .seq (.store "off" (.lit 0) (.lit 0))
    (.seq (.store "off" (.lit 1) (.lit 2))
      (.seq (.store "off" (.lit 2) (.lit 4))
        (.seq (.store "off" (.lit 3) (.lit 7))
          (.seq (.store "off" (.lit 4) (.lit 9))
            (.store "off" (.lit 5) (.lit 10))))))

/-- Its targets: `1 2 | 0 2 | 0 1 3 | 2 4 | 3`. -/
def demoTgt : Com :=
  .seq (.store "tgt" (.lit 0) (.lit 1))
    (.seq (.store "tgt" (.lit 1) (.lit 2))
      (.seq (.store "tgt" (.lit 2) (.lit 0))
        (.seq (.store "tgt" (.lit 3) (.lit 2))
          (.seq (.store "tgt" (.lit 4) (.lit 0))
            (.seq (.store "tgt" (.lit 5) (.lit 1))
              (.seq (.store "tgt" (.lit 6) (.lit 3))
                (.seq (.store "tgt" (.lit 7) (.lit 2))
                  (.seq (.store "tgt" (.lit 8) (.lit 4))
                    (.store "tgt" (.lit 9) (.lit 3))))))))))

/-- The mask, with the bit of vertex `2` left open. -/
def demoAlv (a2 : ℕ) : Com :=
  .seq (.store "alv" (.lit 0) (.lit 1))
    (.seq (.store "alv" (.lit 1) (.lit 1))
      (.seq (.store "alv" (.lit 2) (.lit a2))
        (.seq (.store "alv" (.lit 3) (.lit 1))
          (.store "alv" (.lit 4) (.lit 1)))))

/-- Five vertices, ten slots. -/
def demoSetup (a2 : ℕ) : Com :=
  .seq (.assign "n" (.lit 5)) (.seq demoOff (.seq demoTgt (demoAlv a2)))

/-- The five ranks, the bound, the six offsets and the five arc slots,
in that order. -/
def demoReport : Com :=
  .seq (.write (.get "rnk" (.lit 0)))
    (.seq (.write (.get "rnk" (.lit 1)))
      (.seq (.write (.get "rnk" (.lit 2)))
        (.seq (.write (.get "rnk" (.lit 3)))
          (.seq (.write (.get "rnk" (.lit 4)))
            (.seq (.write (.var "kmax"))
              (.seq (.write (.get "ioff" (.lit 0)))
                (.seq (.write (.get "ioff" (.lit 1)))
                  (.seq (.write (.get "ioff" (.lit 2)))
                    (.seq (.write (.get "ioff" (.lit 3)))
                      (.seq (.write (.get "ioff" (.lit 4)))
                        (.seq (.write (.get "ioff" (.lit 5)))
                          (.seq (.write (.get "itg" (.lit 0)))
                            (.seq (.write (.get "itg" (.lit 1)))
                              (.seq (.write (.get "itg" (.lit 2)))
                                (.seq (.write (.get "itg" (.lit 3)))
                                  (.write (.get "itg" (.lit 4))))))))))))))))))

/-- Build the structure, run the engine, report. -/
def demoWatched (a2 : ℕ) : Com := .seq (demoSetup a2) (.seq elimCom demoReport)

/-- Sixteen scalars, thirteen arrays, four temporaries. -/
def demoLayout : Lax13Proofs.Compile.Layout :=
  ⟨["n", "i", "j", "jend", "c", "u", "d", "sp", "ls", "mind", "cnt", "kmax", "p", "w",
    "s", "sc"],
   ["off", "tgt", "alv", "deg", "elm", "rnk", "idg", "bh", "bv", "bn", "ioff", "ifl", "itg"],
   4⟩

/-- The machine program. -/
def demoProg (a2 : ℕ) : Lax13.Ram.Program :=
  Lax13Proofs.Compile.compileProgram demoLayout (demoWatched a2)

/-- The layout covers the block, so the compilation is the one the
simulation theorem is about and not an accident. -/
theorem demoWatched_ok (a2 : ℕ) :
    Lax13Proofs.Compile.Com.Ok demoLayout (demoWatched a2) := by
  simp [demoWatched, demoSetup, demoOff, demoTgt, demoAlv, demoReport, elimCom, initDeg,
    degRow, degSlot, initBuck, initBuckRow, push, elimLoop, elimTurn, elimVertex, decSlot,
    offPass, offRow, fillPass, fillRow, fillSlot, Csr.loadRow, Csr.scan, demoLayout,
    Lax13Proofs.Compile.Com.Ok, Lax13Proofs.Compile.Cond.Ok, Lax13Proofs.Compile.condExpr,
    Lax13Proofs.Compile.Expr.Ok]

/-- Run it at a word length that holds every number this graph
produces. -/
def demoRun (a2 : ℕ) : Option (List ℕ × ℕ) :=
  runOut 16 2000000 (demoProg a2) (Lax13.Ram.initState []) 0

-- vertex `2` alive: the ranks `0 … 4` in reverse peeling order, the
-- bound `2` that the triangle forces, and the blocks
-- `∅ | 0 | 0 1 | 2 | 3`
#guard demoRun 1 = some ([0, 1, 2, 3, 4, 2, 0, 0, 1, 3, 4, 5, 0, 0, 1, 2, 3], 8082)
-- vertex `2` dead: the arena is `0—1` and `3—4`, the bound drops to
-- `1`, vertex `2` is ranked last-but-nothing and its block is empty,
-- and the two arcs are `0 → 1` and `3 → 4`
#guard demoRun 0 = some ([0, 1, 4, 2, 3, 1, 0, 0, 1, 1, 1, 2, 0, 3, 0, 0, 0], 6662)

/-! And the arithmetic on the other side of the abstraction: the two
arrays the run reported really cut into the in-neighbour lists the
orientation is supposed to have. -/

/-- The block of `w`, read off a pair of reported arrays. -/
def demoBlock (IO IT : List ℕ) (w : ℕ) : List ℕ :=
  (List.range (IO.getD (w + 1) 0 - IO.getD w 0)).map fun t => IT.getD (IO.getD w 0 + t) 0

-- with vertex `2` alive: `∅ | 0 | 0 1 | 2 | 3`, in-degrees `0 1 2 1 1`
#guard demoBlock [0, 0, 1, 3, 4, 5] [0, 0, 1, 2, 3] 0 = []
#guard demoBlock [0, 0, 1, 3, 4, 5] [0, 0, 1, 2, 3] 1 = [0]
#guard demoBlock [0, 0, 1, 3, 4, 5] [0, 0, 1, 2, 3] 2 = [0, 1]
#guard demoBlock [0, 0, 1, 3, 4, 5] [0, 0, 1, 2, 3] 3 = [2]
#guard demoBlock [0, 0, 1, 3, 4, 5] [0, 0, 1, 2, 3] 4 = [3]
-- and with it dead the arena is `0—1` and `3—4`, and `2` carries
-- nothing
#guard demoBlock [0, 0, 1, 1, 1, 2] [0, 3, 0, 0, 0] 0 = []
#guard demoBlock [0, 0, 1, 1, 1, 2] [0, 3, 0, 0, 0] 1 = [0]
#guard demoBlock [0, 0, 1, 1, 1, 2] [0, 3, 0, 0, 0] 2 = []
#guard demoBlock [0, 0, 1, 1, 1, 2] [0, 3, 0, 0, 0] 3 = []
#guard demoBlock [0, 0, 1, 1, 1, 2] [0, 3, 0, 0, 0] 4 = [3]

end Demo

end Lax3Proofs.RamElim
