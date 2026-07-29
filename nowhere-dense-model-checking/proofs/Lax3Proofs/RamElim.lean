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

### The program, and that it implements the specification

`elim_spec` is the specification and `implements` discharges the Hoare
triple it is proved from — `Implements`, stated over the program text,
the input surface a caller has, and the linear cost `elimCost`.
Everything that triple's postcondition *means* — `elimPost_of_elimMem`,
and behind it the whole of `ElimCert` and `InCsr` — is proved here too,
and the program is exhibited, compiled and run: the worked example
checks its three answers on a five-vertex graph, with and without the
mask, against the hand computation.

The triple splits along the program's five phases, each a `Spec` of its
own: `initDeg_spec`, the degree pass with its amortized outer loop;
`initBuck_spec`, the bucket build, whose content is `Buck.push`;
`elimLoop_spec`, the elimination, whose turn is `elimTurn_run` and
whose `while` is paid out of the potential `Pot`; `offPass_spec`, the
running sum; and `fillPass_spec`, the counting sort that writes the
in-neighbour lists. `implements` sequences the five against `AfterDeg`,
`AfterBuck`, `AfterLoop` and `AfterOff`, the four predicates saying
what a phase hands the next. The reachability relation the bucket
phases run on is `chain`, and `written` is the fill's counterpart —
what a row has written so far, which at the end of the row is the block
`InCsr` asks for.
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
engine cannot know: that the round's orientation put the arcs it *added
on fraternal grounds* the way the ranking says. The arcs the round
inherited from `D`, and the ones a transitive link forced, are none of
the ranking's business — `Augmentation.inDegLE_of_augStep` charges
those elsewhere. -/
theorem greedyFratRound_of_cert {D D' : Orientation n} {ρ : Fin n → ℕ} {k : ℕ}
    (h : ElimCert (fratGraph D) ρ k)
    (hor : ∀ u v : Fin n, u ∈ D'.inN v → u ∉ D.inN v → ¬ TransLink D u v →
      (fratGraph D).Adj u v → ρ u < ρ v) :
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
  /-- The degree array holds the true current degrees of the arena — of
  the vertices still there. What it holds at an eliminated vertex is the
  degree that vertex had when it was taken, and the program is right not
  to keep it up: a row scan decrements the neighbours that are still
  alive, and no clause below asks about the others. -/
  deg : ∀ v : Fin n, E (v : ℕ) = 0 → D (v : ℕ) = (nbrsIn (masked G M) (aliveF E) v).card
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

/-- Every surviving degree is smaller than the number of vertices. -/
theorem deg_lt (h : Elim G M E D R ID cnt mind kmax) {v : ℕ} (hv : v < n) (hE : E v = 0) :
    D v < n := by
  rw [show v = ((⟨v, hv⟩ : Fin n) : ℕ) from rfl, h.deg ⟨v, hv⟩ hE]
  exact card_nbrsIn_lt _ _

/-- The pointer never passes the last possible degree. -/
theorem mind_lt (h : Elim G M E D R ID cnt mind kmax) {v : ℕ} (hv : v < n) (hE : E v = 0) :
    mind < n := lt_of_le_of_lt (h.min_le v hv hE) (h.deg_lt hv hE)

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
    (hdec : ∀ u < n, E u = 0 → MAdj G M u v → D' u = D u - 1)
    (hkeep : ∀ u < n, E u = 0 → ¬ MAdj G M u v → D' u = D u) :
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
  have hdeg' : ∀ u : Fin n, (upd E v 1) (u : ℕ) = 0 →
      D' (u : ℕ) = (nbrsIn (masked G M) (aliveF (upd E v 1)) u).card := by
    intro u hu
    have huv : (u : ℕ) ≠ v := fun hc => by rw [hc, upd_self] at hu; omega
    have hEu : E (u : ℕ) = 0 := by rwa [upd_of_ne _ huv] at hu
    rw [halive, nbrsIn_erase]
    by_cases hadj : MAdj G M (u : ℕ) v
    · rw [hdec (u : ℕ) u.isLt hEu hadj, h.deg u hEu,
        Finset.card_erase_of_mem ((hmemv u).2 hadj)]
    · rw [hkeep (u : ℕ) u.isLt hEu hadj, h.deg u hEu,
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
    · rw [hdec u hu hEu' hadj]; omega
    · rw [hkeep u hu hEu' hadj]; omega
  · -- the vertex just taken records the degree it had
    by_cases hwv : (w : ℕ) = v
    · have hwe : w = (⟨v, hv⟩ : Fin n) := Fin.ext hwv
      subst hwe
      rw [upd_self, upd_self, hself]
      rw [← h.deg ⟨v, hv⟩ hE]
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
      rw [upd_self, upd_self, hself, ← h.deg u (mem_aliveF.1 huS)]
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
    fun v _ => by rw [hal]; exact hD v, fun v hv hEv => Nat.zero_le _,
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

/-- The slots of the bucket whose head is `p`, from the head down. -/
def chain (BN : ℕ → ℕ) (p : ℕ) : List ℕ :=
  if 0 < p then
    if _hlt : BN p < p then p :: chain BN (BN p) else [p]
  else []
termination_by p
decreasing_by omega

@[simp] theorem chain_zero (BN : ℕ → ℕ) : chain BN 0 = [] := by rw [chain]; simp

theorem chain_cons (BN : ℕ → ℕ) {p : ℕ} (hp : 0 < p) (h : BN p < p) :
    chain BN p = p :: chain BN (BN p) := by rw [chain]; simp [hp, h]

theorem chain_mem_pos {BN : ℕ → ℕ} {p q : ℕ} (hq : q ∈ chain BN p) : 0 < q := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp at hq
    · by_cases h : BN p < p
      · rw [chain_cons BN hp h, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hp
        · exact ih _ h hq
      · rw [chain] at hq; simp only [if_pos hp, dif_neg h, List.mem_singleton] at hq; omega

theorem chain_mem_le {BN : ℕ → ℕ} {p q : ℕ} (hq : q ∈ chain BN p) : q ≤ p := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp at hq
    · by_cases h : BN p < p
      · rw [chain_cons BN hp h, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact le_rfl
        · exact le_trans (ih _ h hq) (le_of_lt h)
      · rw [chain] at hq; simp only [if_pos hp, dif_neg h, List.mem_singleton] at hq; omega

/-- Writing a cell the chains cannot reach leaves them alone. -/
theorem chain_upd_high {BN : ℕ → ℕ} {s : ℕ} (halloc : ∀ p, 0 < p → p < s → BN p < p) (x : ℕ) :
    ∀ p < s, chain (upd BN s x) p = chain BN p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hps
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · have h₁ : BN p < p := halloc p hp hps
      have h₂ : upd BN s x p = BN p := upd_of_ne _ (by omega)
      rw [chain_cons _ hp (by rw [h₂]; exact h₁), h₂, chain_cons BN hp h₁,
        ih (BN p) (by omega) (by omega)]

/-- **A push, at the bucket it pushes into**: the fresh slot goes in
front of the old head. -/
theorem chain_push_eq {BH BN : ℕ → ℕ} {s d : ℕ} (hs : 0 < s)
    (halloc : ∀ p, 0 < p → p < s → BN p < p) (hd : BH d < s) :
    chain (upd BN s (BH d)) (upd BH d s d) = s :: chain BN (BH d) := by
  rw [upd_self, chain_cons _ hs (by rw [upd_self]; exact hd), upd_self,
    chain_upd_high halloc _ _ hd]

/-- **A push, at every other bucket**: nothing happens. -/
theorem chain_push_ne {BH BN : ℕ → ℕ} {s d e : ℕ}
    (halloc : ∀ p, 0 < p → p < s → BN p < p) (he : BH e < s) (hed : e ≠ d) :
    chain (upd BN s (BH d)) (upd BH d s e) = chain BN (BH e) := by
  rw [upd_of_ne _ hed, chain_upd_high halloc _ _ he]

/-- One summand of a sum over the buckets goes up by one and the rest
stand still. -/
theorem sum_add_one {N d : ℕ} (hd : d ≤ N) {f g : ℕ → ℕ}
    (hne : ∀ e ≤ N, e ≠ d → f e = g e) (heq : f d = g d + 1) :
    ∑ e ∈ Finset.range (N + 1), f e = (∑ e ∈ Finset.range (N + 1), g e) + 1 := by
  classical
  have hmem : d ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
  have h₁ := Finset.add_sum_erase (Finset.range (N + 1)) f hmem
  have h₂ := Finset.add_sum_erase (Finset.range (N + 1)) g hmem
  have h₃ : ∑ x ∈ (Finset.range (N + 1)).erase d, f x
      = ∑ x ∈ (Finset.range (N + 1)).erase d, g x :=
    Finset.sum_congr rfl (fun e he => hne e
      (by have := Finset.mem_range.1 (Finset.mem_of_mem_erase he); omega)
      (Finset.ne_of_mem_erase he))
  omega

/-- What the lazily deleted bucket stacks satisfy at every point of the
run: the arena is allocated downwards, every slot holds a vertex, every
uneliminated vertex below `m` has a slot in the bucket of its current
degree, and `ls` counts the slots the buckets still hold. -/
structure Buck (n m : ℕ) (E D BH BV BN : ℕ → ℕ) (sp ls : ℕ) : Prop where
  /-- Slot zero is the sentinel, so the pointer starts above it. -/
  sp_pos : 0 < sp
  /-- Every bucket head is an allocated slot, or the sentinel. -/
  head_lt : ∀ d ≤ n, BH d < sp
  /-- **An allocated slot points strictly downwards**, which is what
  makes a chain finite and bounds the travel of a pop. -/
  alloc : ∀ p, 0 < p → p < sp → BN p < p
  /-- And holds a vertex. -/
  val_lt : ∀ p, 0 < p → p < sp → BV p < n
  /-- A degree names a bucket. -/
  deg_le : ∀ v < m, D v ≤ n
  /-- **Every uneliminated vertex has a slot in the bucket of its
  current degree** — the clause an empty bucket is read against. -/
  mem : ∀ v < m, E v = 0 → ∃ q ∈ chain BN (BH (D v)), BV q = v
  /-- And `ls` is the number of slots the buckets hold. -/
  ls_eq : ls = ∑ d ∈ Finset.range (n + 1), (chain BN (BH d)).length

namespace Buck

variable {m : ℕ} {E D BH BV BN : ℕ → ℕ} {sp ls : ℕ}

/-- **An empty bucket has no vertex in it.** -/
theorem no_deg (h : Buck n m E D BH BV BN sp ls) {d : ℕ} (hd : BH d = 0)
    {v : ℕ} (hv : v < m) (hE : E v = 0) : D v ≠ d := by
  intro hDv
  obtain ⟨q, hq, -⟩ := h.mem v hv hE
  rw [hDv, hd] at hq
  simp at hq

/-- The elimination flags only ever enter through `E v = 0`, so a state
that says less about them still satisfies the relation. -/
theorem weaken (h : Buck n m (fun _ => 0) D BH BV BN sp ls) (E : ℕ → ℕ) :
    Buck n m E D BH BV BN sp ls :=
  { h with mem := fun v hv _ => h.mem v hv rfl }

/-- **A push.** One fresh slot, linked in front of the head of bucket
`d`, holding the vertex `x` whose new degree `d` is. Every other
bucket's chain is untouched, so every witness the state had it still
has. -/
theorem push (h : Buck n m E D BH BV BN sp ls) {D' : ℕ → ℕ} {x d m' : ℕ}
    (hx : x < n) (hd : d ≤ n) (hdx : D' x = d) (hDD : ∀ v, v ≠ x → D' v = D v)
    (hD' : ∀ v < m', D' v ≤ n) (hm : ∀ v < m', v ≠ x → v < m) :
    Buck n m' E D' (upd BH d sp) (upd BV sp x) (upd BN sp (BH d)) (sp + 1) (ls + 1) := by
  have hdsp : BH d < sp := h.head_lt d hd
  refine ⟨by omega, fun e he => ?_, fun p hp hps => ?_, fun p hp hps => ?_, hD', ?_, ?_⟩
  · by_cases hed : e = d
    · rw [hed, upd_self]; omega
    · rw [upd_of_ne _ hed]; have := h.head_lt e he; omega
  · by_cases hpsp : p = sp
    · rw [hpsp, upd_self]; omega
    · rw [upd_of_ne _ hpsp]; exact h.alloc p hp (by omega)
  · by_cases hpsp : p = sp
    · rw [hpsp, upd_self]; exact hx
    · rw [upd_of_ne _ hpsp]; exact h.val_lt p hp (by omega)
  · intro v hv hEv
    by_cases hvx : v = x
    · subst hvx
      exact ⟨sp, by rw [hdx, chain_push_eq h.sp_pos h.alloc hdsp]; simp, upd_self ..⟩
    · obtain ⟨q, hq, hqv⟩ := h.mem v (hm v hv hvx) hEv
      have hDv : D v ≤ n := h.deg_le v (hm v hv hvx)
      have hqsp : q < sp := lt_of_le_of_lt (chain_mem_le hq) (h.head_lt _ hDv)
      refine ⟨q, ?_, by rw [upd_of_ne _ (by omega : q ≠ sp)]; exact hqv⟩
      rw [hDD v hvx]
      by_cases hDd : D v = d
      · rw [hDd, chain_push_eq h.sp_pos h.alloc hdsp, List.mem_cons]
        exact Or.inr (hDd ▸ hq)
      · rw [chain_push_ne h.alloc (h.head_lt _ hDv) hDd]; exact hq
  · rw [h.ls_eq]
    refine (sum_add_one hd (fun e hen hed => ?_) ?_).symm
    · rw [chain_push_ne h.alloc (h.head_lt e hen) hed]
    · rw [chain_push_eq h.sp_pos h.alloc hdsp]; simp

/-- **A pop.** The head slot of bucket `d` comes off, stale or not.
Every other bucket's chain is literally unchanged — a pop writes one
head and no next pointer — and the popped bucket loses exactly its
head, so every witness survives but the one naming the popped slot's
own vertex. That the bucket was nonempty is what says there was a slot
to lose, and so that `ls` really goes down. -/
theorem pop (h : Buck n m E D BH BV BN sp ls) {d : ℕ} (hd : d ≤ n) (hne : BH d ≠ 0)
    (E' : ℕ → ℕ) (hE' : ∀ v < m, E' v = 0 → E v = 0)
    (hout : ∀ v < m, E' v = 0 → D v = d → v ≠ BV (BH d)) :
    0 < ls ∧ Buck n m E' D (upd BH d (BN (BH d))) BV BN sp (ls - 1) := by
  have hdsp : BH d < sp := h.head_lt d hd
  have hpos : 0 < BH d := Nat.pos_of_ne_zero hne
  have hlt : BN (BH d) < BH d := h.alloc _ hpos hdsp
  have hchain : chain BN (BH d) = BH d :: chain BN (BN (BH d)) := chain_cons BN hpos hlt
  have hsum : ∑ e ∈ Finset.range (n + 1), (chain BN (BH e)).length
      = (∑ e ∈ Finset.range (n + 1), (chain BN (upd BH d (BN (BH d)) e)).length) + 1 := by
    refine sum_add_one hd (fun e _ hed => ?_) ?_
    · rw [upd_of_ne _ hed]
    · rw [upd_self, hchain]; simp
  refine ⟨by rw [h.ls_eq, hsum]; omega,
    ⟨h.sp_pos, fun e he => ?_, h.alloc, h.val_lt, h.deg_le, ?_, by rw [h.ls_eq, hsum]; omega⟩⟩
  · by_cases hed : e = d
    · rw [hed, upd_self]; omega
    · rw [upd_of_ne _ hed]; exact h.head_lt e he
  · intro v hv hEv
    obtain ⟨q, hq, hqv⟩ := h.mem v hv (hE' v hv hEv)
    by_cases hDd : D v = d
    · rw [hDd, upd_self]
      rw [hDd, hchain, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact absurd hqv.symm (hout v hv hEv hDd)
      · exact ⟨q, hq, hqv⟩
    · rw [upd_of_ne _ hDd]; exact ⟨q, hq, hqv⟩

end Buck

/-! #### The buckets, filled -/

/-- The invariant of the bucket build: one slot per vertex placed so
far, at the top of the arena, and every vertex below the counter with a
slot in the bucket of its degree. -/
def BuckInv (n ns : ℕ) (D : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs "deg" = arrOf n D ∧ σ.vars "i" ≤ n ∧
    σ.vars "sp" = σ.vars "i" + 1 ∧ σ.vars "ls" = σ.vars "i" ∧
    ∃ BH BV BN, σ.arrs "bh" = arrOf (n + 1) BH ∧ σ.arrs "bv" = arrOf (n + ns + 1) BV ∧
      σ.arrs "bn" = arrOf (n + ns + 1) BN ∧
      Buck n (σ.vars "i") (fun _ => 0) D BH BV BN (σ.vars "sp") (σ.vars "ls")

/-- **One vertex, put in the bucket of its degree.** The fresh slot is
the top of the arena, so it is above every slot the chains hold and the
push is `Buck.push` on the nose. -/
theorem initBuckRow_spec (B n ns : ℕ) (D : ℕ → ℕ) (hnB : n + 1 < B)
    (hD : ∀ v < n, D v < n) :
    Spec B (fun σ => BuckInv n ns D σ ∧ σ.vars "i" < n) initBuckRow
      (fun σ σ' => BuckInv n ns D σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 25 := by
  intro σ hσ
  obtain ⟨⟨hn, hdeg, hile, hsp, hls, BH, BV, BN, hbh, hbv, hbn, hbuck⟩, hlt⟩ := hσ
  have hdegi : (σ.arrs "deg").getD (σ.vars "i") 0 = D (σ.vars "i") := by
    rw [hdeg, getD_arrOf D hlt]
  have hDi : D (σ.vars "i") < n := hD _ hlt
  have hdeglen : σ.vars "i" < (σ.arrs "deg").length := by rw [hdeg, length_arrOf]; exact hlt
  have hbvlen : σ.vars "sp" < (σ.arrs "bv").length := by rw [hbv, length_arrOf]; omega
  have hbnlen : σ.vars "sp" < (σ.arrs "bn").length := by rw [hbn, length_arrOf]; omega
  have hbhlen : (σ.arrs "deg").getD (σ.vars "i") 0 < (σ.arrs "bh").length := by
    rw [hdegi, hbh, length_arrOf]; omega
  have hbhd : (σ.arrs "bh").getD ((σ.arrs "deg").getD (σ.vars "i") 0) 0
      = BH (D (σ.vars "i")) := by rw [hdegi, hbh, getD_arrOf BH (by omega)]
  have hbhdlt : BH (D (σ.vars "i")) < σ.vars "sp" := hbuck.head_lt _ (by omega)
  have hbhdB : (σ.arrs "bh").getD ((σ.arrs "deg").getD (σ.vars "i") 0) 0 < B := by
    rw [hbhd]; omega
  have hdiB : (σ.arrs "deg").getD (σ.vars "i") 0 < B := by rw [hdegi]; omega
  -- the same reads in the `getElem?` form the walk's discharger normalizes into
  have hdegi' : (σ.arrs "deg")[σ.vars "i"]?.getD 0 = D (σ.vars "i") := by
    rw [← List.getD_eq_getElem?_getD]; exact hdegi
  have hdiB' : (σ.arrs "deg")[σ.vars "i"]?.getD 0 < B := by rw [hdegi']; omega
  have hbhlen' : (σ.arrs "deg")[σ.vars "i"]?.getD 0 < (σ.arrs "bh").length := by
    rw [hdegi', hbh, length_arrOf]; omega
  have hbhd' : (σ.arrs "bh").getD ((σ.arrs "deg")[σ.vars "i"]?.getD 0) 0
      = BH (D (σ.vars "i")) := by rw [hdegi', hbh, getD_arrOf BH (by omega)]
  have hbhd'B : (σ.arrs "bh").getD ((σ.arrs "deg")[σ.vars "i"]?.getD 0) 0 < B := by
    rw [hbhd']; omega
  have hbhd'' : (σ.arrs "bh")[(σ.arrs "deg")[σ.vars "i"]?.getD 0]?.getD 0
      = BH (D (σ.vars "i")) := by rw [← List.getD_eq_getElem?_getD]; exact hbhd'
  have hbhd''B : (σ.arrs "bh")[(σ.arrs "deg")[σ.vars "i"]?.getD 0]?.getD 0 < B := by
    rw [hbhd'']; omega
  run_vcg
  refine ⟨⟨by simp [hn], by simp [hdeg], by simp; omega, by simp; omega, by simp; omega,
    upd BH (D (σ.vars "i")) (σ.vars "sp"), upd BV (σ.vars "sp") (σ.vars "i"),
    upd BN (σ.vars "sp") (BH (D (σ.vars "i"))),
    by simp [hbh, hdegi', set_arrOf_eq_upd], by simp [hbv, set_arrOf_eq_upd],
    by simp [hbn, hbhd'', set_arrOf_eq_upd], ?_⟩, by simp⟩
  have hpush := hbuck.push (D' := D) (x := σ.vars "i") (d := D (σ.vars "i"))
    (m' := σ.vars "i" + 1) hlt (by omega) rfl (fun _ _ => rfl)
    (fun v hv => le_of_lt (hD v (by omega))) (fun v hv hvx => by omega)
  simpa using hpush

/-- **Every vertex, put in the bucket of its degree.** A flat pass, so
the kit's counted scan supplies the loop; what the pass leaves is one
slot per vertex, `sp` at `n + 1` and `ls` at `n`. The heads start at
the sentinel, which is what the machine's zeroed memory already
says. -/
theorem initBuck_spec (B n ns : ℕ) (D : ℕ → ℕ) (hnB : n + 1 < B) (hD : ∀ v < n, D v < n) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "deg" = arrOf n D ∧
        (∃ g, σ.arrs "bh" = arrOf (n + 1) g ∧ ∀ j ≤ n, g j = 0) ∧
        (∃ g, σ.arrs "bv" = arrOf (n + ns + 1) g) ∧ (∃ g, σ.arrs "bn" = arrOf (n + ns + 1) g))
      initBuck
      (fun _ σ' => BuckInv n ns D σ' ∧ σ'.vars "i" = n)
      (29 * n + 10) := by
  have hloop : Spec B (fun σ => BuckInv n ns D (σ.setVar "i" 0))
      (.seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "n")) initBuckRow))
      (fun _ σ' => BuckInv n ns D σ' ∧ σ'.vars "i" = n) ((25 + 4) * n + 6) :=
    Spec.forRangeZero "i" "n" (BuckInv n ns D) n 25 (by omega)
      (fun _ h => h.2.2.1) (fun _ h => h.1) (initBuckRow_spec B n ns D hnB hD)
  run_vcg [hloop]
  · exact ‹BuckInv n ns D _ ∧ _›
  · -- the arena is empty, so every bucket is the sentinel and `ls` is nought
    obtain ⟨BH, hbh, hBH⟩ := ‹∃ g, σ.arrs "bh" = arrOf (n + 1) g ∧ ∀ j ≤ n, g j = 0›
    obtain ⟨BV, hbv⟩ := ‹∃ g, σ.arrs "bv" = arrOf (n + ns + 1) g›
    obtain ⟨BN, hbn⟩ := ‹∃ g, σ.arrs "bn" = arrOf (n + ns + 1) g›
    have hn : σ.vars "n" = n := ‹σ.vars "n" = n›
    have hdeg : σ.arrs "deg" = arrOf n D := ‹σ.arrs "deg" = arrOf n D›
    refine ⟨by simp [hn], by simp [hdeg], by simp, by simp, by simp,
      BH, BV, BN, by simp [hbh], by simp [hbv], by simp [hbn],
      ⟨by simp, fun d hd => by simp [hBH d hd], fun p hp hps => by simp at hps; omega,
        fun p hp hps => by simp at hps; omega, fun v hv => by simp at hv,
        fun v hv => by simp at hv, ?_⟩⟩
    refine (Finset.sum_eq_zero fun d hd => ?_).symm
    rw [hBH d (by have := Finset.mem_range.1 hd; omega), chain_zero]
    simp

/-! #### The elimination -/

/-- The vertices whose rows the run has already scanned: the ones taken
and alive. Their blocks tile part of the target array, which is what
bounds the slot counter and so the arena. -/
def scanned (n : ℕ) (E M : ℕ → ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun v => E v = 1 ∧ M v ≠ 0)

theorem mem_scanned {E M : ℕ → ℕ} {v : ℕ} :
    v ∈ scanned n E M ↔ v < n ∧ E v = 1 ∧ M v ≠ 0 := by
  rw [scanned, Finset.mem_filter, Finset.mem_range]

/-- **The rows already scanned fit inside the target array.** -/
theorem scanned_sum_le (hcsr : CsrGraph G ns O T) (E : ℕ → ℕ) :
    ∑ v ∈ scanned n E M, Csr.rowLen O v ≤ ns :=
  hcsr.sum_rowLen_le (fun _ hv => (mem_scanned.1 hv).1)

/-- Taking a live vertex adds its row to them. -/
theorem scanned_upd_alive {E M : ℕ → ℕ} {w : ℕ} (hw : w < n) (hE : E w = 0) (hM : M w ≠ 0) :
    scanned n (upd E w 1) M = insert w (scanned n E M) := by
  ext v
  simp only [mem_scanned, Finset.mem_insert]
  by_cases hvw : v = w
  · subst hvw; simp [hw, hM]
  · rw [upd_of_ne _ hvw]; exact ⟨fun h => Or.inr h, fun h => h.resolve_left hvw⟩

/-- Taking a dead one adds nothing: it has no row to scan. -/
theorem scanned_upd_dead {E M : ℕ → ℕ} {w : ℕ} (hM : M w = 0) :
    scanned n (upd E w 1) M = scanned n E M := by
  ext v
  simp only [mem_scanned]
  by_cases hvw : v = w
  · subst hvw; simp [hM]
  · rw [upd_of_ne _ hvw]

/-- The arrays of the engine, at their lengths. -/
def ElimArr (n ns : ℕ) (O T M E D R ID BH BV BN : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
    σ.arrs "alv" = arrOf n M ∧ σ.arrs "elm" = arrOf n E ∧ σ.arrs "deg" = arrOf n D ∧
    σ.arrs "rnk" = arrOf n R ∧ σ.arrs "idg" = arrOf n ID ∧
    σ.arrs "bh" = arrOf (n + 1) BH ∧ σ.arrs "bv" = arrOf (n + ns + 1) BV ∧
    σ.arrs "bn" = arrOf (n + ns + 1) BN

/-- A surviving neighbour of `w` that the row scan has already passed,
and so already decremented. -/
def hit (O T M E : ℕ → ℕ) (w j u : ℕ) : Prop :=
  E u = 0 ∧ M u ≠ 0 ∧ ∃ t, O w ≤ t ∧ t < j ∧ T t = u

theorem hit_mono {O T M E : ℕ → ℕ} {w j u : ℕ} (h : hit O T M E w j u) :
    hit O T M E w (j + 1) u := ⟨h.1, h.2.1, h.2.2.imp fun _ ht => ⟨ht.1, by omega, ht.2.2⟩⟩

/-- One more slot passed either was already a hit, or is the slot itself. -/
theorem hit_succ {O T M E : ℕ → ℕ} {w j u : ℕ} (h : hit O T M E w (j + 1) u) :
    hit O T M E w j u ∨ (u = T j ∧ E u = 0 ∧ M u ≠ 0) := by
  obtain ⟨hE, hM, t, h₁, h₂, h₃⟩ := h
  rcases Nat.lt_or_ge t j with hlt | hge
  · exact Or.inl ⟨hE, hM, t, h₁, hlt, h₃⟩
  · have ht : t = j := by omega
    subst ht
    exact Or.inr ⟨h₃.symm, hE, hM⟩

/-- **The slot the scan stands at is not a hit yet**: the row names each
neighbour once, so nothing before it named the same vertex. -/
theorem not_hit_self (hcsr : CsrSimple G ns O T) {M E : ℕ → ℕ} {w j : ℕ} (hw : w < n)
    (h₁ : O w ≤ j) (h₂ : j < O (w + 1)) : ¬ hit O T M E w j (T j) := by
  rintro ⟨-, -, t, ht₁, ht₂, ht₃⟩
  have := hcsr.nodup w hw t j ht₁ (by omega) h₁ h₂ ht₃
  omega

/-- The invariant of the row scan of an extraction: the degrees are the
ones the extraction started with, decremented at every surviving
neighbour the scan has already passed. -/
def DecInv (n ns : ℕ) (O T M E R ID D₀ : ℕ → ℕ) (w ls₀ sc₀ mv kv cv : ℕ) (σ : Env) : Prop :=
  ∃ D BH BV BN, ElimArr n ns O T M E D R ID BH BV BN σ ∧
    Buck n n E D BH BV BN (σ.vars "sp") (σ.vars "ls") ∧
    (∀ u < n, E u ≤ 1) ∧ (∀ u < n, D u < n) ∧
    (∀ u < n, hit O T M E w (σ.vars "j") u → D u = D₀ u - 1) ∧
    (∀ u < n, ¬ hit O T M E w (σ.vars "j") u → D u = D₀ u) ∧
    σ.vars "jend" = O (w + 1) ∧ O w ≤ σ.vars "j" ∧ σ.vars "j" ≤ O (w + 1) ∧
    σ.vars "sc" + (O (w + 1) - σ.vars "j") = ∑ v ∈ scanned n E M, Csr.rowLen O v ∧
    σ.vars "sp" ≤ n + 1 + σ.vars "sc" ∧ σ.vars "ls" + 1 ≤ σ.vars "sp" ∧
    σ.vars "ls" + sc₀ ≤ ls₀ + σ.vars "sc" ∧
    σ.vars "mind" = mv ∧ σ.vars "kmax" = kv ∧ σ.vars "cnt" = cv

/-- **One slot of the row of the vertex being eliminated.** Three paths:
a dead target and an eliminated one are passed over, and a surviving
one loses a degree and is pushed into its new bucket — which is
`Buck.push`, the old slot left where it is. Written in the `_run` form
the kit's row scan consumes, with every obligation of the walk
pre-loaded, `RamBfs.scanSlot_run`'s shape and for its reason. -/
theorem decSlot_run {B n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M E R ID D₀ : ℕ → ℕ}
    {w ls₀ sc₀ mv kv cv : ℕ} (hcsr : CsrSimple G ns O T) (hw : w < n) (hB : n + ns + 1 < B)
    (hMB : ∀ z < n, M z < B) {σ : Env}
    (hI : DecInv n ns O T M E R ID D₀ w ls₀ sc₀ mv kv cv σ)
    (hjlt : σ.vars "j" < O (w + 1)) :
    ∃ σ' K, Run B decSlot σ σ' K ∧ K ≤ 48 ∧
      DecInv n ns O T M E R ID D₀ w ls₀ sc₀ mv kv cv σ' ∧
        σ'.vars "j" = σ.vars "j" + 1 := by
  obtain ⟨D, BH, BV, BN, ⟨hn, hoff, htgt, halv, helm, hdeg, hrnk, hidg, hbh, hbv, hbn⟩,
    hbuck, hbit, hdn, hhit, hnhit, hje, hj₁, hj₂, hsc, hspc, hlsp, hls0, hmind, hkmax,
    hcnt⟩ := hI
  have hSle : ∑ v ∈ scanned n E M, Csr.rowLen O v ≤ ns := scanned_sum_le hcsr.csr E
  have hns : O (w + 1) ≤ ns := hcsr.csr.le_ns (by omega)
  have hjns : σ.vars "j" < ns := by omega
  have hun : T (σ.vars "j") < n := hcsr.csr.target_lt' hw hjlt
  have hscns : σ.vars "sc" + 1 ≤ ns := by omega
  have hroom : σ.vars "sp" < n + ns + 1 := by omega
  -- the target read, in both the forms the walk states it in
  have hrj : (σ.arrs "tgt").getD (σ.vars "j") 0 = T (σ.vars "j") := by
    rw [htgt, getD_arrOf T hjns]
  have hrj' : (σ.arrs "tgt")[σ.vars "j"]?.getD 0 = T (σ.vars "j") := by
    rw [← List.getD_eq_getElem?_getD]; exact hrj
  have hjlen : σ.vars "j" < (σ.arrs "tgt").length := by rw [htgt, length_arrOf]; omega
  have huB : (σ.arrs "tgt").getD (σ.vars "j") 0 < B := by rw [hrj]; omega
  -- the three array reads at the target
  have halvlen : (σ.arrs "tgt").getD (σ.vars "j") 0 < (σ.arrs "alv").length := by
    rw [hrj, halv, length_arrOf]; exact hun
  have halvv : (σ.arrs "alv").getD ((σ.arrs "tgt").getD (σ.vars "j") 0) 0
      = M (T (σ.vars "j")) := by rw [hrj, halv, getD_arrOf M hun]
  have halvB : (σ.arrs "alv").getD ((σ.arrs "tgt").getD (σ.vars "j") 0) 0 < B := by
    rw [halvv]; exact hMB _ hun
  have helmlen : (σ.arrs "tgt").getD (σ.vars "j") 0 < (σ.arrs "elm").length := by
    rw [hrj, helm, length_arrOf]; exact hun
  have helmv : (σ.arrs "elm").getD ((σ.arrs "tgt").getD (σ.vars "j") 0) 0
      = E (T (σ.vars "j")) := by rw [hrj, helm, getD_arrOf E hun]
  have helmB : (σ.arrs "elm").getD ((σ.arrs "tgt").getD (σ.vars "j") 0) 0 < B := by
    rw [helmv]; have := hbit _ hun; omega
  have hdeglen : (σ.arrs "tgt").getD (σ.vars "j") 0 < (σ.arrs "deg").length := by
    rw [hrj, hdeg, length_arrOf]; exact hun
  have hdegv : (σ.arrs "deg").getD ((σ.arrs "tgt").getD (σ.vars "j") 0) 0
      = D (T (σ.vars "j")) := by rw [hrj, hdeg, getD_arrOf D hun]
  have hdegB : (σ.arrs "deg").getD ((σ.arrs "tgt").getD (σ.vars "j") 0) 0 < B := by
    rw [hdegv]; have := hdn _ hun; omega
  -- the same reads in the environment the two conditionals test in
  have hbrAlv : ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).arrs "alv").getD
      ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).vars "u") 0
      = M (T (σ.vars "j")) := by rw [arrs_setVar, vars_setVar]; simpa using halvv
  have hbrElm : ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).arrs "elm").getD
      ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).vars "u") 0
      = E (T (σ.vars "j")) := by rw [arrs_setVar, vars_setVar]; simpa using helmv
  have hbrAlvB : ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).arrs "alv").getD
      ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).vars "u") 0 < B := by
    rw [hbrAlv]; exact hMB _ hun
  have hbrElmB : ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).arrs "elm").getD
      ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).vars "u") 0 < B := by
    rw [hbrElm]; have := hbit _ hun; omega
  have hbhlen : (σ.arrs "bh").length = n + 1 := by rw [hbh, length_arrOf]
  have hbvlen : (σ.arrs "bv").length = n + ns + 1 := by rw [hbv, length_arrOf]
  have hbnlen : (σ.arrs "bn").length = n + ns + 1 := by rw [hbn, length_arrOf]
  have hnothit : ¬ hit O T M E w (σ.vars "j") (T (σ.vars "j")) :=
    not_hit_self hcsr hw hj₁ hjlt
  have hDun : D (T (σ.vars "j")) < n := hdn _ hun
  have hd1n : D (T (σ.vars "j")) - 1 < n + 1 := by omega
  -- the degree cell after the decrement, and the bucket head it names
  have hsetD : ((σ.arrs "deg").set ((σ.arrs "tgt").getD (σ.vars "j") 0)
      ((σ.arrs "deg").getD ((σ.arrs "tgt").getD (σ.vars "j") 0) 0 - 1)).getD
      ((σ.arrs "tgt").getD (σ.vars "j") 0) 0 = D (T (σ.vars "j")) - 1 := by
    rw [hdegv, hrj, hdeg, set_arrOf_eq_upd, getD_arrOf _ hun, upd_self]
  have hheadlt : BH (D (T (σ.vars "j")) - 1) < σ.vars "sp" := hbuck.head_lt _ (by omega)
  have hbhget : (σ.arrs "bh").getD (((σ.arrs "deg").set ((σ.arrs "tgt").getD (σ.vars "j") 0)
      ((σ.arrs "deg").getD ((σ.arrs "tgt").getD (σ.vars "j") 0) 0 - 1)).getD
      ((σ.arrs "tgt").getD (σ.vars "j") 0) 0) 0 = BH (D (T (σ.vars "j")) - 1) := by
    rw [hsetD, hbh, getD_arrOf BH (by omega)]
  have hdn' : ∀ u < n, upd D (T (σ.vars "j")) (D (T (σ.vars "j")) - 1) u < n := by
    intro u hu
    by_cases hux : u = T (σ.vars "j")
    · rw [hux, upd_self]; omega
    · rw [upd_of_ne _ hux]; exact hdn u hu
  run_vcg
  · -- a surviving neighbour loses a degree and is pushed into its new bucket
    have hMu : M (T (σ.vars "j")) ≠ 0 := by omega
    have hEu : E (T (σ.vars "j")) = 0 := by omega
    have hpush := hbuck.push (D' := upd D (T (σ.vars "j")) (D (T (σ.vars "j")) - 1))
      (x := T (σ.vars "j")) (d := D (T (σ.vars "j")) - 1) (m' := n) hun (by omega)
      (upd_self ..) (fun v hv => upd_of_ne _ hv)
      (fun v hv => le_of_lt (hdn' v hv)) (fun v hv _ => hv)
    refine ⟨⟨upd D (T (σ.vars "j")) (D (T (σ.vars "j")) - 1),
      upd BH (D (T (σ.vars "j")) - 1) (σ.vars "sp"), upd BV (σ.vars "sp") (T (σ.vars "j")),
      upd BN (σ.vars "sp") (BH (D (T (σ.vars "j")) - 1)),
      ⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv], by simp [helm],
        by simp [hdeg, hrj', set_arrOf_eq_upd, hun], by simp [hrnk], by simp [hidg],
        by simp [hbh, hdeg, hrj', set_arrOf_eq_upd, hun, hd1n],
        by simp [hbv, hrj', set_arrOf_eq_upd],
        by simp [hbn, hbh, hdeg, hrj', set_arrOf_eq_upd, hun, hd1n]⟩,
      by simpa using hpush, hbit, by simpa using hdn', ?_, ?_,
      by simp [hje], by simp; omega, by simp; omega, by simp; omega,
      by simp; omega, by simp; omega, by simp; omega,
      by simp [hmind], by simp [hkmax], by simp [hcnt]⟩, by simp⟩
    · intro x hx hhx
      simp only [vars_setVar] at hhx
      rcases hit_succ (by simpa using hhx) with hh | ⟨rfl, -, -⟩
      · rw [upd_of_ne _ (by rintro rfl; exact hnothit hh)]; exact hhit x hx hh
      · rw [upd_self, hnhit _ hx hnothit]
    · intro x hx hnhx
      simp only [vars_setVar] at hnhx
      have hnh : ¬ hit O T M E w (σ.vars "j" + 1) x := by simpa using hnhx
      rw [upd_of_ne _ (by rintro rfl; exact hnh ⟨hEu, hMu, σ.vars "j", hj₁, by omega, rfl⟩)]
      exact hnhit x hx (fun hc => hnh (hit_mono hc))
  · -- an eliminated neighbour is passed over
    have hEu : E (T (σ.vars "j")) ≠ 0 := by omega
    refine ⟨⟨D, BH, BV, BN,
      ⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv], by simp [helm],
        by simp [hdeg], by simp [hrnk], by simp [hidg], by simp [hbh], by simp [hbv],
        by simp [hbn]⟩,
      by simpa using hbuck, hbit, hdn, ?_, ?_,
      by simp [hje], by simp; omega, by simp; omega, by simp; omega,
      by simp; omega, by simp; omega, by simp; omega,
      by simp [hmind], by simp [hkmax], by simp [hcnt]⟩, by simp⟩
    · intro x hx hhx
      simp only [vars_setVar] at hhx
      rcases hit_succ (by simpa using hhx) with hh | ⟨rfl, hE0, -⟩
      · exact hhit x hx hh
      · exact absurd hE0 hEu
    · intro x hx hnhx
      simp only [vars_setVar] at hnhx
      have hnh : ¬ hit O T M E w (σ.vars "j" + 1) x := by simpa using hnhx
      exact hnhit x hx (fun hc => hnh (hit_mono hc))
  · -- a dead neighbour is passed over
    have hMu : M (T (σ.vars "j")) = 0 := by omega
    refine ⟨⟨D, BH, BV, BN,
      ⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv], by simp [helm],
        by simp [hdeg], by simp [hrnk], by simp [hidg], by simp [hbh], by simp [hbv],
        by simp [hbn]⟩,
      by simpa using hbuck, hbit, hdn, ?_, ?_,
      by simp [hje], by simp; omega, by simp; omega, by simp; omega,
      by simp; omega, by simp; omega, by simp; omega,
      by simp [hmind], by simp [hkmax], by simp [hcnt]⟩, by simp⟩
    · intro x hx hhx
      simp only [vars_setVar] at hhx
      rcases hit_succ (by simpa using hhx) with hh | ⟨rfl, -, hM0⟩
      · exact hhit x hx hh
      · exact absurd hMu hM0
    · intro x hx hnhx
      simp only [vars_setVar] at hnhx
      have hnh : ¬ hit O T M E w (σ.vars "j" + 1) x := by simpa using hnhx
      exact hnhit x hx (fun hc => hnh (hit_mono hc))
  all_goals simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr,
    ↓reduceIte, String.reduceEq]
  all_goals omega

/-- **The row of the vertex being eliminated, scanned.** The loop is the
kit's row scan: the caller says what a slot does, and the combinator
supplies the loop condition, the exit fact and the cost. -/
theorem decScan_spec {B n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M E R ID D₀ : ℕ → ℕ}
    {w ls₀ sc₀ mv kv cv : ℕ} (hcsr : CsrSimple G ns O T) (hw : w < n) (hB : n + ns + 1 < B)
    (hMB : ∀ z < n, M z < B) :
    Spec B (fun σ => DecInv n ns O T M E R ID D₀ w ls₀ sc₀ mv kv cv σ ∧ σ.vars "j" = O w)
      (Csr.scan "j" "jend" decSlot)
      (fun _ σ' => DecInv n ns O T M E R ID D₀ w ls₀ sc₀ mv kv cv σ' ∧
        σ'.vars "j" = O (w + 1))
      (52 * Csr.rowLen O w + 4) := by
  have hrow : Csr.rowLen O w = O (w + 1) - O w := rfl
  have hns : O (w + 1) ≤ ns := hcsr.csr.le_ns (by omega)
  refine Csr.rowScan_spec B (52 * Csr.rowLen O w + 4) (O (w + 1)) 48 "j" "jend" decSlot
    (DecInv n ns O T M E R ID D₀ w ls₀ sc₀ mv kv cv) (by omega) (fun σ hσ => ?_)
    (fun σ hσ hlt => ?_)
    (fun _ hσ => hσ.1) (fun σ hσ => by rw [hσ.2]; omega)
  · obtain ⟨D, BH, BV, BN, -, -, -, -, -, -, hje, -, hjle, -⟩ := hσ
    exact ⟨hje, hjle⟩
  · obtain ⟨σ', K', hr, hK, hI', hj'⟩ := decSlot_run hcsr hw hB hMB hσ hlt
    exact ⟨σ', K', hr, hI', hj', hK⟩

/-- The invariant of the elimination loop: the arrays at their lengths,
`Elim` on the mathematics, `Buck` on the buckets, and the four counters
that bound the arena and pay for the run. -/
def ElimSt (n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M E D R ID BH BV BN : ℕ → ℕ)
    (σ : Env) : Prop :=
  ElimArr n ns O T M E D R ID BH BV BN σ ∧
    Elim G M E D R ID (σ.vars "cnt") (σ.vars "mind") (σ.vars "kmax") ∧
    Buck n n E D BH BV BN (σ.vars "sp") (σ.vars "ls") ∧
    (∀ u < n, D u < n) ∧
    σ.vars "sc" = ∑ v ∈ scanned n E M, Csr.rowLen O v ∧
    σ.vars "sp" ≤ n + 1 + σ.vars "sc" ∧ σ.vars "ls" + 1 ≤ σ.vars "sp" ∧
    σ.vars "mind" ≤ n ∧ σ.vars "kmax" ≤ n

/-- The same with the arrays existentially quantified, which is what a
loop invariant has to be. -/
def ElimInv (n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ E D R ID BH BV BN, ElimSt n ns G O T M E D R ID BH BV BN σ

/-- **The potential the elimination is paid out of.** A pointer bump
comes out of the first term, a stale pop out of the second, an
extraction's row scan out of the third, and the extraction itself out of
the fourth — which also refunds the one the pointer's drop costs. -/
def Pot (n ns : ℕ) (σ : Env) : ℕ :=
  40 * (n + 1 - σ.vars "mind") + 40 * σ.vars "ls" + 100 * (ns - σ.vars "sc") +
    80 * (n - σ.vars "cnt")

/-- The row scan with the vertex's being a vertex moved into the
precondition, so that the specification is a term whatever the state
says — which is what a walk that must step over the scan on a path it
will then contradict needs. -/
theorem decScan_spec' {B n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M E R ID D₀ : ℕ → ℕ}
    {w ls₀ sc₀ mv kv cv : ℕ} (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B)
    (hMB : ∀ z < n, M z < B) :
    Spec B (fun σ => w < n ∧ DecInv n ns O T M E R ID D₀ w ls₀ sc₀ mv kv cv σ ∧
        σ.vars "j" = O w)
      (Csr.scan "j" "jend" decSlot)
      (fun _ σ' => DecInv n ns O T M E R ID D₀ w ls₀ sc₀ mv kv cv σ' ∧
        σ'.vars "j" = O (w + 1))
      (52 * Csr.rowLen O w + 4) :=
  fun σ hσ => decScan_spec hcsr hσ.1 hB hMB σ ⟨hσ.2.1, hσ.2.2⟩

/-- **The extraction, not taken.** A popped slot whose vertex is no
longer of the degree the pointer names is dropped and the state does not
move. Stated as a specification so that a turn which does not extract is
walked without ever entering `elimVertex` — and so pays six, not the
extraction's price. -/
theorem elimSkipMin_spec (B : ℕ) :
    Spec B (fun τ => τ.vars "w" < (τ.arrs "deg").length ∧
        (τ.arrs "deg").getD (τ.vars "w") 0 < B ∧ τ.vars "w" < B ∧ τ.vars "mind" < B ∧
        (τ.arrs "deg").getD (τ.vars "w") 0 ≠ τ.vars "mind")
      (.ite (.eq (.get "deg" (.var "w")) (.var "mind")) elimVertex .skip)
      (fun τ τ' => τ' = τ) 6 := by
  rintro τ ⟨hlen, hval, hwB, hmB, hne⟩
  have hb : (Cond.eq (.get "deg" (.var "w")) (.var "mind")).evalB B τ = some false := by
    rw [evalB_condEq
      (RunStep.eval_get B τ "deg" (.var "w") (τ.vars "w") (evalB_var hwB) hlen hval)
      (evalB_var hmB)]
    simpa using hne
  exact ⟨τ, (Run.ite_false hb Run.skip).mono (by simp), rfl⟩

/-- **The pointer moves up over an empty bucket.** An empty bucket holds
no surviving vertex of that degree — that is what `Buck.no_deg` says and
what `Elim.bump` asks for — and the turn is paid out of the pointer's own
term of the potential. -/
theorem elimBump_run {B n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M E D R ID BH BV BN : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B) {σ : Env}
    (hst : ElimSt n ns G O T M E D R ID BH BV BN σ) (hcnt : σ.vars "cnt" < n)
    (hbh0 : BH (σ.vars "mind") = 0) :
    ∃ σ' K, Run B elimTurn σ σ' K ∧ K ≤ 30 ∧
      (ElimInv n ns G O T M σ' ∧ Pot n ns σ' + 34 ≤ Pot n ns σ) := by
  obtain ⟨⟨hn, hoff, htgt, halv, helm, hdeg, hrnk, hidg, hbh, hbv, hbn⟩,
    helim, hbuck, hdn, hsc, hspc, hlsp, hmind, hkmax⟩ := hst
  obtain ⟨v₀, hv₀, hEv₀⟩ := helim.exists_alive hcnt
  have hmindn : σ.vars "mind" < n := helim.mind_lt hv₀ hEv₀
  have hSns : σ.vars "sc" ≤ ns := by rw [hsc]; exact scanned_sum_le hcsr.csr E
  have hbhlen : (σ.arrs "bh").length = n + 1 := by rw [hbh, length_arrOf]
  have hbhv : (σ.arrs "bh").getD (σ.vars "mind") 0 = BH (σ.vars "mind") := by
    rw [hbh, getD_arrOf BH (by omega)]
  have hbhB : (σ.arrs "bh").getD (σ.vars "mind") 0 < B := by rw [hbhv, hbh0]; omega
  have hnod : ∀ v < n, E v = 0 → D v ≠ σ.vars "mind" := fun v hv hEv => hbuck.no_deg hbh0 hv hEv
  have hmind1 : σ.vars "mind" + 1 ≤ n := by
    have h₁ := helim.min_le v₀ hv₀ hEv₀
    have h₂ := hnod v₀ hv₀ hEv₀
    have h₃ := hdn v₀ hv₀
    omega
  run_vcg [elimSkipMin_spec B]
  · -- the pointer moves up
    refine ⟨⟨E, D, R, ID, BH, BV, BN,
      ⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv], by simp [helm],
        by simp [hdeg], by simp [hrnk], by simp [hidg], by simp [hbh], by simp [hbv],
        by simp [hbn]⟩,
      by simpa using helim.bump hnod, by simpa using hbuck, hdn, by simpa using hsc,
      by simp; omega, by simp; omega, by simp; omega, by simp [hkmax]⟩, ?_⟩
    simp only [Pot, vars_setVar, ↓reduceIte, String.reduceEq]
    omega
  all_goals exfalso; omega

/-- **A stale slot is dropped.** The head slot of the bucket the pointer
names is popped, and its vertex turns out to be eliminated already or to
have moved to a smaller bucket since; nothing else happens. The turn is
paid out of the slot count, which the pop really does lower — that is
`Buck.pop`'s first answer. -/
theorem elimStale_run {B n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M E D R ID BH BV BN : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B) {σ : Env}
    (hst : ElimSt n ns G O T M E D R ID BH BV BN σ) (hcnt : σ.vars "cnt" < n)
    (hbh0 : BH (σ.vars "mind") ≠ 0)
    (hstale : ¬ (E (BV (BH (σ.vars "mind"))) = 0 ∧
      D (BV (BH (σ.vars "mind"))) = σ.vars "mind")) :
    ∃ σ' K, Run B elimTurn σ σ' K ∧ K ≤ 30 ∧
      (ElimInv n ns G O T M σ' ∧ Pot n ns σ' + 34 ≤ Pot n ns σ) := by
  obtain ⟨⟨hn, hoff, htgt, halv, helm, hdeg, hrnk, hidg, hbh, hbv, hbn⟩,
    helim, hbuck, hdn, hsc, hspc, hlsp, hmind, hkmax⟩ := hst
  obtain ⟨v₀, hv₀, hEv₀⟩ := helim.exists_alive hcnt
  have hmindn : σ.vars "mind" < n := helim.mind_lt hv₀ hEv₀
  have hSns : σ.vars "sc" ≤ ns := by rw [hsc]; exact scanned_sum_le hcsr.csr E
  have hbhlen : (σ.arrs "bh").length = n + 1 := by rw [hbh, length_arrOf]
  have hbvlen : (σ.arrs "bv").length = n + ns + 1 := by rw [hbv, length_arrOf]
  have hbnlen : (σ.arrs "bn").length = n + ns + 1 := by rw [hbn, length_arrOf]
  have hdeglen : (σ.arrs "deg").length = n := by rw [hdeg, length_arrOf]
  have helmlen : (σ.arrs "elm").length = n := by rw [helm, length_arrOf]
  have hbhv : (σ.arrs "bh").getD (σ.vars "mind") 0 = BH (σ.vars "mind") := by
    rw [hbh, getD_arrOf BH (by omega)]
  have hbhpos : 0 < BH (σ.vars "mind") := Nat.pos_of_ne_zero hbh0
  have hbhlt : BH (σ.vars "mind") < σ.vars "sp" := hbuck.head_lt _ (by omega)
  have hbhB : (σ.arrs "bh").getD (σ.vars "mind") 0 < B := by rw [hbhv]; omega
  have hwn : BV (BH (σ.vars "mind")) < n := hbuck.val_lt _ hbhpos hbhlt
  have hbnlt : BN (BH (σ.vars "mind")) < BH (σ.vars "mind") := hbuck.alloc _ hbhpos hbhlt
  have hbitw : E (BV (BH (σ.vars "mind"))) ≤ 1 := helim.bit _ hwn
  have hdnw : D (BV (BH (σ.vars "mind"))) < n := hdn _ hwn
  have hbvv : (σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0
      = BV (BH (σ.vars "mind")) := by rw [hbhv, hbv, getD_arrOf BV (by omega)]
  have hbvB : (σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 < B := by
    rw [hbvv]; omega
  have hbnv : (σ.arrs "bn").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0
      = BN (BH (σ.vars "mind")) := by rw [hbhv, hbn, getD_arrOf BN (by omega)]
  have hbnB : (σ.arrs "bn").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 < B := by
    rw [hbnv]; omega
  have helmv : (σ.arrs "elm").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0
      = E (BV (BH (σ.vars "mind"))) := by rw [hbvv, helm, getD_arrOf E hwn]
  have helmB : (σ.arrs "elm").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 < B := by
    rw [helmv]; omega
  have hdegvv : (σ.arrs "deg").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0
      = D (BV (BH (σ.vars "mind"))) := by rw [hbvv, hdeg, getD_arrOf D hwn]
  have hdegB : (σ.arrs "deg").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 < B := by
    rw [hdegvv]; omega
  have hout : ∀ v < n, E v = 0 → D v = σ.vars "mind" → v ≠ BV (BH (σ.vars "mind")) := by
    rintro v hv hEv hDv rfl
    exact hstale ⟨hEv, hDv⟩
  obtain ⟨hlspos, hpop⟩ := hbuck.pop (by omega) hbh0 E (fun _ _ h => h) hout
  run_vcg [elimSkipMin_spec B]
  · -- the bucket the pointer names is not empty
    exfalso; omega
  · -- the vertex is alive but has moved to a smaller bucket
    have hEq := ‹(_ : Env) = _›
    subst hEq
    refine ⟨⟨E, D, R, ID, upd BH (σ.vars "mind") (BN (BH (σ.vars "mind"))), BV, BN,
      ⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv], by simp [helm],
        by simp [hdeg], by simp [hrnk], by simp [hidg],
        by simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr, ↓reduceIte,
              String.reduceEq]
           rw [hbnv, hbh, set_arrOf_eq_upd],
        by simp [hbv], by simp [hbn]⟩,
      by simpa using helim, by simpa using hpop, hdn, by simpa using hsc,
      by simp; omega, by simp; omega, by simp [hmind], by simp [hkmax]⟩, ?_⟩
    simp only [Pot, vars_setVar, arrs_setVar, vars_setArr, ↓reduceIte, String.reduceEq]
    omega
  · -- the vertex has been eliminated already
    refine ⟨⟨E, D, R, ID, upd BH (σ.vars "mind") (BN (BH (σ.vars "mind"))), BV, BN,
      ⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv], by simp [helm],
        by simp [hdeg], by simp [hrnk], by simp [hidg],
        by simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr, ↓reduceIte,
              String.reduceEq]
           rw [hbnv, hbh, set_arrOf_eq_upd],
        by simp [hbv], by simp [hbn]⟩,
      by simpa using helim, by simpa using hpop, hdn, by simpa using hsc,
      by simp; omega, by simp; omega, by simp [hmind], by simp [hkmax]⟩, ?_⟩
    simp only [Pot, vars_setVar, arrs_setVar, vars_setArr, ↓reduceIte, String.reduceEq]
    omega
  all_goals simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr,
    ↓reduceIte, String.reduceEq] at *
  all_goals omega

/-- **What the row scan leaves is what `Elim.extract` asks for.** The
slots of the row of `w` name exactly its neighbours in the arena, so
"decremented by the scan" and "a neighbour in the arena" are the same
condition, once the vertex being taken is itself excluded — which
adjacency does for nothing. -/
theorem extract_of_scan {n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M E D D' : ℕ → ℕ} {w : ℕ}
    (hcsr : CsrSimple G ns O T) (hw : w < n) (hMw : M w ≠ 0)
    (hh : ∀ u < n, hit O T M (upd E w 1) w (O (w + 1)) u → D' u = D u - 1)
    (hnh : ∀ u < n, ¬ hit O T M (upd E w 1) w (O (w + 1)) u → D' u = D u) :
    (∀ u < n, E u = 0 → MAdj G M u w → D' u = D u - 1) ∧
      (∀ u < n, E u = 0 → ¬ MAdj G M u w → D' u = D u) := by
  refine ⟨fun u hu hEu hadj => hh u hu ⟨?_, hadj.alive_left, ?_⟩,
    fun u hu hEu hnadj => hnh u hu fun hcon => hnadj ?_⟩
  · have hne : u ≠ w := fun hc => G.ne_of_adj hadj.adj (by simp [hc])
    rw [upd_of_ne _ hne]; exact hEu
  · exact hcsr.csr.slot_of_madj (M := M) hadj.symm
  · obtain ⟨-, hM, t, h₁, h₂, h₃⟩ := hcon
    have hma := hcsr.csr.madj_of_slot hw h₁ h₂ hMw (by rw [h₃]; exact hM)
    rw [h₃] at hma
    exact hma.symm

set_option maxHeartbeats 4000000 in
/-- **The one turn that does anything.** The slot's vertex is
uneliminated and of the degree the pointer names, so it is taken:
stamped with the next rank down, its extraction degree recorded, and —
if it is alive in the arena — its row scanned. What the scan leaves is
`Elim.extract`'s two hypotheses, by `extract_of_scan`; the turn is paid
out of the extraction term of the potential, which also refunds the one
the pointer's drop costs. -/
theorem elimTake_run {B n ns : ℕ} {G : SimpleGraph (Fin n)}
    {O T M E D R ID BH BV BN : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B) (hMB : ∀ z < n, M z < B) {σ : Env}
    (hst : ElimSt n ns G O T M E D R ID BH BV BN σ) (hcnt : σ.vars "cnt" < n)
    (hbh0 : BH (σ.vars "mind") ≠ 0) (hEw : E (BV (BH (σ.vars "mind"))) = 0)
    (hDw : D (BV (BH (σ.vars "mind"))) = σ.vars "mind")
    (hMw : M (BV (BH (σ.vars "mind"))) ≠ 0) :
    ∃ σ' K, Run B elimTurn σ σ' K ∧
      K ≤ 73 + 52 * Csr.rowLen O (BV (BH (σ.vars "mind"))) ∧
      (ElimInv n ns G O T M σ' ∧
        Pot n ns σ' + 77 + 52 * Csr.rowLen O (BV (BH (σ.vars "mind"))) ≤ Pot n ns σ) := by
  obtain ⟨⟨hn, hoff, htgt, halv, helm, hdeg, hrnk, hidg, hbh, hbv, hbn⟩,
    helim, hbuck, hdn, hsc, hspc, hlsp, hmind, hkmax⟩ := hst
  obtain ⟨v₀, hv₀, hEv₀⟩ := helim.exists_alive hcnt
  have hmindn : σ.vars "mind" < n := helim.mind_lt hv₀ hEv₀
  have hSns : σ.vars "sc" ≤ ns := by rw [hsc]; exact scanned_sum_le hcsr.csr E
  have hbhlen : (σ.arrs "bh").length = n + 1 := by rw [hbh, length_arrOf]
  have hbvlen : (σ.arrs "bv").length = n + ns + 1 := by rw [hbv, length_arrOf]
  have hbnlen : (σ.arrs "bn").length = n + ns + 1 := by rw [hbn, length_arrOf]
  have hdeglen : (σ.arrs "deg").length = n := by rw [hdeg, length_arrOf]
  have helmlen : (σ.arrs "elm").length = n := by rw [helm, length_arrOf]
  have hrnklen : (σ.arrs "rnk").length = n := by rw [hrnk, length_arrOf]
  have hidglen : (σ.arrs "idg").length = n := by rw [hidg, length_arrOf]
  have halvlen : (σ.arrs "alv").length = n := by rw [halv, length_arrOf]
  have hbhv : (σ.arrs "bh").getD (σ.vars "mind") 0 = BH (σ.vars "mind") := by
    rw [hbh, getD_arrOf BH (by omega)]
  have hbhpos : 0 < BH (σ.vars "mind") := Nat.pos_of_ne_zero hbh0
  have hbhlt : BH (σ.vars "mind") < σ.vars "sp" := hbuck.head_lt _ (by omega)
  have hbhB : (σ.arrs "bh").getD (σ.vars "mind") 0 < B := by rw [hbhv]; omega
  have hwn : BV (BH (σ.vars "mind")) < n := hbuck.val_lt _ hbhpos hbhlt
  have hbnlt : BN (BH (σ.vars "mind")) < BH (σ.vars "mind") := hbuck.alloc _ hbhpos hbhlt
  have hdnw : D (BV (BH (σ.vars "mind"))) < n := hdn _ hwn
  have hbvv : (σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0
      = BV (BH (σ.vars "mind")) := by rw [hbhv, hbv, getD_arrOf BV (by omega)]
  have hbvB : (σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 < B := by
    rw [hbvv]; omega
  have hbnv : (σ.arrs "bn").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0
      = BN (BH (σ.vars "mind")) := by rw [hbhv, hbn, getD_arrOf BN (by omega)]
  have hbnB : (σ.arrs "bn").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 < B := by
    rw [hbnv]; omega
  have helmv : (σ.arrs "elm").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0
      = E (BV (BH (σ.vars "mind"))) := by rw [hbvv, helm, getD_arrOf E hwn]
  have helmB : (σ.arrs "elm").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 < B := by
    rw [helmv, hEw]; omega
  have hdegvv : (σ.arrs "deg").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0
      = D (BV (BH (σ.vars "mind"))) := by rw [hbvv, hdeg, getD_arrOf D hwn]
  have hdegB : (σ.arrs "deg").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 < B := by
    rw [hdegvv]; omega
  have halvv : (σ.arrs "alv").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0
      = M (BV (BH (σ.vars "mind"))) := by rw [hbvv, halv, getD_arrOf M hwn]
  have halvB : (σ.arrs "alv").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 < B := by
    rw [halvv]; exact hMB _ hwn
  have hbhv' : (σ.arrs "bh")[σ.vars "mind"]?.getD 0 = BH (σ.vars "mind") := by
    rw [← List.getD_eq_getElem?_getD]; exact hbhv
  have hbvv' : (σ.arrs "bv")[(σ.arrs "bh")[σ.vars "mind"]?.getD 0]?.getD 0
      = BV (BH (σ.vars "mind")) := by
    rw [hbhv', ← List.getD_eq_getElem?_getD, hbv, getD_arrOf BV (by omega)]
  have hbnv' : (σ.arrs "bn")[(σ.arrs "bh")[σ.vars "mind"]?.getD 0]?.getD 0
      = BN (BH (σ.vars "mind")) := by
    rw [hbhv', ← List.getD_eq_getElem?_getD, hbn, getD_arrOf BN (by omega)]
  have hOns : O (BV (BH (σ.vars "mind")) + 1) ≤ ns := hcsr.csr.le_ns (by omega)
  have hOw : O (BV (BH (σ.vars "mind"))) ≤ O (BV (BH (σ.vars "mind")) + 1) :=
    hcsr.csr.mono _ hwn
  have hcsrRel : Csr "off" "tgt" n ns n O T σ :=
    ⟨hoff, htgt, fun i hi => hcsr.csr.mono i hi, hcsr.csr.last,
      fun p hp => hcsr.csr.target_lt p hp⟩
  have hout : ∀ v < n, upd E (BV (BH (σ.vars "mind"))) 1 v = 0 →
      D v = σ.vars "mind" → v ≠ BV (BH (σ.vars "mind")) := by
    rintro v hv hEv - rfl
    rw [upd_self] at hEv
    omega
  obtain ⟨hlspos, hpop⟩ := hbuck.pop (by omega) hbh0 (upd E (BV (BH (σ.vars "mind"))) 1)
    (fun v hv hEv => by
      rw [upd_of_ne _ (fun hc => by rw [hc, upd_self] at hEv; omega)] at hEv; exact hEv)
    hout
  have hsum : ∑ v ∈ scanned n (upd E (BV (BH (σ.vars "mind"))) 1) M, Csr.rowLen O v
      = Csr.rowLen O (BV (BH (σ.vars "mind"))) + ∑ v ∈ scanned n E M, Csr.rowLen O v := by
    rw [scanned_upd_alive hwn hEw hMw, Finset.sum_insert (by simp [mem_scanned, hEw])]
  have hbite : ∀ u < n, upd E (BV (BH (σ.vars "mind"))) 1 u ≤ 1 := by
    intro u hu
    by_cases huw : u = BV (BH (σ.vars "mind"))
    · rw [huw, upd_self]
    · rw [upd_of_ne _ huw]; exact helim.bit u hu
  run_vcg [Csr.loadRow_spec B n ns n "off" "tgt" "w" "j" "jend" O T (by decide) (by decide),
    decScan_spec' (n := n) (ns := ns) (G := G) (O := O) (T := T) (M := M)
      (E := upd E (BV (BH (σ.vars "mind"))) 1)
      (R := upd R (BV (BH (σ.vars "mind"))) (n - 1 - σ.vars "cnt"))
      (ID := upd ID (BV (BH (σ.vars "mind"))) (σ.vars "mind")) (D₀ := D)
      (w := BV (BH (σ.vars "mind"))) (ls₀ := σ.vars "ls" - 1) (sc₀ := σ.vars "sc")
      (mv := σ.vars "mind") (kv := max (σ.vars "kmax") (σ.vars "mind"))
      (cv := σ.vars "cnt" + 1) hcsr hB hMB]
  · -- the bucket the pointer names is not empty
    exfalso; omega
  · -- the extraction, raising the bound
    obtain ⟨hdecI, hjend⟩ := ‹DecInv n ns O T M _ _ _ D _ _ _ _ _ _ _ ∧ _›
    obtain ⟨D', BH', BV', BN', ⟨hn2, hoff2, htgt2, halv2, helm2, hdeg2, hrnk2, hidg2,
      hbh2, hbv2, hbn2⟩, hbuck2, hbit2, hdn2, hhit2, hnhit2, hje2, hja2, hjb2, hsc2,
      hspc2, hlsp2, hls02, hmind2, hkmax2, hcnt2⟩ := hdecI
    rw [hjend] at hhit2 hnhit2 hsc2
    simp only [Nat.sub_self, Nat.add_zero] at hsc2
    obtain ⟨hdecl, hkeepl⟩ := extract_of_scan hcsr hwn hMw hhit2 hnhit2
    have hext := helim.extract hcnt hwn hEw hDw hdecl hkeepl
    have hscns2 : ∑ v ∈ scanned n (upd E (BV (BH (σ.vars "mind"))) 1) M, Csr.rowLen O v ≤ ns :=
      scanned_sum_le hcsr.csr _
    refine ⟨⟨upd E (BV (BH (σ.vars "mind"))) 1, D',
      upd R (BV (BH (σ.vars "mind"))) (n - 1 - σ.vars "cnt"),
      upd ID (BV (BH (σ.vars "mind"))) (σ.vars "mind"), BH', BV', BN',
      ⟨by simp [hn2], by simp [hoff2], by simp [htgt2], by simp [halv2], by simp [helm2],
        by simp [hdeg2], by simp [hrnk2], by simp [hidg2], by simp [hbh2], by simp [hbv2],
        by simp [hbn2]⟩,
      by simpa [hmind2, hkmax2, hcnt2] using hext, by simpa using hbuck2, hdn2,
      by simpa using hsc2, by simpa using hspc2, by simpa using hlsp2,
      by simp [hmind2]; omega, by simp [hkmax2]; omega⟩, ?_⟩
    simp only [Pot, vars_setVar, ↓reduceIte, String.reduceEq]
    omega
  · -- a dead vertex has no row, but this one is alive
    exfalso
    simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr, ↓reduceIte,
      String.reduceEq] at *
    omega
  · -- the extraction, the bound standing
    obtain ⟨hdecI, hjend⟩ := ‹DecInv n ns O T M _ _ _ D _ _ _ _ _ _ _ ∧ _›
    obtain ⟨D', BH', BV', BN', ⟨hn2, hoff2, htgt2, halv2, helm2, hdeg2, hrnk2, hidg2,
      hbh2, hbv2, hbn2⟩, hbuck2, hbit2, hdn2, hhit2, hnhit2, hje2, hja2, hjb2, hsc2,
      hspc2, hlsp2, hls02, hmind2, hkmax2, hcnt2⟩ := hdecI
    rw [hjend] at hhit2 hnhit2 hsc2
    simp only [Nat.sub_self, Nat.add_zero] at hsc2
    obtain ⟨hdecl, hkeepl⟩ := extract_of_scan hcsr hwn hMw hhit2 hnhit2
    have hext := helim.extract hcnt hwn hEw hDw hdecl hkeepl
    have hscns2 : ∑ v ∈ scanned n (upd E (BV (BH (σ.vars "mind"))) 1) M, Csr.rowLen O v ≤ ns :=
      scanned_sum_le hcsr.csr _
    refine ⟨⟨upd E (BV (BH (σ.vars "mind"))) 1, D',
      upd R (BV (BH (σ.vars "mind"))) (n - 1 - σ.vars "cnt"),
      upd ID (BV (BH (σ.vars "mind"))) (σ.vars "mind"), BH', BV', BN',
      ⟨by simp [hn2], by simp [hoff2], by simp [htgt2], by simp [halv2], by simp [helm2],
        by simp [hdeg2], by simp [hrnk2], by simp [hidg2], by simp [hbh2], by simp [hbv2],
        by simp [hbn2]⟩,
      by simpa [hmind2, hkmax2, hcnt2] using hext, by simpa using hbuck2, hdn2,
      by simpa using hsc2, by simpa using hspc2, by simpa using hlsp2,
      by simp [hmind2]; omega, by simp [hkmax2]; omega⟩, ?_⟩
    simp only [Pot, vars_setVar, ↓reduceIte, String.reduceEq]
    omega
  · -- a dead vertex has no row, but this one is alive
    exfalso
    simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr, ↓reduceIte,
      String.reduceEq] at *
    omega
  · -- the vertex is of the degree the pointer names
    exfalso
    simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr, ↓reduceIte,
      String.reduceEq] at *
    omega
  · -- the vertex is not eliminated
    exfalso
    simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr, ↓reduceIte,
      String.reduceEq] at *
    omega
  all_goals simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr,
    ↓reduceIte, String.reduceEq] at *
  all_goals try omega
  · -- the row of the vertex, loaded
    exact ⟨⟨hcsrRel.of_eq (by simp) (by simp), by omega, by omega⟩, by omega, by omega⟩
  · -- the scan starts at the top of the row, in the state the extraction left
    obtain ⟨-, hjl, hjel, rfl⟩ :=
      ‹Csr.LoadRowPost "off" "tgt" "w" "j" "jend" n ns n O T _ _›
    refine ⟨hwn, ⟨D, upd BH (σ.vars "mind") (BN (BH (σ.vars "mind"))), BV, BN,
      ⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv],
        by simp only [arrs_setVar, arrs_setArr, vars_setArr, vars_setVar, ↓reduceIte,
              String.reduceEq]
           rw [hbvv, helm, set_arrOf_eq_upd],
        by simp [hdeg],
        by simp only [arrs_setVar, arrs_setArr, vars_setArr, vars_setVar, ↓reduceIte,
              String.reduceEq]
           rw [hbvv, hn, hrnk, set_arrOf_eq_upd],
        by simp only [arrs_setVar, arrs_setArr, vars_setArr, vars_setVar, ↓reduceIte,
              String.reduceEq]
           rw [hbvv, hidg, set_arrOf_eq_upd],
        by simp only [arrs_setVar, arrs_setArr, vars_setArr, vars_setVar, ↓reduceIte,
              String.reduceEq]
           rw [hbnv, hbh, set_arrOf_eq_upd],
        by simp [hbv], by simp [hbn]⟩,
      by simpa using hpop, hbite, hdn,
      fun u hu hh => absurd hh
        (by rintro ⟨-, -, t, h₁, h₂, -⟩; simp [hbvv'] at h₂; omega),
      fun u _ _ => rfl,
      by simp [hbvv'], by simp [hbvv'], by simp [hbvv']; omega,
      by simp only [vars_setVar, vars_setArr, ↓reduceIte, String.reduceEq, hbvv]
         rw [hsum, hsc]; simp only [Csr.rowLen]; omega,
      by simp; omega, by simp; omega, by simp,
      by simp, ?_, by simp⟩, by simp [hbvv']⟩
    simp only [vars_setVar, vars_setArr, ↓reduceIte, String.reduceEq, Nat.max_def]
    split <;> omega
  · -- the pointer is a word after the scan
    obtain ⟨hd, -⟩ := ‹DecInv n ns O T M _ _ _ D _ _ _ _ _ _ _ ∧ _›
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hm2, -, -⟩ := hd
    omega
  · -- and stays one when it drops
    obtain ⟨hd, -⟩ := ‹DecInv n ns O T M _ _ _ D _ _ _ _ _ _ _ ∧ _›
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hm2, -, -⟩ := hd
    omega
  · -- the row of the vertex, loaded
    exact ⟨⟨hcsrRel.of_eq (by simp) (by simp), by omega, by omega⟩, by omega, by omega⟩
  · -- the scan starts at the top of the row, in the state the extraction left
    obtain ⟨-, hjl, hjel, rfl⟩ :=
      ‹Csr.LoadRowPost "off" "tgt" "w" "j" "jend" n ns n O T _ _›
    refine ⟨hwn, ⟨D, upd BH (σ.vars "mind") (BN (BH (σ.vars "mind"))), BV, BN,
      ⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv],
        by simp only [arrs_setVar, arrs_setArr, vars_setArr, vars_setVar, ↓reduceIte,
              String.reduceEq]
           rw [hbvv, helm, set_arrOf_eq_upd],
        by simp [hdeg],
        by simp only [arrs_setVar, arrs_setArr, vars_setArr, vars_setVar, ↓reduceIte,
              String.reduceEq]
           rw [hbvv, hn, hrnk, set_arrOf_eq_upd],
        by simp only [arrs_setVar, arrs_setArr, vars_setArr, vars_setVar, ↓reduceIte,
              String.reduceEq]
           rw [hbvv, hidg, set_arrOf_eq_upd],
        by simp only [arrs_setVar, arrs_setArr, vars_setArr, vars_setVar, ↓reduceIte,
              String.reduceEq]
           rw [hbnv, hbh, set_arrOf_eq_upd],
        by simp [hbv], by simp [hbn]⟩,
      by simpa using hpop, hbite, hdn,
      fun u hu hh => absurd hh
        (by rintro ⟨-, -, t, h₁, h₂, -⟩; simp [hbvv'] at h₂; omega),
      fun u _ _ => rfl,
      by simp [hbvv'], by simp [hbvv'], by simp [hbvv']; omega,
      by simp only [vars_setVar, vars_setArr, ↓reduceIte, String.reduceEq, hbvv]
         rw [hsum, hsc]; simp only [Csr.rowLen]; omega,
      by simp; omega, by simp; omega, by simp,
      by simp, ?_, by simp⟩, by simp [hbvv']⟩
    simp only [vars_setVar, vars_setArr, ↓reduceIte, String.reduceEq, Nat.max_def]
    split <;> omega
  · -- the pointer is a word after the scan
    obtain ⟨hd, -⟩ := ‹DecInv n ns O T M _ _ _ D _ _ _ _ _ _ _ ∧ _›
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hm2, -, -⟩ := hd
    omega
  · -- and stays one when it drops
    obtain ⟨hd, -⟩ := ‹DecInv n ns O T M _ _ _ D _ _ _ _ _ _ _ ∧ _›
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hm2, -, -⟩ := hd
    omega

/-- **A dead vertex has no row to scan.** Stated as a specification so
that the turn which takes one is walked without entering the scan at
all — which is right, since the arena isolates it. -/
theorem elimSkipRow_spec (B : ℕ) (h0 : 0 < B) :
    Spec B (fun τ => τ.vars "w" < (τ.arrs "alv").length ∧
        (τ.arrs "alv").getD (τ.vars "w") 0 < B ∧ τ.vars "w" < B ∧
        (τ.arrs "alv").getD (τ.vars "w") 0 = 0)
      (.ite (.lt (.lit 0) (.get "alv" (.var "w")))
        (.seq (Csr.loadRow "off" "w" "j" "jend") (Csr.scan "j" "jend" decSlot)) .skip)
      (fun τ τ' => τ' = τ) 6 := by
  rintro τ ⟨hlen, hval, hwB, hzero⟩
  have hb : (Cond.lt (.lit 0) (.get "alv" (.var "w"))).evalB B τ = some false := by
    rw [evalB_condLt (evalB_lit h0)
      (RunStep.eval_get B τ "alv" (.var "w") (τ.vars "w") (evalB_var hwB) hlen hval)]
    simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero_eq]
    exact hzero
  exact ⟨τ, (Run.ite_false hb Run.skip).mono (by simp), rfl⟩

set_option maxHeartbeats 1000000 in
/-- **The one turn that does anything, on a vertex the mask killed.**
Everything is as in `elimTake_run` but the row: a dead vertex is
isolated in the arena, so it has no neighbours to tell and the scan is
skipped. -/
theorem elimTakeDead_run {B n ns : ℕ} {G : SimpleGraph (Fin n)}
    {O T M E D R ID BH BV BN : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B) (hMB : ∀ z < n, M z < B) {σ : Env}
    (hst : ElimSt n ns G O T M E D R ID BH BV BN σ) (hcnt : σ.vars "cnt" < n)
    (hbh0 : BH (σ.vars "mind") ≠ 0) (hEw : E (BV (BH (σ.vars "mind"))) = 0)
    (hDw : D (BV (BH (σ.vars "mind"))) = σ.vars "mind")
    (hMw : M (BV (BH (σ.vars "mind"))) = 0) :
    ∃ σ' K, Run B elimTurn σ σ' K ∧ K ≤ 73 ∧
      (ElimInv n ns G O T M σ' ∧ Pot n ns σ' + 77 ≤ Pot n ns σ) := by
  obtain ⟨⟨hn, hoff, htgt, halv, helm, hdeg, hrnk, hidg, hbh, hbv, hbn⟩,
    helim, hbuck, hdn, hsc, hspc, hlsp, hmind, hkmax⟩ := hst
  obtain ⟨v₀, hv₀, hEv₀⟩ := helim.exists_alive hcnt
  have hmindn : σ.vars "mind" < n := helim.mind_lt hv₀ hEv₀
  have hSns : σ.vars "sc" ≤ ns := by rw [hsc]; exact scanned_sum_le hcsr.csr E
  have hbhlen : (σ.arrs "bh").length = n + 1 := by rw [hbh, length_arrOf]
  have hbvlen : (σ.arrs "bv").length = n + ns + 1 := by rw [hbv, length_arrOf]
  have hbnlen : (σ.arrs "bn").length = n + ns + 1 := by rw [hbn, length_arrOf]
  have hdeglen : (σ.arrs "deg").length = n := by rw [hdeg, length_arrOf]
  have helmlen : (σ.arrs "elm").length = n := by rw [helm, length_arrOf]
  have hrnklen : (σ.arrs "rnk").length = n := by rw [hrnk, length_arrOf]
  have hidglen : (σ.arrs "idg").length = n := by rw [hidg, length_arrOf]
  have halvlen : (σ.arrs "alv").length = n := by rw [halv, length_arrOf]
  have hbhv : (σ.arrs "bh").getD (σ.vars "mind") 0 = BH (σ.vars "mind") := by
    rw [hbh, getD_arrOf BH (by omega)]
  have hbhpos : 0 < BH (σ.vars "mind") := Nat.pos_of_ne_zero hbh0
  have hbhlt : BH (σ.vars "mind") < σ.vars "sp" := hbuck.head_lt _ (by omega)
  have hbhB : (σ.arrs "bh").getD (σ.vars "mind") 0 < B := by rw [hbhv]; omega
  have hwn : BV (BH (σ.vars "mind")) < n := hbuck.val_lt _ hbhpos hbhlt
  have hbnlt : BN (BH (σ.vars "mind")) < BH (σ.vars "mind") := hbuck.alloc _ hbhpos hbhlt
  have hdnw : D (BV (BH (σ.vars "mind"))) < n := hdn _ hwn
  have hbvv : (σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0
      = BV (BH (σ.vars "mind")) := by rw [hbhv, hbv, getD_arrOf BV (by omega)]
  have hbvB : (σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 < B := by
    rw [hbvv]; omega
  have hbnv : (σ.arrs "bn").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0
      = BN (BH (σ.vars "mind")) := by rw [hbhv, hbn, getD_arrOf BN (by omega)]
  have hbnB : (σ.arrs "bn").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 < B := by
    rw [hbnv]; omega
  have helmv : (σ.arrs "elm").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0
      = E (BV (BH (σ.vars "mind"))) := by rw [hbvv, helm, getD_arrOf E hwn]
  have helmB : (σ.arrs "elm").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 < B := by
    rw [helmv, hEw]; omega
  have hdegvv : (σ.arrs "deg").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0
      = D (BV (BH (σ.vars "mind"))) := by rw [hbvv, hdeg, getD_arrOf D hwn]
  have hdegB : (σ.arrs "deg").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 < B := by
    rw [hdegvv]; omega
  have halvv : (σ.arrs "alv").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0
      = M (BV (BH (σ.vars "mind"))) := by rw [hbvv, halv, getD_arrOf M hwn]
  have halvB : (σ.arrs "alv").getD
      ((σ.arrs "bv").getD ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 < B := by
    rw [halvv]; exact hMB _ hwn
  have hout : ∀ v < n, upd E (BV (BH (σ.vars "mind"))) 1 v = 0 →
      D v = σ.vars "mind" → v ≠ BV (BH (σ.vars "mind")) := by
    rintro v hv hEv - rfl
    rw [upd_self] at hEv
    omega
  obtain ⟨hlspos, hpop⟩ := hbuck.pop (by omega) hbh0 (upd E (BV (BH (σ.vars "mind"))) 1)
    (fun v hv hEv => by
      rw [upd_of_ne _ (fun hc => by rw [hc, upd_self] at hEv; omega)] at hEv; exact hEv)
    hout
  have hscd : scanned n (upd E (BV (BH (σ.vars "mind"))) 1) M = scanned n E M :=
    scanned_upd_dead hMw
  have hext := helim.extract hcnt hwn hEw hDw
    (fun u _ _ hadj => absurd hMw hadj.alive_right) (fun _ _ _ _ => rfl)
  run_vcg [elimSkipRow_spec B (by omega)]
  · exfalso; omega
  · -- the extraction, raising the bound
    have hEq := ‹(_ : Env) = _›
    subst hEq
    simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr, ↓reduceIte,
      String.reduceEq] at *
    rw [Nat.max_eq_right (by omega : σ.vars "kmax" ≤ σ.vars "mind")] at hext
    refine ⟨⟨upd E (BV (BH (σ.vars "mind"))) 1, D,
      upd R (BV (BH (σ.vars "mind"))) (n - 1 - σ.vars "cnt"),
      upd ID (BV (BH (σ.vars "mind"))) (σ.vars "mind"),
      upd BH (σ.vars "mind") (BN (BH (σ.vars "mind"))), BV, BN,
      ⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv],
        by simp only [arrs_setVar, arrs_setArr, ↓reduceIte, String.reduceEq]
           rw [hbvv, helm, set_arrOf_eq_upd],
        by simp [hdeg],
        by simp only [arrs_setVar, arrs_setArr, ↓reduceIte, String.reduceEq]
           rw [hbvv, hn, hrnk, set_arrOf_eq_upd],
        by simp only [arrs_setVar, arrs_setArr, ↓reduceIte, String.reduceEq]
           rw [hbvv, hidg, set_arrOf_eq_upd],
        by simp only [arrs_setVar, arrs_setArr, ↓reduceIte, String.reduceEq]
           rw [hbnv, hbh, set_arrOf_eq_upd],
        by simp [hbv], by simp [hbn]⟩,
      by simpa using hext, by simpa using hpop, hdn, by simp [hscd, hsc],
      by simp; omega, by simp; omega, by simp; omega, by simp; omega⟩, ?_⟩
    simp only [Pot, vars_setVar, vars_setArr, ↓reduceIte, String.reduceEq]
    omega
  · -- the extraction, the bound standing
    have hEq := ‹(_ : Env) = _›
    subst hEq
    simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr, ↓reduceIte,
      String.reduceEq] at *
    rw [Nat.max_eq_left (by omega : σ.vars "mind" ≤ σ.vars "kmax")] at hext
    refine ⟨⟨upd E (BV (BH (σ.vars "mind"))) 1, D,
      upd R (BV (BH (σ.vars "mind"))) (n - 1 - σ.vars "cnt"),
      upd ID (BV (BH (σ.vars "mind"))) (σ.vars "mind"),
      upd BH (σ.vars "mind") (BN (BH (σ.vars "mind"))), BV, BN,
      ⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv],
        by simp only [arrs_setVar, arrs_setArr, ↓reduceIte, String.reduceEq]
           rw [hbvv, helm, set_arrOf_eq_upd],
        by simp [hdeg],
        by simp only [arrs_setVar, arrs_setArr, ↓reduceIte, String.reduceEq]
           rw [hbvv, hn, hrnk, set_arrOf_eq_upd],
        by simp only [arrs_setVar, arrs_setArr, ↓reduceIte, String.reduceEq]
           rw [hbvv, hidg, set_arrOf_eq_upd],
        by simp only [arrs_setVar, arrs_setArr, ↓reduceIte, String.reduceEq]
           rw [hbnv, hbh, set_arrOf_eq_upd],
        by simp [hbv], by simp [hbn]⟩,
      by simpa using hext, by simpa using hpop, hdn, by simp [hscd, hsc],
      by simp; omega, by simp; omega, by simp; omega, by simp; omega⟩, ?_⟩
    simp only [Pot, vars_setVar, vars_setArr, ↓reduceIte, String.reduceEq]
    omega
  · exfalso
    simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr, ↓reduceIte,
      String.reduceEq] at *
    omega
  · exfalso
    simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr, ↓reduceIte,
      String.reduceEq] at *
    omega
  all_goals simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr,
    ↓reduceIte, String.reduceEq] at *
  all_goals first
    | omega
    | (have hEq := ‹(_ : Env) = _›
       subst hEq
       simp only [vars_setVar, vars_setArr, ↓reduceIte, String.reduceEq] at *
       omega)

/-- **A turn of the elimination.** The four cases the bucket relation
and the invariant leave: an empty bucket, a stale slot, and an
extraction on a live or on a dead vertex. Each pays for itself out of
the potential, which is what the loop rule asks. -/
theorem elimTurn_run {B n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B) (hMB : ∀ z < n, M z < B) {σ : Env}
    (hI : ElimInv n ns G O T M σ) (hcnt : σ.vars "cnt" < n) :
    ∃ σ' K, Run B elimTurn σ σ' K ∧ ElimInv n ns G O T M σ' ∧
      4 + K + Pot n ns σ' ≤ Pot n ns σ := by
  obtain ⟨E, D, R, ID, BH, BV, BN, hst⟩ := hI
  by_cases hbh0 : BH (σ.vars "mind") = 0
  · obtain ⟨σ', K, hrun, hK, hI', hpot⟩ := elimBump_run hcsr hB hst hcnt hbh0
    exact ⟨σ', K, hrun, hI', by omega⟩
  · by_cases htake : E (BV (BH (σ.vars "mind"))) = 0 ∧
        D (BV (BH (σ.vars "mind"))) = σ.vars "mind"
    · by_cases hMw : M (BV (BH (σ.vars "mind"))) = 0
      · obtain ⟨σ', K, hrun, hK, hI', hpot⟩ :=
          elimTakeDead_run hcsr hB hMB hst hcnt hbh0 htake.1 htake.2 hMw
        exact ⟨σ', K, hrun, hI', by omega⟩
      · obtain ⟨σ', K, hrun, hK, hI', hpot⟩ :=
          elimTake_run hcsr hB hMB hst hcnt hbh0 htake.1 htake.2 hMw
        exact ⟨σ', K, hrun, hI', by omega⟩
    · obtain ⟨σ', K, hrun, hK, hI', hpot⟩ := elimStale_run hcsr hB hst hcnt hbh0 htake
      exact ⟨σ', K, hrun, hI', by omega⟩

/-- **What the loop leaves, read at its exit.** The test having failed,
`cnt` stands at `n`, and every clause the rest of the program wants is
read off the invariant at that point: `Elim.cert` is the certificate,
`Elim.taken` says the recorded extraction degree of a vertex is the
in-degree the orientation gives it, and the same clause bounds the
recorded degrees by the rows they were counted from — which is what
puts the whole in-list array inside the target array, `psum ID n ≤ ns`,
the bound the two remaining passes are written against. -/
theorem elimExit_read {B n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) {τ : Env} (hI : ElimInv n ns G O T M τ)
    (hfalse : (Cond.lt (Expr.var "cnt") (Expr.var "n")).evalB B τ = some false) :
    ∃ R ID k, τ.vars "n" = n ∧ τ.vars "kmax" = k ∧ τ.arrs "rnk" = arrOf n R ∧
      τ.arrs "idg" = arrOf n ID ∧ (∀ v < n, R v < n) ∧
      ElimCert (masked G M) (fun v : Fin n => R (v : ℕ)) k ∧
      (∀ w : Fin n, ID (w : ℕ) =
        ((ElimCert.elimOr (masked G M) (fun v : Fin n => R (v : ℕ))).inN w).card) ∧
      psum ID n ≤ ns := by
  obtain ⟨E, D, R, ID, BH, BV, BN, harr, helim, hbuck, hDlt, hsc, hspb, hlsb, hmind, hkmax⟩ := hI
  obtain ⟨hn, hoff, htgt, halv, helm, hdeg, hrnk, hidg, hbh, hbv, hbn⟩ := harr
  have hcntn : τ.vars "cnt" = n := by
    have h1 := le_of_condLt_false hfalse
    have h2 := helim.cnt_le
    omega
  rw [hcntn] at helim
  have hcert := helim.cert
  have hall : ∀ v < n, E v = 1 := fun v hv => helim.all_elim ⟨v, hv⟩
  -- the recorded extraction degree is the in-degree of the orientation
  have hID : ∀ w : Fin n, ID (w : ℕ) =
      ((ElimCert.elimOr (masked G M) (fun v : Fin n => R (v : ℕ))).inN w).card := by
    intro w
    have h1 := helim.taken w (helim.all_elim w)
    have h2 := helim.survOf_eq_surv w
    have h4 : (ElimCert.elimOr (masked G M) (fun v : Fin n => R (v : ℕ))).inN w
        = nbrsIn (masked G M) (surv (fun v : Fin n => R (v : ℕ)) (R (w : ℕ))) w :=
      (curNbrs_eq_backNbrs hcert.inj w).symm
    rw [h1, h2, h4]
  -- and it fits inside the row it was counted from, or is nought at a dead vertex
  have hIDrow : ∀ v ∈ Finset.range n,
      ID v ≤ (if E v = 1 ∧ M v ≠ 0 then Csr.rowLen O v else 0) := by
    intro v hv
    have hvn : v < n := Finset.mem_range.1 hv
    have h1 := helim.taken ⟨v, hvn⟩ (helim.all_elim ⟨v, hvn⟩)
    have hsub : nbrsIn (masked G M) (survOf E R (R v + 1)) (⟨v, hvn⟩ : Fin n) ⊆
        nbrsIn (masked G M) Finset.univ (⟨v, hvn⟩ : Fin n) := fun u hu =>
      mem_nbrsIn.2 ⟨Finset.mem_univ _, (mem_nbrsIn.1 hu).2⟩
    have h2 : ID v ≤ adeg G M v := by
      rw [h1, adeg_eq hvn]; exact Finset.card_le_card hsub
    by_cases hM : M v = 0
    · rw [adeg_of_dead hvn hM] at h2
      simp [hM]
      omega
    · rw [if_pos ⟨hall v hvn, hM⟩]
      refine le_trans h2 ?_
      rw [adeg_of_alive hcsr hvn hM]
      calc (liveSlots O T M v).card ≤ (Finset.Ico (O v) (O (v + 1))).card :=
            Finset.card_filter_le _ _
        _ = Csr.rowLen O v := by rw [Nat.card_Ico]; rfl
  have hpsum : psum ID n ≤ ns := by
    have hle : ∑ v ∈ Finset.range n, ID v ≤ ∑ v ∈ scanned n E M, Csr.rowLen O v := by
      rw [scanned, Finset.sum_filter]
      exact Finset.sum_le_sum hIDrow
    exact le_trans hle (scanned_sum_le hcsr.csr E)
  exact ⟨R, ID, τ.vars "kmax", hn, rfl, hrnk, hidg,
    fun v hv => helim.rank_lt v hv (hall v hv), hcert, hID, hpsum⟩

/-- **The elimination, walked.** The four counters are set, and then the
loop is `Spec.while_potential` with `elimTurn_run` as its step: every
turn pays four plus its own cost out of `Pot`, which is what the rule
asks for. The invariant holds at entry by `Elim.init` — nothing
eliminated, the degree array holding the arena degrees `initDeg` left,
and the buckets `initBuck` filled, weakened to the flags by
`Buck.weaken` — and `Pot` at *any* state of the invariant is at most
`160 n + 100 ns + 40`, since `ls + 1 ≤ sp ≤ n + 1 + sc` bounds the
arena's slot count by the slots already scanned. The four assignments
cost eight and the loop's last test four. -/
theorem elimLoop_spec (B n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M D : ℕ → ℕ)
    (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B) (hMB : ∀ z < n, M z < B)
    (hDadeg : ∀ v < n, D v = adeg G M v) :
    Spec B (fun σ => BuckInv n ns D σ ∧ σ.vars "i" = n ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
        σ.arrs "alv" = arrOf n M ∧
        (∃ g, σ.arrs "elm" = arrOf n g ∧ ∀ j < n, g j = 0) ∧
        (∃ g, σ.arrs "rnk" = arrOf n g) ∧ (∃ g, σ.arrs "idg" = arrOf n g))
      elimLoop
      (fun _ σ' => ∃ R ID k, σ'.vars "n" = n ∧ σ'.vars "kmax" = k ∧
        σ'.arrs "rnk" = arrOf n R ∧ σ'.arrs "idg" = arrOf n ID ∧ (∀ v < n, R v < n) ∧
        ElimCert (masked G M) (fun v : Fin n => R (v : ℕ)) k ∧
        (∀ w : Fin n, ID (w : ℕ) =
          ((ElimCert.elimOr (masked G M) (fun v : Fin n => R (v : ℕ))).inN w).card) ∧
        psum ID n ≤ ns)
      (160 * n + 100 * ns + 52) := by
  have hDlt : ∀ v < n, D v < n := by
    intro v hv
    rw [hDadeg v hv, adeg_eq hv]
    exact card_nbrsIn_lt _ _
  have hDcard : ∀ v : Fin n, D (v : ℕ) = (nbrsIn (masked G M) Finset.univ v).card := by
    intro v
    rw [hDadeg (v : ℕ) v.isLt, adeg_eq (G := G) (M := M) v.isLt]
  have hloop : Spec B (ElimInv n ns G O T M)
      (.while (.lt (.var "cnt") (.var "n")) elimTurn)
      (fun _ σ' => ElimInv n ns G O T M σ' ∧
        (Cond.lt (Expr.var "cnt") (Expr.var "n")).evalB B σ' = some false)
      (160 * n + 100 * ns + 44) := by
    refine Spec.while_potential (ElimInv n ns G O T M) (Pot n ns) ?_ ?_ (fun _ h => h) ?_
    · rintro σ ⟨E, D', R, ID, BH, BV, BN, hst⟩
      have hn : σ.vars "n" = n := hst.1.1
      have hcnt := hst.2.1.cnt_le
      exact evalB_condLt_vars (by omega) (by omega)
    · intro σ hI hb
      have hcnt : σ.vars "cnt" < n := by
        obtain ⟨E, D', R, ID, BH, BV, BN, hst⟩ := id hI
        have h := lt_of_condLt_true hb
        rw [hst.1.1] at h; exact h
      obtain ⟨σ', K, hrun, hI', hpot⟩ := elimTurn_run hcsr hB hMB hI hcnt
      refine ⟨σ', K, hrun, hI', ?_⟩
      simp only [size_condLt, size_var]
      omega
    · -- the potential of *any* state of the invariant is inside the budget
      rintro σ ⟨E, D', R, ID, BH, BV, BN, hst⟩
      have hsc : σ.vars "sc" ≤ ns := by
        rw [hst.2.2.2.2.1]; exact scanned_sum_le hcsr.csr E
      have h1 := hst.2.2.2.2.2.1
      have h2 := hst.2.2.2.2.2.2.1
      simp only [Pot, size_condLt, size_var]
      omega
  run_vcg [hloop]
  · -- the exit: `cnt` stands at `n`, and the certificate is read off the state
    exact elimExit_read hcsr ‹ElimInv n ns G O T M _ ∧ _›.1 ‹ElimInv n ns G O T M _ ∧ _›.2
  · -- the state the loop starts in: nothing eliminated, the degrees true, one slot per vertex
    obtain ⟨hn, hdeg, hile, hsp, hls, BH, BV, BN, hbh, hbv, hbn, hbuck⟩ := ‹BuckInv n ns D σ›
    obtain ⟨E, helm, hE⟩ := ‹∃ g, σ.arrs "elm" = arrOf n g ∧ ∀ j < n, g j = 0›
    obtain ⟨R, hrnk⟩ := ‹∃ g, σ.arrs "rnk" = arrOf n g›
    obtain ⟨ID, hidg⟩ := ‹∃ g, σ.arrs "idg" = arrOf n g›
    have hi : σ.vars "i" = n := ‹σ.vars "i" = n›
    have hscan : scanned n E M = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
      have h := mem_scanned.1 hv
      rw [hE v h.1] at h
      omega
    refine ⟨E, D, R, ID, BH, BV, BN,
      ⟨by simp [hn], by simp [‹σ.arrs "off" = arrOf (n + 1) O›],
        by simp [‹σ.arrs "tgt" = arrOf ns T›], by simp [‹σ.arrs "alv" = arrOf n M›],
        by simp [helm], by simp [hdeg], by simp [hrnk], by simp [hidg], by simp [hbh],
        by simp [hbv], by simp [hbn]⟩,
      ?_, ?_, hDlt, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using Elim.init (G := G) (M := M) (R := R) (ID := ID) hE hDcard
    · simpa [hi, hsp, hls] using (hbuck.weaken E)
    · simp [hscan]
    · simp [hsp, hi]
    · simp [hsp, hls, hi]
    · simp
    · simp

/-! #### The in-lists, filled

The last pass is a counting sort. Every live vertex's row is walked once
more and every slot naming a live target of *smaller* rank — that is,
every in-neighbour of the row's vertex in the elimination orientation —
is written at the row's fill pointer, which then moves on. What the
scan has written of a row is `written`, and `written_last` is the whole
content of the pass: at the end of the row that set is the block
`InCsr` asks for. The pointer stays inside its own block because the
row names each neighbour once, so the set grows by one at each write
and never overtakes `ID w`, the block's length. -/

/-- Every slot of the in-list array is in the block of some vertex,
which is what turns "every block names vertices" into `InCsr`'s
`target_lt`. -/
theorem exists_block {ID : ℕ → ℕ} {m t : ℕ} (ht : t < psum ID m) :
    ∃ w < m, psum ID w ≤ t ∧ t < psum ID (w + 1) := by
  induction m with
  | zero => simp at ht
  | succ m ih =>
      rcases Nat.lt_or_ge t (psum ID m) with hlt | hge
      · obtain ⟨w, hw, h₁, h₂⟩ := ih hlt
        exact ⟨w, by omega, h₁, h₂⟩
      · exact ⟨m, by omega, hge, ht⟩

/-- An in-neighbour of `w` the fill has already written: alive, of
smaller rank, and named by a slot the scan has passed. -/
def fhit (O T M R : ℕ → ℕ) (w j u : ℕ) : Prop :=
  M u ≠ 0 ∧ R u < R w ∧ ∃ t, O w ≤ t ∧ t < j ∧ T t = u

/-- The in-neighbours of `w` written out so far: what the fill pointer
counts, and — at the end of the row — the block itself. -/
noncomputable def written {n : ℕ} (O T M R : ℕ → ℕ) (w j : ℕ) : Finset (Fin n) :=
  pick (fun u : Fin n => fhit O T M R w j (u : ℕ))

theorem mem_written {O T M R : ℕ → ℕ} {w j : ℕ} {u : Fin n} :
    u ∈ written (n := n) O T M R w j ↔ fhit O T M R w j (u : ℕ) := mem_pick

@[simp] theorem written_start (O T M R : ℕ → ℕ) (w : ℕ) :
    written (n := n) O T M R w (O w) = ∅ :=
  Finset.eq_empty_of_forall_notMem fun u hu => by
    obtain ⟨-, -, t, h₁, h₂, -⟩ := mem_written.1 hu
    omega

/-- A slot that writes nothing leaves the set alone. -/
theorem written_succ_of_skip {R : ℕ → ℕ} {w j : ℕ}
    (hno : ¬ (M (T j) ≠ 0 ∧ R (T j) < R w)) :
    written (n := n) O T M R w (j + 1) = written (n := n) O T M R w j := by
  ext u
  simp only [mem_written, fhit]
  constructor
  · rintro ⟨hM, hR, t, h₁, h₂, h₃⟩
    rcases Nat.lt_or_ge t j with hlt | hge
    · exact ⟨hM, hR, t, h₁, hlt, h₃⟩
    · exact absurd ⟨by rw [show j = t by omega, h₃]; exact hM,
        by rw [show j = t by omega, h₃]; exact hR⟩ hno
  · rintro ⟨hM, hR, t, h₁, h₂, h₃⟩
    exact ⟨hM, hR, t, h₁, by omega, h₃⟩

/-- And a slot that writes adds exactly its target. -/
theorem written_succ_of_take {R : ℕ → ℕ} {w j : ℕ} (hw : O w ≤ j) (htn : T j < n)
    (hM : M (T j) ≠ 0) (hR : R (T j) < R w) :
    written (n := n) O T M R w (j + 1)
      = insert (⟨T j, htn⟩ : Fin n) (written (n := n) O T M R w j) := by
  ext u
  simp only [mem_written, Finset.mem_insert, fhit]
  constructor
  · rintro ⟨hM', hR', t, h₁, h₂, h₃⟩
    rcases Nat.lt_or_ge t j with hlt | hge
    · exact Or.inr ⟨hM', hR', t, h₁, hlt, h₃⟩
    · exact Or.inl (Fin.ext (by rw [← h₃, show t = j by omega]))
  · rintro (rfl | ⟨hM', hR', t, h₁, h₂, h₃⟩)
    · exact ⟨hM, hR, j, hw, by omega, rfl⟩
    · exact ⟨hM', hR', t, h₁, by omega, h₃⟩

/-- **The slot the scan stands at has not been written yet**: the row
names each neighbour once, so the set really does grow by one. -/
theorem not_mem_written (hcsr : CsrSimple G ns O T) {R : ℕ → ℕ} {w j : ℕ} (hw : w < n)
    (h₁ : O w ≤ j) (h₂ : j < O (w + 1)) (htn : T j < n) :
    (⟨T j, htn⟩ : Fin n) ∉ written (n := n) O T M R w j := by
  intro hmem
  obtain ⟨-, -, t, ht₁, ht₂, ht₃⟩ := mem_written.1 hmem
  have := hcsr.nodup w hw t j ht₁ (by omega) h₁ h₂ ht₃
  omega

/-- A dead vertex carries no arcs, so its block is empty and the pass
has nothing to do at it. -/
theorem inN_of_dead {R : ℕ → ℕ} {w : ℕ} (hw : w < n) (hM : M w = 0) :
    (ElimCert.elimOr (masked G M) (fun v : Fin n => R (v : ℕ))).inN ⟨w, hw⟩ = ∅ :=
  Finset.eq_empty_of_forall_notMem fun u hu => by
    have := (masked_adj.1 (ElimCert.mem_elimOr.1 hu).1).2.2
    exact this hM

/-- **What the row scan ends with**: the in-neighbours of a live vertex
in the elimination orientation are exactly the alive targets of its row
that carry a smaller rank. -/
theorem written_last (hcsr : CsrSimple G ns O T) {R : ℕ → ℕ} {w : ℕ} (hw : w < n)
    (hMw : M w ≠ 0) :
    written (n := n) O T M R w (O (w + 1))
      = (ElimCert.elimOr (masked G M) (fun v : Fin n => R (v : ℕ))).inN ⟨w, hw⟩ := by
  ext u
  rw [mem_written, ElimCert.mem_elimOr]
  constructor
  · rintro ⟨hM, hR, t, h₁, h₂, h₃⟩
    have hmb : M (T t) ≠ 0 := by rw [h₃]; exact hM
    have hadj := hcsr.csr.madj_of_slot hw h₁ h₂ hMw hmb
    rw [h₃] at hadj
    exact ⟨(madj_iff (u := u) hw).1 hadj.symm, hR⟩
  · rintro ⟨hadj, hR⟩
    have hmadj : MAdj G M w (u : ℕ) := ((madj_iff (u := u) hw).2 hadj).symm
    obtain ⟨t, h₁, h₂, h₃⟩ := hcsr.csr.slot_of_madj hmadj
    exact ⟨hmadj.alive_right, hR, t, h₁, h₂, h₃⟩

/-- The invariant of the fill, with the row in progress named: the
blocks below `w` are complete, the blocks above it are still empty, the
block of `w` holds `S`, and everything written so far names a
vertex. -/
def FillSt (n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M R ID F IT : ℕ → ℕ)
    (w : ℕ) (S : Finset (Fin n)) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
    σ.arrs "alv" = arrOf n M ∧ σ.arrs "rnk" = arrOf n R ∧
    σ.arrs "ifl" = arrOf n F ∧ σ.arrs "itg" = arrOf ns IT ∧ w ≤ n ∧
    (∀ v < n, w < v → F v = psum ID v) ∧
    (∀ v < n, v < w → F v = psum ID (v + 1)) ∧
    (w < n → F w = psum ID w + S.card) ∧
    (∀ v < n, ∀ t, psum ID v ≤ t → t < F v → IT t < n) ∧
    (∀ v : Fin n, (v : ℕ) < w → ∀ u : Fin n,
      u ∈ (ElimCert.elimOr (masked G M) (fun z : Fin n => R (z : ℕ))).inN v ↔
        ∃ t, psum ID (v : ℕ) ≤ t ∧ t < psum ID ((v : ℕ) + 1) ∧ IT t = (u : ℕ)) ∧
    (w < n → ∀ u : Fin n, u ∈ S ↔ ∃ t, psum ID w ≤ t ∧ t < F w ∧ IT t = (u : ℕ))

/-- The invariant of the fill's outer loop: the row the counter names
has nothing written in it yet. -/
def FillInv (n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M R ID : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ F IT, FillSt n ns G O T M R ID F IT (σ.vars "i") ∅ σ

/-- The invariant of the fill's row scan: the row is a live vertex's,
and what is written of it is what the pointer has passed. -/
def FillScanInv (n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M R ID : ℕ → ℕ) (w : ℕ)
    (σ : Env) : Prop :=
  (∃ F IT, FillSt n ns G O T M R ID F IT w (written (n := n) O T M R w (σ.vars "j")) σ) ∧
    σ.vars "i" = w ∧ w < n ∧ M w ≠ 0 ∧ σ.vars "jend" = O (w + 1) ∧
    O w ≤ σ.vars "j" ∧ σ.vars "j" ≤ O (w + 1)

/-- A scalar the invariant does not name leaves it alone. -/
theorem fillSt_setVar {n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M R ID F IT : ℕ → ℕ}
    {w : ℕ} {S : Finset (Fin n)} {σ : Env} (h : FillSt n ns G O T M R ID F IT w S σ)
    (x : String) (hx : x ≠ "n") (a : ℕ) :
    FillSt n ns G O T M R ID F IT w S (σ.setVar x a) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, rest⟩ := h
  exact ⟨by simp [Ne.symm hx, h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5],
    by simp [h6], by simp [h7], rest⟩

/-- **One slot of the fill.** Three paths: a dead target and one of
larger rank are passed over, and an in-neighbour is written at the fill
pointer, which then moves on. That the write stays inside the block is
`not_mem_written` — the set grows by one and is bounded by `ID w`, the
block's own length. Written in the `_run` form the kit's row scan
consumes, with every obligation of the walk pre-loaded, `degSlot_run`'s
shape and for its reason. -/
theorem fillSlot_run {B n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M R ID : ℕ → ℕ} {w : ℕ}
    (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B) (hMB : ∀ z < n, M z < B)
    (hRlt : ∀ v < n, R v < n)
    (hID : ∀ v : Fin n, ID (v : ℕ) =
      ((ElimCert.elimOr (masked G M) (fun z : Fin n => R (z : ℕ))).inN v).card)
    (hpsum : psum ID n ≤ ns) {σ : Env}
    (hI : FillScanInv n ns G O T M R ID w σ) (hjlt : σ.vars "j" < O (w + 1)) :
    ∃ σ' K, Run B fillSlot σ σ' K ∧ K ≤ 28 ∧
      FillScanInv n ns G O T M R ID w σ' ∧ σ'.vars "j" = σ.vars "j" + 1 := by
  obtain ⟨⟨F, IT, hn, hoff, htgt, halv, hrnk, hifl, hitg, hwn, hhi, hlo, hFw, hITlt, hmemv,
    hS⟩, hi, hwlt, hMw, hje, hj₁, hj₂⟩ := hI
  have hns : O (w + 1) ≤ ns := hcsr.csr.le_ns (by omega)
  have hjns : σ.vars "j" < ns := by omega
  have htn : T (σ.vars "j") < n := hcsr.csr.target_lt _ hjns
  have htv : (σ.arrs "tgt").getD (σ.vars "j") 0 = T (σ.vars "j") := by
    rw [htgt, getD_arrOf T hjns]
  have htv' : (σ.arrs "tgt")[σ.vars "j"]?.getD 0 = T (σ.vars "j") := by
    rw [← List.getD_eq_getElem?_getD]; exact htv
  have hjlen : σ.vars "j" < (σ.arrs "tgt").length := by rw [htgt, length_arrOf]; omega
  have htB : (σ.arrs "tgt").getD (σ.vars "j") 0 < B := by rw [htv]; omega
  have hIDw : ID w = ((ElimCert.elimOr (masked G M)
    (fun z : Fin n => R (z : ℕ))).inN ⟨w, hwlt⟩).card := hID ⟨w, hwlt⟩
  have hsub : written (n := n) O T M R w (σ.vars "j") ⊆
      (ElimCert.elimOr (masked G M) (fun z : Fin n => R (z : ℕ))).inN ⟨w, hwlt⟩ := by
    intro u hu
    rw [← written_last hcsr hwlt hMw]
    obtain ⟨hM', hR', t, h1, h2, h3⟩ := mem_written.1 hu
    exact mem_written.2 ⟨hM', hR', t, h1, by omega, h3⟩
  have hcard : (written (n := n) O T M R w (σ.vars "j")).card ≤ ID w := by
    rw [hIDw]; exact Finset.card_le_card hsub
  have hFle : F w ≤ psum ID (w + 1) := by rw [hFw hwlt, psum_succ]; omega
  have hFns : F w ≤ ns := le_trans hFle (le_trans (psum_mono ID (by omega)) hpsum)
  have hFwlow : psum ID w ≤ F w := by rw [hFw hwlt]; omega
  have hFhigh : ∀ v < n, F v ≤ psum ID (v + 1) := by
    intro v hv
    rcases lt_trichotomy v w with h | h | h
    · rw [hlo v hv h]
    · rw [h]; exact hFle
    · rw [hhi v hv h]; exact psum_mono ID (by omega)
  -- the write stays inside the block, which is what the store's range asks
  have hstrict : M (T (σ.vars "j")) ≠ 0 → R (T (σ.vars "j")) < R w →
      F w < psum ID (w + 1) := by
    intro hm hr
    have hmem : (⟨T (σ.vars "j"), htn⟩ : Fin n) ∈
        (ElimCert.elimOr (masked G M) (fun z : Fin n => R (z : ℕ))).inN ⟨w, hwlt⟩ := by
      rw [← written_last hcsr hwlt hMw]
      exact mem_written.2 ⟨hm, hr, σ.vars "j", hj₁, by omega, rfl⟩
    have hnot := not_mem_written (M := M) (R := R) hcsr hwlt hj₁ hjlt htn
    have hins := Finset.card_le_card (Finset.insert_subset hmem hsub)
    rw [Finset.card_insert_of_notMem hnot, ← hIDw] at hins
    rw [hFw hwlt, psum_succ]
    omega
  have hstrictns : M (T (σ.vars "j")) ≠ 0 → R (T (σ.vars "j")) < R w → F w < ns := by
    intro hm hr
    have h1 := hstrict hm hr
    have h2 := psum_mono ID (show w + 1 ≤ n by omega)
    omega
  have hF0 : (σ.arrs "ifl").getD (σ.vars "i") 0 = F w := by
    rw [hifl, hi, getD_arrOf F hwlt]
  have hF0w : (σ.arrs "ifl").getD w 0 = F w := by rw [hifl, getD_arrOf F hwlt]
  have hitglen : (σ.arrs "itg").length = ns := by rw [hitg, length_arrOf]
  have hifllen0 : σ.vars "i" < (σ.arrs "ifl").length := by
    rw [hifl, length_arrOf, hi]; exact hwlt
  -- the four reads, in the forms the walk states its obligations in
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
  have hrnkulen : ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).vars "u")
      < ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).arrs "rnk").length := by
    rw [arrs_setVar, vars_setVar, hrnk, length_arrOf]; simpa [htv'] using htn
  have hbrRu : ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).arrs "rnk").getD
      ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).vars "u") 0
      = R (T (σ.vars "j")) := by
    rw [arrs_setVar, vars_setVar]; simpa [htv', hrnk] using getD_arrOf R htn
  have hbrRuB : ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).arrs "rnk").getD
      ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).vars "u") 0 < B := by
    rw [hbrRu]; have := hRlt _ htn; omega
  have hrnkilen : ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).vars "i")
      < ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).arrs "rnk").length := by
    rw [arrs_setVar, vars_setVar, hrnk, length_arrOf]; simpa [hi] using hwlt
  have hbrRi : ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).arrs "rnk").getD
      ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).vars "i") 0 = R w := by
    rw [arrs_setVar, vars_setVar]; simpa [hi, hrnk] using getD_arrOf R hwlt
  have hbrRiB : ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).arrs "rnk").getD
      ((σ.setVar "u" ((σ.arrs "tgt").getD (σ.vars "j") 0)).vars "i") 0 < B := by
    rw [hbrRi]; have := hRlt _ hwlt; omega
  have hjB : σ.vars "j" + 1 < B := by omega
  run_vcg
  · -- the arc is written: the slot's target joins the block of the row
    have hm : M (T (σ.vars "j")) ≠ 0 := by omega
    have hr : R (T (σ.vars "j")) < R w := by omega
    have hFlt : F w < psum ID (w + 1) := hstrict hm hr
    have hnot := not_mem_written (M := M) (R := R) hcsr hwlt hj₁ hjlt htn
    have hwr : written (n := n) O T M R w (σ.vars "j" + 1)
        = insert (⟨T (σ.vars "j"), htn⟩ : Fin n) (written (n := n) O T M R w (σ.vars "j")) :=
      written_succ_of_take hj₁ htn hm hr
    refine ⟨⟨⟨upd F w (F w + 1), upd IT (F w) (T (σ.vars "j")), ?_⟩, by simp [hi], hwlt, hMw,
      by simp [hje], by simp; omega, by simp; omega⟩, by simp⟩
    simp only [vars_setVar, arrs_setVar, vars_setArr, arrs_setArr, ↓reduceIte,
      String.reduceEq, hF0w, htv, hi]
    rw [hwr]
    refine ⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv], by simp [hrnk],
      by simp [hifl, set_arrOf_eq_upd], by simp [hitg, set_arrOf_eq_upd],
      hwn, fun v hv hwv => ?_, fun v hv hvw => ?_, fun _ => ?_, fun v hv t ht1 ht2 => ?_,
      fun v hvw u => ?_, fun _ u => ?_⟩
    · rw [upd_of_ne _ (by omega : v ≠ w)]; exact hhi v hv hwv
    · rw [upd_of_ne _ (by omega : v ≠ w)]; exact hlo v hv hvw
    · rw [upd_self, Finset.card_insert_of_notMem hnot, hFw hwlt]; omega
    · by_cases hvw : v = w
      · rw [hvw] at ht1 ht2
        rw [upd_self] at ht2
        by_cases htF : t = F w
        · rw [htF, upd_self]; exact htn
        · rw [upd_of_ne _ htF]; exact hITlt w hwlt t ht1 (by omega)
      · rw [upd_of_ne _ hvw] at ht2
        have htne : t ≠ F w := by
          rcases Nat.lt_or_ge v w with h | h
          · have h1 := hFhigh v hv
            have h2 := psum_mono ID (show v + 1 ≤ w by omega)
            omega
          · have h1 := psum_mono ID (show w + 1 ≤ v by omega)
            omega
        rw [upd_of_ne _ htne]; exact hITlt v hv t ht1 ht2
    · rw [hmemv v hvw u]
      have hne : ∀ t, t < psum ID ((v : ℕ) + 1) → t ≠ F w := by
        intro t ht
        have := psum_mono ID (show (v : ℕ) + 1 ≤ w by omega)
        omega
      constructor
      · rintro ⟨t, h1, h2, h3⟩
        exact ⟨t, h1, h2, by rw [upd_of_ne _ (hne t h2)]; exact h3⟩
      · rintro ⟨t, h1, h2, h3⟩
        rw [upd_of_ne _ (hne t h2)] at h3
        exact ⟨t, h1, h2, h3⟩
    · rw [Finset.mem_insert, upd_self]
      constructor
      · rintro (rfl | hu)
        · exact ⟨F w, hFwlow, by omega, upd_self ..⟩
        · obtain ⟨t, h1, h2, h3⟩ := (hS hwlt u).1 hu
          exact ⟨t, h1, by omega, by rw [upd_of_ne _ (by omega : t ≠ F w)]; exact h3⟩
      · rintro ⟨t, h1, h2, h3⟩
        by_cases htF : t = F w
        · rw [htF, upd_self] at h3; exact Or.inl (Fin.ext h3.symm)
        · rw [upd_of_ne _ htF] at h3
          exact Or.inr ((hS hwlt u).2 ⟨t, h1, by omega, h3⟩)
  · -- alive, but not of smaller rank: nothing is written
    have hno : ¬ (M (T (σ.vars "j")) ≠ 0 ∧ R (T (σ.vars "j")) < R w) := by omega
    refine ⟨⟨⟨F, IT, ?_⟩, by simp [hi], hwlt, hMw, by simp [hje], by simp; omega,
      by simp; omega⟩, by simp⟩
    simp only [vars_setVar, ↓reduceIte, String.reduceEq]
    rw [written_succ_of_skip hno]
    exact ⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv], by simp [hrnk],
      by simp [hifl], by simp [hitg], hwn, hhi, hlo, hFw, hITlt, hmemv, hS⟩
  · -- a dead target is passed over
    have hno : ¬ (M (T (σ.vars "j")) ≠ 0 ∧ R (T (σ.vars "j")) < R w) := by omega
    refine ⟨⟨⟨F, IT, ?_⟩, by simp [hi], hwlt, hMw, by simp [hje], by simp; omega,
      by simp; omega⟩, by simp⟩
    simp only [vars_setVar, ↓reduceIte, String.reduceEq]
    rw [written_succ_of_skip hno]
    exact ⟨by simp [hn], by simp [hoff], by simp [htgt], by simp [halv], by simp [hrnk],
      by simp [hifl], by simp [hitg], hwn, hhi, hlo, hFw, hITlt, hmemv, hS⟩
  all_goals
    simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr, ↓reduceIte,
      String.reduceEq, hF0, htv, hitglen, hifllen0] at *
  all_goals omega

/-- **A row, finished.** What the scan wrote is the block, so the fill
pointer has arrived at the start of the next one and the row's clause
joins the completed ones. -/
theorem fillSt_succ {n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M R ID F IT : ℕ → ℕ} {v : ℕ}
    (hID : ∀ z : Fin n, ID (z : ℕ) =
      ((ElimCert.elimOr (masked G M) (fun y : Fin n => R (y : ℕ))).inN z).card)
    (hv : v < n) {τ : Env}
    (h : FillSt n ns G O T M R ID F IT v
      ((ElimCert.elimOr (masked G M) (fun y : Fin n => R (y : ℕ))).inN ⟨v, hv⟩) τ) :
    FillSt n ns G O T M R ID F IT (v + 1) ∅ τ := by
  obtain ⟨hn, hoff, htgt, halv, hrnk, hifl, hitg, hwn, hhi, hlo, hFw, hITlt, hmemv, hS⟩ := h
  have hFv : F v = psum ID (v + 1) := by
    rw [hFw hv, psum_succ, ← hID ⟨v, hv⟩]
  refine ⟨hn, hoff, htgt, halv, hrnk, hifl, hitg, by omega, fun z hz hvz => ?_,
    fun z hz hzv => ?_, fun hlt => ?_, hITlt, fun z hzv u => ?_, fun hlt u => ?_⟩
  · exact hhi z hz (by omega)
  · rcases Nat.lt_or_ge z v with h | h
    · exact hlo z hz h
    · rw [show z = v by omega]; exact hFv
  · rw [hhi (v + 1) hlt (by omega)]; simp
  · rcases Nat.lt_or_ge (z : ℕ) v with h | h
    · exact hmemv z h u
    · have hz2 : z = (⟨v, hv⟩ : Fin n) := Fin.ext (show (z : ℕ) = v by omega)
      subst hz2
      rw [hS hv u]
      constructor
      · rintro ⟨t, h1, h2, h3⟩; exact ⟨t, h1, by rw [hFv] at h2; exact h2, h3⟩
      · rintro ⟨t, h1, h2, h3⟩; exact ⟨t, h1, by rw [hFv]; exact h2, h3⟩
  · constructor
    · intro hu; simp at hu
    · rintro ⟨t, h1, h2, -⟩
      rw [hhi (v + 1) hlt (by omega)] at h2
      omega

/-- **One vertex's block, written out.** The row is walked by the kit's
row scan; a dead vertex has no row to walk and no arcs to write, which
`inN_of_dead` is. -/
theorem fillRow_run {B n ns : ℕ} {G : SimpleGraph (Fin n)} {O T M R ID : ℕ → ℕ} {v : ℕ}
    (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B) (hMB : ∀ z < n, M z < B)
    (hRlt : ∀ z < n, R z < n)
    (hID : ∀ z : Fin n, ID (z : ℕ) =
      ((ElimCert.elimOr (masked G M) (fun y : Fin n => R (y : ℕ))).inN z).card)
    (hpsum : psum ID n ≤ ns) (hv : v < n) {σ : Env}
    (hI : FillInv n ns G O T M R ID σ) (hiv : σ.vars "i" = v) :
    ∃ σ' K, Run B fillRow σ σ' K ∧ K ≤ 32 * Csr.rowLen O v + 21 ∧
      FillInv n ns G O T M R ID σ' ∧ σ'.vars "i" = v + 1 := by
  obtain ⟨F, IT, hst⟩ := id hI
  rw [hiv] at hst
  obtain ⟨hn, hoff, htgt, halv, hrnk, hifl, hitg, hwn, hhi, hlo, hFw, hITlt, hmemv,
    hS⟩ := id hst
  have hns : O (v + 1) ≤ ns := hcsr.csr.le_ns (by omega)
  have hov : O v ≤ O (v + 1) := hcsr.csr.mono v hv
  have hcsrRel : Csr "off" "tgt" n ns n O T σ :=
    ⟨hoff, htgt, fun i hi => hcsr.csr.mono i hi, hcsr.csr.last,
      fun p hp => hcsr.csr.target_lt p hp⟩
  have havlen : σ.vars "i" < (σ.arrs "alv").length := by
    rw [halv, length_arrOf, hiv]; exact hv
  have hav : (σ.arrs "alv").getD (σ.vars "i") 0 = M v := by
    rw [halv, hiv, getD_arrOf M hv]
  have havB : (σ.arrs "alv").getD (σ.vars "i") 0 < B := by rw [hav]; exact hMB v hv
  have hiB : σ.vars "i" + 1 < B := by rw [hiv]; omega
  have hscanSpec : Spec B
      (fun τ => FillScanInv n ns G O T M R ID v τ ∧ τ.vars "j" = O v)
      (Csr.scan "j" "jend" fillSlot)
      (fun _ τ' => (∃ F' IT', FillSt n ns G O T M R ID F' IT' (v + 1) ∅ τ') ∧
        τ'.vars "i" = v ∧ τ'.vars "i" + 1 < B)
      (32 * Csr.rowLen O v + 4) := by
    refine (Csr.rowScan_spec B (32 * Csr.rowLen O v + 4) (O (v + 1)) 28 "j" "jend" fillSlot
      (FillScanInv n ns G O T M R ID v) (by omega)
      (fun τ hτ => ⟨hτ.2.2.2.2.1, hτ.2.2.2.2.2.2⟩)
      (fun τ hτ hlt => ?_) (fun _ hτ => hτ.1)
      (fun τ hτ => by rw [hτ.2]; have : Csr.rowLen O v = O (v + 1) - O v := rfl; omega)).post
      (fun _ τ' _ hQ => ?_)
    · obtain ⟨τ', K', hr, hK', hI', hj'⟩ := fillSlot_run hcsr hB hMB hRlt hID hpsum hτ hlt
      exact ⟨τ', K', hr, hI', hj', hK'⟩
    · obtain ⟨⟨F', IT', hst'⟩, hi', -, hMv, -, -, -⟩ := hQ.1
      rw [hQ.2, written_last hcsr hv hMv] at hst'
      exact ⟨⟨F', IT', fillSt_succ hID hv hst'⟩, hi', by rw [hi']; omega⟩
  run_vcg [Csr.loadRow_spec B n ns n "off" "tgt" "i" "j" "jend" O T (by decide) (by decide),
    hscanSpec]
  · -- a live vertex: what the scan left, with the counter moved on
    obtain ⟨⟨F', IT', hst'⟩, hi', -⟩ := ‹(∃ F' IT', FillSt n ns G O T M R ID F' IT' (v+1) ∅ _)
      ∧ _›
    refine ⟨⟨F', IT', ?_⟩, by simp [hi']⟩
    simp only [vars_setVar, ↓reduceIte, hi']
    exact fillSt_setVar hst' "i" (by decide) _
  · -- a dead vertex has no row to scan
    have hMv : M v = 0 := by
      have := ‹¬ (0 < (_ : List ℕ).getD _ 0)›
      omega
    have hst2 : FillSt n ns G O T M R ID F IT v
        ((ElimCert.elimOr (masked G M) (fun y : Fin n => R (y : ℕ))).inN ⟨v, hv⟩) σ := by
      rw [inN_of_dead hv hMv]; exact hst
    refine ⟨⟨F, IT, ?_⟩, by simp [hiv]⟩
    simp only [vars_setVar, ↓reduceIte, hiv]
    exact fillSt_setVar (fillSt_succ hID hv hst2) "i" (by decide) _
  · -- the two offset reads: a row of the structure, and its number a word
    exact ⟨⟨by simpa using hcsrRel, by omega, by omega⟩, by simp [hiv]; omega,
      by simp [hiv]; omega⟩
  · -- the scan starts at the top of the row, with nothing written yet
    obtain ⟨-, hj', hje', rfl⟩ :=
      ‹Csr.LoadRowPost "off" "tgt" "i" "j" "jend" n ns n O T _ _›
    have hMv : M v ≠ 0 := by
      have := ‹0 < (_ : List ℕ).getD _ 0›
      omega
    refine ⟨⟨⟨F, IT, ?_⟩, by simp [hiv], hv, hMv, by simp [hiv], by simp [hiv], ?_⟩, ?_⟩
    · simp only [vars_setVar, ↓reduceIte, String.reduceEq, hiv]
      rw [written_start]
      exact fillSt_setVar (fillSt_setVar hst "j" (by decide) _) "jend" (by decide) _
    · simp [hiv]; omega
    · simp [hiv]

/-- **The in-neighbour lists, written out.** A second amortized walk of
the block structure — the same "so much per slot left, so much per row
left" the degree pass is paid with — and what it leaves is `InCsr` on
the nose: the blocks the offsets cut hold exactly the in-neighbours of
the elimination orientation. -/
theorem fillPass_spec (B n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M R ID : ℕ → ℕ)
    (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B) (hMB : ∀ z < n, M z < B)
    (hRlt : ∀ z < n, R z < n)
    (hID : ∀ z : Fin n, ID (z : ℕ) =
      ((ElimCert.elimOr (masked G M) (fun y : Fin n => R (y : ℕ))).inN z).card)
    (hpsum : psum ID n ≤ ns) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧
        σ.arrs "tgt" = arrOf ns T ∧ σ.arrs "alv" = arrOf n M ∧ σ.arrs "rnk" = arrOf n R ∧
        (∃ g, σ.arrs "ifl" = arrOf n g ∧ ∀ j < n, g j = psum ID j) ∧
        (∃ g, σ.arrs "itg" = arrOf ns g))
      fillPass
      (fun _ σ' => ∃ IT, σ'.arrs "itg" = arrOf ns IT ∧
        InCsr (ElimCert.elimOr (masked G M) (fun y : Fin n => R (y : ℕ))) (psum ID n)
          (psum ID) IT)
      (32 * n + 32 * ns + 10) := by
  have hOle : ∀ i ≤ n, O i ≤ ns := fun i hi => hcsr.csr.le_ns hi
  have hloop : Spec B (FillInv n ns G O T M R ID)
      (.while (.lt (.var "i") (.var "n")) fillRow)
      (fun _ σ' => FillInv n ns G O T M R ID σ' ∧
        (Cond.lt (Expr.var "i") (Expr.var "n")).evalB B σ' = some false)
      (32 * n + 32 * ns + 8) := by
    refine Spec.while_potential (FillInv n ns G O T M R ID)
      (fun σ => 32 * (ns - O (σ.vars "i")) + 32 * (n - σ.vars "i"))
      (fun σ hσ => ?_) (fun σ hσ hb => ?_) (fun _ h => h)
      (fun σ _ => by simp only [size_condLt, size_var]; omega)
    · obtain ⟨F, IT, hst⟩ := hσ
      exact evalB_condLt_vars (by have := hst.2.2.2.2.2.2.2.1; omega) (by rw [hst.1]; omega)
    · have hlt : σ.vars "i" < n := by
        obtain ⟨F, IT, hst⟩ := id hσ
        have := lt_of_condLt_true hb
        rw [hst.1] at this; exact this
      obtain ⟨σ', K, hrun, hK, hI', hi'⟩ := fillRow_run hcsr hB hMB hRlt hID hpsum hlt hσ rfl
      refine ⟨σ', K, hrun, hI', ?_⟩
      have h₁ : O (σ.vars "i") ≤ O (σ.vars "i" + 1) := hcsr.csr.mono _ hlt
      have h₂ : O (σ.vars "i" + 1) ≤ ns := hOle _ (by omega)
      have hrow : Csr.rowLen O (σ.vars "i") = O (σ.vars "i" + 1) - O (σ.vars "i") := rfl
      simp only [size_condLt, size_var, hi']
      omega
  run_vcg [hloop]
  · -- the exit: every block is complete, which is what `InCsr` says
    obtain ⟨⟨F, IT, hst⟩, hfalse⟩ := ‹FillInv n ns G O T M R ID _ ∧ _›
    obtain ⟨hn, hoff, htgt, halv, hrnk, hifl, hitg, hwn, hhi, hlo, hFw, hITlt, hmemv,
      hS⟩ := hst
    have h₁ := le_of_condLt_false hfalse
    rw [hn] at h₁
    refine ⟨IT, hitg, psum_zero ID, rfl, fun i _ => psum_mono ID (by omega),
      fun t ht => ?_, fun w u => hmemv w (by have := w.isLt; omega) u, fun w => ?_⟩
    · obtain ⟨v, hv, ha, hb⟩ := exists_block ht
      exact hITlt v hv t ha (by rw [hlo v hv (by omega)]; exact hb)
    · rw [psum_succ, hID w]; omega
  · -- the pass starts with every block empty
    obtain ⟨F, hifl, hF⟩ := ‹∃ g, σ.arrs "ifl" = arrOf n g ∧ ∀ j < n, g j = psum ID j›
    obtain ⟨IT, hitg⟩ := ‹∃ g, σ.arrs "itg" = arrOf ns g›
    refine ⟨F, IT, by simpa using ‹σ.vars "n" = n›,
      by simpa using ‹σ.arrs "off" = arrOf (n + 1) O›,
      by simpa using ‹σ.arrs "tgt" = arrOf ns T›,
      by simpa using ‹σ.arrs "alv" = arrOf n M›,
      by simpa using ‹σ.arrs "rnk" = arrOf n R›, by simpa using hifl, by simpa using hitg,
      by simp, fun v hv _ => hF v hv, fun v hv hlt => by simp at hlt,
      fun hlt => by simp; exact hF 0 (by simpa using hlt),
      fun v hv t ht1 ht2 => ?_, fun v hv u => by simp at hv, fun hlt u => ?_⟩
    · rw [hF v hv] at ht2; omega
    · simp only [vars_setVar, ↓reduceIte]
      have h0 : F 0 = psum ID 0 := hF 0 (by simpa using hlt)
      constructor
      · intro hu; simp at hu
      · rintro ⟨t, h1, h2, -⟩; rw [h0] at h2; omega

/-- **The Hoare triple for the engine**: that the five phases of the
program leave memory in the state `ElimMem` describes, within the cost
`elimCost`. It is stated over the program text and the input surface a
caller has, so a caller may thread it as a hypothesis; `implements`
below discharges it. The invariant it is proved against is `Elim`, its
three turns are `Elim.init`, `Elim.bump` and `Elim.extract`, and its
exit reading is `Elim.cert`.

It splits along the program's five phases, each a `Spec` of its own,
and what each phase does is —

* `initDeg` — `initDeg_spec`: it leaves `deg v` at the arena degree of
  `v`, at a cost of `48 n + 44 ns + 10`. Its content is
  `card_liveSlots` — the row's live slots biject with the arena
  neighbours — and `adeg_of_dead` for the other branch, and its result
  is exactly `Elim.init`'s second hypothesis. The outer loop is
  amortized against `44 (ns − off i) + 48 (n − i)`, the rows tiling the
  target array.
* `initBuck` — `initBuck_spec`: one slot per vertex, pushed into the
  bucket of its degree, at a cost of `29 n + 10`, leaving `sp = n + 1`
  and `ls = n`. Its content is `Buck.push`, and what it leaves is
  `Buck n n` — the relation the elimination loop carries.
* `elimLoop` — `elimLoop_spec`: the four counters, then
  `Spec.while_potential (ElimInv n ns G O T M) (Pot n ns)` with
  `elimTurn_run` as its step. That turn's four cases are `elimBump_run`
  (an empty bucket, by `Buck.no_deg` and `Elim.bump`), `elimStale_run`
  (a stale slot, by `Buck.pop`), and `elimTake_run` /
  `elimTakeDead_run` (an extraction, by `Buck.pop`, the row scan
  `decScan_spec`, `extract_of_scan` and `Elim.extract`). `Elim.init`
  and `initBuck_spec`'s answer are its entry reading and
  `elimExit_read` is its exit, at `cnt = n`. `Pot` never exceeds
  `160 n + 100 ns + 40`, so the phase costs `160 n + 100 ns + 52`.
* `offPass` — `offPass_spec`: a running sum, at a cost of `24 n + 12`,
  leaving `ioff j = psum ID j` for every `j ≤ n` and every fill pointer
  at the start of its own block. It establishes `InCsr`'s `zero`,
  `last`, `mono` and `len`.
* `fillPass` — `fillPass_spec`: a second amortized walk of the block
  structure whose content is a counting sort — each arc lands in the
  block of its larger-ranked endpoint — giving `InCsr`'s `mem_iff` and
  `target_lt`, at a cost of `32 n + 32 ns + 10`.

The cost is amortized, with the potential `Pot`,

    40 · (n + 1 − mind) + 40 · ls + 100 · (ns − sc) + 80 · (n − cnt),

for the loop: a pointer bump is paid out of the first term, a stale pop
out of the second, an extraction's row scan out of the third, and the
extraction itself out of the fourth, which also refunds the one the
pointer's drop costs. The pointer never runs away because `Elim.min_le`
plus an empty bucket forces it below every surviving degree, and the
arena never overflows because a slot is pushed once per vertex and once
per scanned slot — which is the clause `sp ≤ n + 1 + sc` of `ElimSt`,
with `sc ≤ ns` from `scanned_sum_le`. -/
def Implements (B n ns : ℕ) (G : SimpleGraph (Fin n)) (M O T : ℕ → ℕ) : Prop :=
  CsrSimple G ns O T → n + ns + 1 < B → (∀ z < n, M z < B) →
    Spec B (ElimPre n ns O T M) elimCom (ElimMem G M ns) (elimCost n ns)

/-! ### The five phases, sequenced

What each phase hands the next, written out once so that the five
specifications compose by the walk and nothing is re-established: every
array a phase does not write is carried across it by `Spec.frame`, and
every array it does write is named in the predicate below. -/

/-- What the degree pass leaves the bucket build: the input arrays
untouched, the arena degrees in `deg`, and the rest of the scratch at
its lengths. -/
def AfterDeg (n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
    σ.arrs "alv" = arrOf n M ∧ σ.arrs "deg" = arrOf n (adeg G M) ∧
    (∃ g, σ.arrs "elm" = arrOf n g ∧ ∀ j < n, g j = 0) ∧
    (∃ g, σ.arrs "rnk" = arrOf n g) ∧ (∃ g, σ.arrs "idg" = arrOf n g) ∧
    (∃ g, σ.arrs "bh" = arrOf (n + 1) g ∧ ∀ j ≤ n, g j = 0) ∧
    (∃ g, σ.arrs "bv" = arrOf (n + ns + 1) g) ∧ (∃ g, σ.arrs "bn" = arrOf (n + ns + 1) g) ∧
    (∃ g, σ.arrs "ioff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "ifl" = arrOf n g) ∧
    (∃ g, σ.arrs "itg" = arrOf ns g)

/-- What the bucket build leaves the elimination: `Buck` on the arena,
one slot per vertex. -/
def AfterBuck (n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M : ℕ → ℕ) (σ : Env) : Prop :=
  BuckInv n ns (adeg G M) σ ∧ σ.vars "i" = n ∧
    σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧ σ.arrs "alv" = arrOf n M ∧
    (∃ g, σ.arrs "elm" = arrOf n g ∧ ∀ j < n, g j = 0) ∧
    (∃ g, σ.arrs "rnk" = arrOf n g) ∧ (∃ g, σ.arrs "idg" = arrOf n g) ∧
    (∃ g, σ.arrs "ioff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "ifl" = arrOf n g) ∧
    (∃ g, σ.arrs "itg" = arrOf ns g)

/-- What the elimination leaves the two in-list passes: the certificate,
the recorded extraction degrees read as the in-degrees of the
orientation, and the bound that puts the whole in-list array inside the
target array. -/
def AfterLoop (n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ R ID k, σ.vars "n" = n ∧ σ.vars "kmax" = k ∧
    σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧ σ.arrs "alv" = arrOf n M ∧
    σ.arrs "rnk" = arrOf n R ∧ σ.arrs "idg" = arrOf n ID ∧ (∀ v < n, R v < n) ∧
    ElimCert (masked G M) (fun v : Fin n => R (v : ℕ)) k ∧
    (∀ w : Fin n, ID (w : ℕ) =
      ((ElimCert.elimOr (masked G M) (fun v : Fin n => R (v : ℕ))).inN w).card) ∧
    psum ID n ≤ ns ∧
    (∃ g, σ.arrs "ioff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "ifl" = arrOf n g) ∧
    (∃ g, σ.arrs "itg" = arrOf ns g)

/-- And what the offsets leave the fill: the same, with every block
opened and every fill pointer at the start of its own. -/
def AfterOff (n ns : ℕ) (G : SimpleGraph (Fin n)) (O T M : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ R ID k, σ.vars "n" = n ∧ σ.vars "kmax" = k ∧
    σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧ σ.arrs "alv" = arrOf n M ∧
    σ.arrs "rnk" = arrOf n R ∧ (∀ v < n, R v < n) ∧
    ElimCert (masked G M) (fun v : Fin n => R (v : ℕ)) k ∧
    (∀ w : Fin n, ID (w : ℕ) =
      ((ElimCert.elimOr (masked G M) (fun v : Fin n => R (v : ℕ))).inN w).card) ∧
    psum ID n ≤ ns ∧
    (∃ g, σ.arrs "ioff" = arrOf (n + 1) g ∧ ∀ j ≤ n, g j = psum ID j) ∧
    (∃ g, σ.arrs "ifl" = arrOf n g ∧ ∀ j < n, g j = psum ID j) ∧
    (∃ g, σ.arrs "itg" = arrOf ns g)

/-- **The engine implements its specification.** The five phase walks —
`initDeg_spec`, `initBuck_spec`, `elimLoop_spec`, `offPass_spec`,
`fillPass_spec` — are sequenced by the kit's walk against the four
predicates above, each phase's postcondition being the next one's
precondition on the nose and every array a phase does not write carried
across it by `Spec.frame`. The certificate the elimination left and the
block structure the fill left are `ElimMem`'s two halves, and the five
costs sum to `293 n + 176 ns + 94`, inside `elimCost`. -/
theorem implements {B : ℕ} : Implements B n ns G M O T := by
  intro hcsr hB hMB
  have hDlt : ∀ v < n, adeg G M v < n := fun v hv => by
    rw [adeg_eq hv]; exact card_nbrsIn_lt _ _
  have w1 : Spec B (ElimPre n ns O T M) initDeg (fun _ σ' => AfterDeg n ns G O T M σ')
      (48 * n + 44 * ns + 10) := by
    intro σ hσ
    obtain ⟨hn, hoff, htgt, halv, hdeg0, helm, hrnk, hidg, hbh, hbv, hbn, hioff, hifl,
      hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨hI, hi⟩, -, hfa, -, -⟩ :=
      (initDeg_spec B n ns G O T M hcsr (by omega) (by omega) hMB).frame σ
        ⟨hn, hoff, htgt, halv, hdeg0⟩
    obtain ⟨hn', hoff', htgt', halv', -, g, hdegg, hg⟩ := hI
    obtain ⟨e, he1, he2⟩ := helm
    obtain ⟨r, hr1⟩ := hrnk
    obtain ⟨d, hd1⟩ := hidg
    obtain ⟨bh, hbh1, hbh2⟩ := hbh
    obtain ⟨bv, hbv1⟩ := hbv
    obtain ⟨bn, hbn1⟩ := hbn
    obtain ⟨io, hio1⟩ := hioff
    obtain ⟨fl, hfl1⟩ := hifl
    obtain ⟨tg, htg1⟩ := hitg
    exact ⟨σ', hrun, hn', hoff', htgt', halv',
      by rw [hdegg, arrOf_congr (fun j hj => hg j (by rw [hi]; exact hj))],
      ⟨e, by rw [hfa "elm" (by decide)]; exact he1, he2⟩,
      ⟨r, by rw [hfa "rnk" (by decide)]; exact hr1⟩,
      ⟨d, by rw [hfa "idg" (by decide)]; exact hd1⟩,
      ⟨bh, by rw [hfa "bh" (by decide)]; exact hbh1, hbh2⟩,
      ⟨bv, by rw [hfa "bv" (by decide)]; exact hbv1⟩,
      ⟨bn, by rw [hfa "bn" (by decide)]; exact hbn1⟩,
      ⟨io, by rw [hfa "ioff" (by decide)]; exact hio1⟩,
      ⟨fl, by rw [hfa "ifl" (by decide)]; exact hfl1⟩,
      ⟨tg, by rw [hfa "itg" (by decide)]; exact htg1⟩⟩
  have w2 : Spec B (AfterDeg n ns G O T M) initBuck (fun _ σ' => AfterBuck n ns G O T M σ')
      (29 * n + 10) := by
    intro σ hσ
    obtain ⟨hn, hoff, htgt, halv, hdeg, helm, hrnk, hidg, hbh, hbv, hbn, hioff, hifl,
      hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨hI, hi⟩, -, hfa, -, -⟩ :=
      (initBuck_spec B n ns (adeg G M) (by omega) hDlt).frame σ ⟨hn, hdeg, hbh, hbv, hbn⟩
    obtain ⟨e, he1, he2⟩ := helm
    obtain ⟨r, hr1⟩ := hrnk
    obtain ⟨d, hd1⟩ := hidg
    obtain ⟨io, hio1⟩ := hioff
    obtain ⟨fl, hfl1⟩ := hifl
    obtain ⟨tg, htg1⟩ := hitg
    exact ⟨σ', hrun, hI, hi,
      by rw [hfa "off" (by decide)]; exact hoff,
      by rw [hfa "tgt" (by decide)]; exact htgt,
      by rw [hfa "alv" (by decide)]; exact halv,
      ⟨e, by rw [hfa "elm" (by decide)]; exact he1, he2⟩,
      ⟨r, by rw [hfa "rnk" (by decide)]; exact hr1⟩,
      ⟨d, by rw [hfa "idg" (by decide)]; exact hd1⟩,
      ⟨io, by rw [hfa "ioff" (by decide)]; exact hio1⟩,
      ⟨fl, by rw [hfa "ifl" (by decide)]; exact hfl1⟩,
      ⟨tg, by rw [hfa "itg" (by decide)]; exact htg1⟩⟩
  have w3 : Spec B (AfterBuck n ns G O T M) elimLoop (fun _ σ' => AfterLoop n ns G O T M σ')
      (160 * n + 100 * ns + 52) := by
    intro σ hσ
    obtain ⟨hbi, hi, hoff, htgt, halv, helm, hrnk, hidg, hioff, hifl, hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨R, ID, k, hn', hk', hrnk', hidg', hRlt, hcert, hIDc, hpsum⟩, -,
      hfa, -, -⟩ :=
      (elimLoop_spec B n ns G O T M (adeg G M) hcsr hB hMB (fun _ _ => rfl)).frame σ
        ⟨hbi, hi, hoff, htgt, halv, helm, hrnk, hidg⟩
    obtain ⟨io, hio1⟩ := hioff
    obtain ⟨fl, hfl1⟩ := hifl
    obtain ⟨tg, htg1⟩ := hitg
    exact ⟨σ', hrun, R, ID, k, hn', hk',
      by rw [hfa "off" (by decide)]; exact hoff,
      by rw [hfa "tgt" (by decide)]; exact htgt,
      by rw [hfa "alv" (by decide)]; exact halv,
      hrnk', hidg', hRlt, hcert, hIDc, hpsum,
      ⟨io, by rw [hfa "ioff" (by decide)]; exact hio1⟩,
      ⟨fl, by rw [hfa "ifl" (by decide)]; exact hfl1⟩,
      ⟨tg, by rw [hfa "itg" (by decide)]; exact htg1⟩⟩
  have w4 : Spec B (AfterLoop n ns G O T M) offPass (fun _ σ' => AfterOff n ns G O T M σ')
      (24 * n + 12) := by
    intro σ hσ
    obtain ⟨R, ID, k, hn, hk, hoff, htgt, halv, hrnk, hidg, hRlt, hcert, hIDc, hpsum,
      hioff, hifl, hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨hn', hs', hio', hfl'⟩, hfv, hfa, -, -⟩ :=
      (offPass_spec B n ID (by omega) (by omega)).frame σ ⟨hn, hidg, hioff, hifl⟩
    obtain ⟨tg, htg1⟩ := hitg
    exact ⟨σ', hrun, R, ID, k, hn', by rw [hfv "kmax" (by decide)]; exact hk,
      by rw [hfa "off" (by decide)]; exact hoff,
      by rw [hfa "tgt" (by decide)]; exact htgt,
      by rw [hfa "alv" (by decide)]; exact halv,
      by rw [hfa "rnk" (by decide)]; exact hrnk,
      hRlt, hcert, hIDc, hpsum, hio', hfl',
      ⟨tg, by rw [hfa "itg" (by decide)]; exact htg1⟩⟩
  have w5 : Spec B (AfterOff n ns G O T M) fillPass (ElimMem G M ns)
      (32 * n + 32 * ns + 10) := by
    intro σ hσ
    obtain ⟨R, ID, k, hn, hk, hoff, htgt, halv, hrnk, hRlt, hcert, hIDc, hpsum, hioff,
      hifl, hitg⟩ := hσ
    obtain ⟨g, hioffg, hioffv⟩ := hioff
    obtain ⟨σ', hrun, ⟨IT, hitg', harcs⟩, hfv, hfa, -, -⟩ :=
      (fillPass_spec B n ns G O T M R ID hcsr hB hMB hRlt hIDc hpsum).frame σ
        ⟨hn, hoff, htgt, halv, hrnk, hifl, hitg⟩
    exact ⟨σ', hrun, R, psum ID, IT, k, psum ID n,
      by rw [hfa "rnk" (by decide)]; exact hrnk,
      by rw [hfv "kmax" (by decide)]; exact hk,
      by rw [hfa "ioff" (by decide), hioffg]
         exact arrOf_congr (fun j hj => hioffv j (by omega)),
      hitg', by omega, ⟨hcert, harcs⟩⟩
  show Spec B (ElimPre n ns O T M) elimCom (ElimMem G M ns) (600 * n + 600 * ns + 100)
  run_vcg [w1, w2, w3, w4, w5] <;> assumption

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
