import Lax3Proofs.CoverConstruction
import Lax12.ShallowMinorDensity
import Lax12Proofs.NowhereDenseWcol

/-!
Transitive–fraternal augmentations and their in-degree bound on nowhere
dense classes.

# The process

An *orientation* of a graph on `Fin n` is recorded by its in-neighbour
finsets `inN : Fin n → Finset (Fin n)`, with no loops and no two-cycles;
`Orients D G` says that the arcs of `D` are exactly the edges of `G`,
each taken in one direction.  One round of the *tight transitive
fraternal augmentation* turns an orientation `D` into an orientation `D'`
that

* keeps every arc of `D`;
* for every transitive link `u → w → v` puts an arc between `u` and `v`;
* for every fraternal link `u → w ← v` puts an arc between `u` and `v`;
* has no other arcs.

The direction of the new arcs is *not* determined: transitive arcs point
forward unless the pair is transitively linked both ways, and fraternal
edges are oriented by whatever rule the consumer likes — the algorithm of
Grohe–Kreutzer–Siebertz orients them by a greedy degeneracy ordering of
the fraternity graph.  Accordingly `AugStep` is a relation, and a run of
the process is a family `D : ℕ → Orientation n` with `IsAugChain G D r`.

# The theorem

`exists_augChain_inDeg_subpolynomial`: for every nowhere dense class `C`,
every number of rounds `r` and every `δ > 0` there is a `c` such that
every subgraph `G` of a member, on `m` vertices, carries an `r`-round
augmentation chain all of whose in-degrees are at most `c · m ^ δ`.

# The proof

Fix an ordering `π` of the vertices attaining `wcol G (2 ^ r)`.  The
*canonical chain* starts from the orientation of `G` by `π` and, at each
round, adds every demanded pair oriented from the `π`-smaller to the
`π`-larger endpoint.  The invariant carried along the chain is that every
arc `u → v` of the `i`-th orientation has `u` weakly `2 ^ i`-reachable
from `v` under `π`: transitive and fraternal links concatenate two walks
of length at most `2 ^ i`, and the weak-reachability side condition
survives the concatenation because the meeting vertex `w` is
`π`-above both ends of a fraternal link and `π`-between the ends of a
transitive one.  In-degrees are then bounded by the size of a weak
reachability set, i.e. by `wcol G (2 ^ r)`, which is subpolynomial on a
nowhere dense class by Lax12.

The same invariant bounds the back-degree of the *fraternity graph* of
each round under `π`, which is the "moreover" the greedy algorithm needs:
`canonChain_fratGraph_backDegree`.  Together with the unconditional
per-round recursion `inDegLE_of_augStep` — old arcs, at most `d²`
transitive arcs and the chosen fraternal arcs — that is the whole budget
of a round.

# Independent of the ordering: fraternity densification

`fratGraph_lowDegreeVertex` is the load-bearing sparse-combinatorics
lemma of the Nešetřil–Ossona de Mendez argument, proved here
unconditionally: if an orientation of `H` has in-degree at most `d` and
every depth-1 minor of `H` on `m` vertices has at most `D₁ · m` edges,
then every nonempty set of vertices carries a vertex of fraternity degree
at most `d * d + d * D₁` inside it.  The proof is the private-witness
extraction: each fraternal pair inside `S` gets a witness `w`; the
witnesses lying inside `S` account for at most `d²` ordered pairs each,
and each witness `w` outside `S` is contracted into the one in-neighbour
of `w` that lies on the most pairs of `w`, which by averaging realizes at
least a `1/d` fraction of the pairs of `w` as edges of a depth-1 minor of
`H` on the vertex set `S`.  With `degeneracyLE_of_lowDegreeVertices` —
greedy elimination — that turns into an ordering, hence into an
orientation of the fraternity graph, which is what a greedy round needs.

# What the P6 program consumes

The program exhibits its own chain — its greedy degeneracy orientation of
`G` and, per round, its greedy orientation of the fraternity graph — and
instantiates

* `walk_of_arc`, the path invariant: every arc of round `i` is realized
  by a `G`-walk of length at most `2 ^ i`, the radius bookkeeping of the
  cover phase;
* `inDegLE_of_augStep`, the per-round budget `d + d² + k`;
* `exists_greedy_round` / `greedy_chain_inDegLE`, the greedy recursion.

The in-degree bound for the *computed* chain needs one input this file
does not prove: `AugmentedDepthOneDensity`, that the augmented graphs of
the rounds again have small depth-1 minor density.  It is carried as a
hypothesis of `greedy_chain_inDegLE`; every other statement here is
unconditional, and the existence theorem
`exists_augChain_subpolynomial` — the theorem the campaign's design
record names as the target — does not need it at all.
-/

namespace Lax3Proofs.Augmentation

open scoped SimpleGraph
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ColoringNumbers
open Lax3Proofs.CoverConstruction

variable {n : ℕ}

/-! ### Orientations -/

/-- An orientation of a graph on `Fin n`, recorded by in-neighbour
finsets: no vertex is its own in-neighbour and no pair is oriented both
ways. -/
structure Orientation (n : ℕ) where
  /-- The in-neighbours of a vertex. -/
  inN : Fin n → Finset (Fin n)
  /-- No loops. -/
  not_mem_self : ∀ v, v ∉ inN v
  /-- No two-cycles. -/
  asymm : ∀ u v, u ∈ inN v → v ∉ inN u

namespace Orientation

/-- The pair `u`, `v` carries an arc of `D`, in one direction or the
other. -/
def Adjacent (D : Orientation n) (u v : Fin n) : Prop :=
  u ∈ D.inN v ∨ v ∈ D.inN u

theorem adjacent_comm {D : Orientation n} {u v : Fin n} (h : D.Adjacent u v) :
    D.Adjacent v u := Or.symm h

theorem adjacent_of_mem_inN {D : Orientation n} {u v : Fin n} (h : u ∈ D.inN v) :
    D.Adjacent u v := Or.inl h

theorem ne_of_mem_inN {D : Orientation n} {u v : Fin n} (h : u ∈ D.inN v) : u ≠ v := by
  rintro rfl; exact D.not_mem_self _ h

/-- The underlying undirected graph of an orientation. -/
def toGraph (D : Orientation n) : SimpleGraph (Fin n) where
  Adj := D.Adjacent
  symm _ _ h := Or.symm h
  loopless := ⟨fun v h => by rcases h with h | h <;> exact D.not_mem_self v h⟩

theorem toGraph_adj {D : Orientation n} {u v : Fin n} :
    D.toGraph.Adj u v ↔ D.Adjacent u v := Iff.rfl

/-- `D` is an orientation of `G`: every arc of `D` is an edge of `G` and
every edge of `G` carries an arc of `D`. -/
def Orients (D : Orientation n) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v, G.Adj u v ↔ D.Adjacent u v

theorem Orients.adj_of_mem_inN {D : Orientation n} {G : SimpleGraph (Fin n)}
    (h : D.Orients G) {u v : Fin n} (huv : u ∈ D.inN v) : G.Adj u v :=
  (h u v).2 (adjacent_of_mem_inN huv)

theorem orients_toGraph (D : Orientation n) : D.Orients D.toGraph :=
  fun _ _ => Iff.rfl

/-- Every in-degree of `D` is at most `d`. -/
def InDegLE (D : Orientation n) (d : ℕ) : Prop := ∀ v, (D.inN v).card ≤ d

end Orientation

open Orientation

/-! ### Transitive and fraternal links -/

/-- `u` reaches `v` transitively in one step: `u → w → v` for some `w`. -/
def TransLink (D : Orientation n) (u v : Fin n) : Prop :=
  ∃ w, u ∈ D.inN w ∧ w ∈ D.inN v

/-- `u` and `v` are fraternal: `u → w ← v` for some `w`. -/
def FratLink (D : Orientation n) (u v : Fin n) : Prop :=
  ∃ w, u ∈ D.inN w ∧ v ∈ D.inN w

theorem FratLink.symm {D : Orientation n} {u v : Fin n} (h : FratLink D u v) :
    FratLink D v u := by
  obtain ⟨w, hu, hv⟩ := h; exact ⟨w, hv, hu⟩

/-- The fraternity graph of an orientation: distinct vertices with a
common out-neighbour. -/
def fratGraph (D : Orientation n) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ FratLink D u v
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem fratGraph_adj {D : Orientation n} {u v : Fin n} :
    (fratGraph D).Adj u v ↔ u ≠ v ∧ FratLink D u v := Iff.rfl

/-! ### One round of the process -/

/-- One round of the tight transitive–fraternal augmentation: `D'` keeps
the arcs of `D`, puts an arc on every transitively and every fraternally
linked pair, and has no other arcs. -/
structure AugStep (D D' : Orientation n) : Prop where
  /-- Old arcs survive. -/
  mono : ∀ u v, u ∈ D.inN v → u ∈ D'.inN v
  /-- Transitive links are covered. -/
  trans_cov : ∀ u v, u ≠ v → TransLink D u v → D'.Adjacent u v
  /-- Fraternal links are covered. -/
  frat_cov : ∀ u v, u ≠ v → FratLink D u v → D'.Adjacent u v
  /-- Tightness: nothing else is added. -/
  tight : ∀ u v, u ∈ D'.inN v → u ∈ D.inN v ∨ TransLink D u v ∨ FratLink D u v

/-- An `r`-round run of the process on `G`: `D 0` orients `G` and each of
the first `r` rounds is an augmentation step. -/
def IsAugChain (G : SimpleGraph (Fin n)) (D : ℕ → Orientation n) (r : ℕ) : Prop :=
  (D 0).Orients G ∧ ∀ i < r, AugStep (D i) (D (i + 1))

/-! ### The path invariant -/

/-- Every arc of `D` is realized by a `G`-walk of length at most `L`. -/
def Realizes (G : SimpleGraph (Fin n)) (L : ℕ) (D : Orientation n) : Prop :=
  ∀ u v, u ∈ D.inN v → ∃ p : G.Walk u v, p.length ≤ L

theorem realizes_of_orients {G : SimpleGraph (Fin n)} {D : Orientation n}
    (h : D.Orients G) : Realizes G 1 D := by
  intro u v huv
  exact ⟨(h.adj_of_mem_inN huv).toWalk, by simp⟩

theorem realizes_mono {G : SimpleGraph (Fin n)} {D : Orientation n} {L L' : ℕ}
    (h : Realizes G L D) (hL : L ≤ L') : Realizes G L' D := by
  intro u v huv
  obtain ⟨p, hp⟩ := h u v huv
  exact ⟨p, hp.trans hL⟩

/-- An augmentation step at most doubles the realizing length: a
transitive or fraternal link concatenates two realized walks. -/
theorem realizes_of_augStep {G : SimpleGraph (Fin n)} {D D' : Orientation n} {L : ℕ}
    (hstep : AugStep D D') (h : Realizes G L D) : Realizes G (2 * L) D' := by
  intro u v huv
  rcases hstep.tight u v huv with hold | ⟨w, huw, hwv⟩ | ⟨w, huw, hvw⟩
  · obtain ⟨p, hp⟩ := h u v hold
    exact ⟨p, by omega⟩
  · obtain ⟨p, hp⟩ := h u w huw
    obtain ⟨q, hq⟩ := h w v hwv
    exact ⟨p.append q, by rw [SimpleGraph.Walk.length_append]; omega⟩
  · obtain ⟨p, hp⟩ := h u w huw
    obtain ⟨q, hq⟩ := h v w hvw
    refine ⟨p.append q.reverse, ?_⟩
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    omega

/-- **Path invariant.**  Along an augmentation chain on `G`, every arc of
the `i`-th orientation is realized by a `G`-walk of length at most
`2 ^ i`. -/
theorem realizes_chain {G : SimpleGraph (Fin n)} {D : ℕ → Orientation n} {r : ℕ}
    (hchain : IsAugChain G D r) : ∀ i ≤ r, Realizes G (2 ^ i) (D i) := by
  intro i
  induction i with
  | zero => intro _; simpa using realizes_of_orients hchain.1
  | succ i ih =>
      intro hi
      have hstep := hchain.2 i (by omega)
      have := realizes_of_augStep hstep (ih (by omega))
      intro u v huv
      obtain ⟨p, hp⟩ := this u v huv
      exact ⟨p, by rw [pow_succ]; omega⟩

/-- The path invariant, applied to a single arc. -/
theorem walk_of_arc {G : SimpleGraph (Fin n)} {D : ℕ → Orientation n} {r : ℕ}
    (hchain : IsAugChain G D r) {i : ℕ} (hi : i ≤ r) {u v : Fin n}
    (h : u ∈ (D i).inN v) : ∃ p : G.Walk u v, p.length ≤ 2 ^ i :=
  realizes_chain hchain i hi u v h

/-- The path invariant read on the underlying graph: every edge of the
`i`-th augmented graph is realized by a `G`-walk of length at most
`2 ^ i`. -/
theorem walk_of_edge {G : SimpleGraph (Fin n)} {D : ℕ → Orientation n} {r : ℕ}
    (hchain : IsAugChain G D r) {i : ℕ} (hi : i ≤ r) {u v : Fin n}
    (h : (D i).toGraph.Adj u v) : ∃ p : G.Walk u v, p.length ≤ 2 ^ i := by
  rcases h with h | h
  · exact walk_of_arc hchain hi h
  · obtain ⟨p, hp⟩ := walk_of_arc hchain hi h
    exact ⟨p.reverse, by simpa using hp⟩

/-! ### Degeneracy

Mathlib has no degeneracy notion for simple graphs, so the two readings
needed here are spelled out locally.  `BackDegLE` is what an orientation
consumes — orient every edge towards its `π`-larger endpoint and the
in-degrees are the back-degrees — and `LowDegreeVertices` is what greedy
elimination consumes and what a density bound produces. -/

/-- `Finset.univ` filtered by an arbitrary predicate on `Fin n`. -/
noncomputable def pick (p : Fin n → Prop) : Finset (Fin n) :=
  @Finset.filter _ p (Classical.decPred p) Finset.univ

theorem mem_pick {p : Fin n → Prop} {u : Fin n} : u ∈ pick p ↔ p u := by
  rw [pick, @Finset.mem_filter _ _ (Classical.decPred p)]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The neighbours of `v` inside `S`. -/
noncomputable def nbrsIn (F : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) :
    Finset (Fin n) := S ∩ pick (fun u => F.Adj u v)

theorem mem_nbrsIn {F : SimpleGraph (Fin n)} {S : Finset (Fin n)} {u v : Fin n} :
    u ∈ nbrsIn F S v ↔ u ∈ S ∧ F.Adj u v := by
  rw [nbrsIn, Finset.mem_inter]
  exact and_congr Iff.rfl mem_pick

/-- Under the vertex ranking `σ`, every vertex of `F` has at most `k`
neighbours of smaller rank. -/
def BackDegLE (F : SimpleGraph (Fin n)) (σ : Fin n → ℕ) (k : ℕ) : Prop :=
  ∀ v, {u | F.Adj u v ∧ σ u < σ v}.ncard ≤ k

/-- `F` is `k`-degenerate: some injective vertex ranking has all
back-degrees at most `k`.  This is what an orientation consumes — orient
every edge towards its larger end. -/
def DegeneracyLE (F : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ σ : Fin n → ℕ, Function.Injective σ ∧ BackDegLE F σ k

/-- Every nonempty set of vertices contains a vertex with at most `k`
neighbours inside it: the elimination form of `k`-degeneracy, which is
what greedy elimination produces and what the density bound proves. -/
def LowDegreeVertices (F : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → ∃ v ∈ S, (nbrsIn F S v).card ≤ k

/-- A `k`-degenerate graph has a vertex of degree at most `k` in every
nonempty vertex set: take the highest-ranked vertex of the set. -/
theorem lowDegreeVertices_of_degeneracyLE {F : SimpleGraph (Fin n)} {k : ℕ}
    (h : DegeneracyLE F k) : LowDegreeVertices F k := by
  classical
  obtain ⟨σ, hinj, hσ⟩ := h
  intro S hS
  obtain ⟨v, hvS, hvmax⟩ := Finset.exists_max_image S σ hS
  refine ⟨v, hvS, ?_⟩
  rw [← Set.ncard_coe_finset]
  refine le_trans (Set.ncard_le_ncard (fun u hu => ?_) (Set.toFinite _)) (hσ v)
  obtain ⟨huS, huv⟩ := mem_nbrsIn.1 hu
  exact ⟨huv, lt_of_le_of_ne (hvmax u huS) fun hc => F.ne_of_adj huv (hinj hc)⟩

/-- **Greedy elimination.**  A graph in which every nonempty vertex set
carries a vertex of small degree inside it is degenerate: peel off such a
vertex, rank it last, and recurse.  This is the step that turns the
density bound of `fratGraph_lowDegreeVertex` into an orientation. -/
theorem degeneracyLE_of_lowDegreeVertices {F : SimpleGraph (Fin n)} {k : ℕ}
    (h : LowDegreeVertices F k) : DegeneracyLE F k := by
  classical
  have key : ∀ (m : ℕ) (S : Finset (Fin n)), S.card ≤ m → ∃ σ : Fin n → ℕ,
      Set.InjOn σ ↑S ∧ (∀ v ∈ S, σ v < S.card) ∧
      ∀ v ∈ S, ((nbrsIn F S v).filter (fun u => σ u < σ v)).card ≤ k := by
    intro m
    induction m with
    | zero =>
        intro S hS
        have : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hS)
        subst this
        exact ⟨fun _ => 0, by simp, by simp, by simp⟩
    | succ m ih =>
        intro S hScard
        rcases S.eq_empty_or_nonempty with rfl | hS
        · exact ⟨fun _ => 0, by simp, by simp, by simp⟩
        obtain ⟨v₀, hv₀S, hv₀deg⟩ := h S hS
        have hcard : (S.erase v₀).card = S.card - 1 := Finset.card_erase_of_mem hv₀S
        have hcpos : 0 < S.card := Finset.card_pos.2 hS
        obtain ⟨σ', hinj', hlt', hdeg'⟩ := ih (S.erase v₀) (by omega)
        refine ⟨fun x => if x = v₀ then S.card - 1 else σ' x, ?_, ?_, ?_⟩
        · intro x hx y hy hxy
          dsimp only at hxy
          by_cases hx0 : x = v₀ <;> by_cases hy0 : y = v₀
          · rw [hx0, hy0]
          · exfalso
            have := hlt' y (Finset.mem_erase.2 ⟨hy0, hy⟩)
            rw [if_pos hx0, if_neg hy0] at hxy
            omega
          · exfalso
            have := hlt' x (Finset.mem_erase.2 ⟨hx0, hx⟩)
            rw [if_neg hx0, if_pos hy0] at hxy
            omega
          · rw [if_neg hx0, if_neg hy0] at hxy
            exact hinj' (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hx0, hx⟩))
              (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hy0, hy⟩)) hxy
        · intro v hv
          dsimp only
          by_cases hv0 : v = v₀
          · rw [if_pos hv0]; omega
          · have := hlt' v (Finset.mem_erase.2 ⟨hv0, hv⟩)
            rw [if_neg hv0]
            omega
        · intro v hv
          by_cases hv0 : v = v₀
          · subst hv0
            refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hv₀deg
          · have hvS' : v ∈ S.erase v₀ := Finset.mem_erase.2 ⟨hv0, hv⟩
            have hvlt := hlt' v hvS'
            refine le_trans (Finset.card_le_card ?_) (hdeg' v hvS')
            intro u hu
            obtain ⟨huN, hulr⟩ := Finset.mem_filter.1 hu
            obtain ⟨huS, huadj⟩ := mem_nbrsIn.1 huN
            dsimp only at hulr
            rw [if_neg hv0] at hulr
            have hu0 : u ≠ v₀ := by
              intro hc
              rw [if_pos hc] at hulr
              omega
            rw [if_neg hu0] at hulr
            exact Finset.mem_filter.2
              ⟨mem_nbrsIn.2 ⟨Finset.mem_erase.2 ⟨hu0, huS⟩, huadj⟩, hulr⟩
  obtain ⟨σ, hinj, -, hdeg⟩ := key n Finset.univ (by simp)
  refine ⟨σ, fun x y hxy => hinj (by simp) (by simp) hxy, fun v => ?_⟩
  refine le_trans (le_of_eq ?_) (hdeg v (Finset.mem_univ v))
  rw [← Set.ncard_coe_finset]
  congr 1
  ext u
  simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_nbrsIn, Finset.mem_univ, true_and]

/-! ### The in-degree budget of one round -/

/-- The vertices transitively linked to `v`: the in-neighbours of the
in-neighbours of `v`. -/
def transIn (D : Orientation n) (v : Fin n) : Finset (Fin n) :=
  (D.inN v).biUnion (fun w => D.inN w)

theorem mem_transIn {D : Orientation n} {u v : Fin n} :
    u ∈ transIn D v ↔ TransLink D u v := by
  simp only [transIn, Finset.mem_biUnion, TransLink]
  exact ⟨fun ⟨w, hw, hu⟩ => ⟨w, hu, hw⟩, fun ⟨w, hu, hw⟩ => ⟨w, hw, hu⟩⟩

/-- A vertex has at most `d²` transitive in-links when in-degrees are at
most `d`. -/
theorem card_transIn_le {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) (v : Fin n) :
    (transIn D v).card ≤ d * d := by
  refine le_trans (Finset.card_biUnion_le) ?_
  calc ∑ w ∈ D.inN v, (D.inN w).card ≤ ∑ _w ∈ D.inN v, d :=
        Finset.sum_le_sum fun w _ => hd w
    _ = (D.inN v).card * d := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ d * d := Nat.mul_le_mul_right d (hd v)

/-- **The budget of one round.**  After an augmentation step the
in-degree of a vertex is at most the old in-degree, plus the `d²`
transitive links, plus the fraternal arcs the round chose to point at it.
This is the recursion the greedy algorithm runs on; it holds for every
augmentation step, with no hypothesis on the graph. -/
theorem inDegLE_of_augStep {D D' : Orientation n} {d k : ℕ} (h : AugStep D D')
    (hd : D.InDegLE d)
    (hk : ∀ v, {u | u ∈ D'.inN v ∧ (fratGraph D).Adj u v}.ncard ≤ k) :
    D'.InDegLE (d + d * d + k) := by
  classical
  intro v
  have hsub : (↑(D'.inN v) : Set (Fin n)) ⊆
      (↑(D.inN v) : Set (Fin n)) ∪ (↑(transIn D v) : Set (Fin n)) ∪
        {u | u ∈ D'.inN v ∧ (fratGraph D).Adj u v} := by
    intro u hu
    have hu' : u ∈ D'.inN v := hu
    rcases h.tight u v hu' with h1 | h2 | h3
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (mem_transIn.2 h2))
    · exact Or.inr ⟨hu', ne_of_mem_inN hu', h3⟩
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at hcard
  refine hcard.trans (le_trans (Set.ncard_union_le _ _) ?_)
  refine Nat.add_le_add (le_trans (Set.ncard_union_le _ _) ?_) (hk v)
  rw [Set.ncard_coe_finset, Set.ncard_coe_finset]
  exact Nat.add_le_add (hd v) (card_transIn_le hd v)

/-- If the round orients the fraternity graph consistently with a ranking
`σ` whose back-degrees are at most `k`, the fraternal contribution to
every in-degree is at most `k`.  This is the clause of
`inDegLE_of_augStep` that a greedy round discharges. -/
theorem fratIn_le_of_backDegLE {D D' : Orientation n} {σ : Fin n → ℕ} {k : ℕ}
    (hσ : BackDegLE (fratGraph D) σ k)
    (hor : ∀ u v, u ∈ D'.inN v → (fratGraph D).Adj u v → σ u < σ v) (v : Fin n) :
    {u | u ∈ D'.inN v ∧ (fratGraph D).Adj u v}.ncard ≤ k := by
  refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (hσ v)
  rintro u ⟨hu, hadj⟩
  exact ⟨hadj, hor u v hu hadj⟩

/-! ### Weak reachability along a chain

The invariant of the canonical chain: every arc of the `i`-th orientation
points from a vertex weakly `2 ^ i`-reachable from its head.  Both
augmentation moves concatenate two such walks, and the `π`-minimality
side condition survives because the meeting vertex is `π`-above the tail
in both cases. -/

/-- Every arc of `D` points from a vertex weakly `s`-reachable from its
head. -/
def WreachBound (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (s : ℕ)
    (D : Orientation n) : Prop :=
  ∀ u v, u ∈ D.inN v → u ∈ wreach G π s v

/-- Weak reachability grows with the radius. -/
theorem wreach_mono {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {s s' : ℕ}
    (hs : s ≤ s') {u v : Fin n} (h : u ∈ wreach G π s v) : u ∈ wreach G π s' v := by
  obtain ⟨p, hp, hmin⟩ := mem_wreach_iff.1 h
  exact mem_wreach_iff.2 ⟨p, hp.trans hs, hmin⟩

/-- A weakly reachable vertex other than the source comes earlier in the
ordering. -/
theorem lt_of_mem_wreach {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {s : ℕ}
    {u v : Fin n} (h : u ∈ wreach G π s v) (hne : u ≠ v) : π u < π v := by
  obtain ⟨p, -, hmin⟩ := mem_wreach_iff.1 h
  exact lt_of_le_of_ne (hmin v p.start_mem_support) fun hc => hne (π.injective hc)

/-- A transitive link of a `wreach`-bounded orientation is weakly
reachable at twice the radius: append the two walks; the meeting vertex
`w` is `π`-above `u`, so the `π`-minimality of `u` survives. -/
theorem wreach_of_transLink {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {s : ℕ}
    {D : Orientation n} (hD : WreachBound G π s D) {u v : Fin n}
    (h : TransLink D u v) : u ∈ wreach G π (2 * s) v := by
  obtain ⟨w, huw, hwv⟩ := h
  obtain ⟨a, ha, hamin⟩ := mem_wreach_iff.1 (hD u w huw)
  obtain ⟨b, hb, hbmin⟩ := mem_wreach_iff.1 (hD w v hwv)
  refine mem_wreach_iff.2 ⟨b.append a, ?_, fun y hy => ?_⟩
  · rw [SimpleGraph.Walk.length_append]; omega
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hy with hy | hy
    · exact le_trans (hamin w a.start_mem_support) (hbmin y hy)
    · exact hamin y hy

/-- A fraternal link of a `wreach`-bounded orientation, taken from its
`π`-smaller end, is weakly reachable at twice the radius. -/
theorem wreach_of_fratLink {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {s : ℕ}
    {D : Orientation n} (hD : WreachBound G π s D) {u v : Fin n}
    (h : FratLink D u v) (hlt : π u ≤ π v) : u ∈ wreach G π (2 * s) v := by
  obtain ⟨w, huw, hvw⟩ := h
  obtain ⟨a, ha, hamin⟩ := mem_wreach_iff.1 (hD u w huw)
  obtain ⟨b, hb, hbmin⟩ := mem_wreach_iff.1 (hD v w hvw)
  refine mem_wreach_iff.2 ⟨b.reverse.append a, ?_, fun y hy => ?_⟩
  · rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hy with hy | hy
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hy
      exact le_trans hlt (hbmin y hy)
    · exact hamin y hy

/-! ### The canonical chain

Fix an ordering `π`.  The canonical chain orients `G` by `π` and, at each
round, orients every newly demanded pair from its `π`-smaller to its
`π`-larger end.  That is a legal augmentation step exactly because the
arcs stay `π`-increasing: a transitive link `u → w → v` then has
`π u < π w < π v`, so the forward direction is the `π`-direction. -/

/-- The orientation of `G` by an ordering: every edge points from its
`π`-smaller to its `π`-larger end. -/
noncomputable def baseOr (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) :
    Orientation n where
  inN v := pick (fun u => G.Adj u v ∧ π u < π v)
  not_mem_self _ h := absurd (mem_pick.1 h).2 (lt_irrefl _)
  asymm _ _ h h' := absurd ((mem_pick.1 h).2.trans (mem_pick.1 h').2) (lt_irrefl _)

theorem mem_baseOr {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {u v : Fin n} :
    u ∈ (baseOr G π).inN v ↔ G.Adj u v ∧ π u < π v := mem_pick

theorem baseOr_orients (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) :
    (baseOr G π).Orients G := by
  intro u v
  constructor
  · intro h
    rcases lt_or_gt_of_ne (fun hc : π u = π v => G.ne_of_adj h (π.injective hc)) with hlt | hlt
    · exact Or.inl (mem_baseOr.2 ⟨h, hlt⟩)
    · exact Or.inr (mem_baseOr.2 ⟨h.symm, hlt⟩)
  · rintro (h | h)
    · exact (mem_baseOr.1 h).1
    · exact ((mem_baseOr.1 h).1).symm

theorem baseOr_wreach (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) :
    WreachBound G π 1 (baseOr G π) := by
  intro u v h
  obtain ⟨hadj, hlt⟩ := mem_baseOr.1 h
  refine mem_wreach_iff.2 ⟨hadj.symm.toWalk, by simp, fun y hy => ?_⟩
  have : y = v ∨ y = u := by simpa using hy
  rcases this with rfl | rfl
  · exact hlt.le
  · exact le_rfl

/-- One round of the canonical chain: keep the old arcs and orient every
newly demanded pair by `π`. -/
noncomputable def tightStep (π : Equiv.Perm (Fin n)) (D : Orientation n) :
    Orientation n where
  inN v := D.inN v ∪
    pick (fun u => ¬ D.Adjacent u v ∧ (TransLink D u v ∨ FratLink D u v) ∧ π u < π v)
  not_mem_self v h := by
    rcases Finset.mem_union.1 h with h | h
    · exact D.not_mem_self v h
    · exact absurd (mem_pick.1 h).2.2 (lt_irrefl _)
  asymm u v h h' := by
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_union.1 h' with h' | h'
      · exact D.asymm u v h h'
      · exact (mem_pick.1 h').1 (Or.inr h)
    · rcases Finset.mem_union.1 h' with h' | h'
      · exact (mem_pick.1 h).1 (Or.inr h')
      · exact absurd ((mem_pick.1 h).2.2.trans (mem_pick.1 h').2.2) (lt_irrefl _)

theorem mem_tightStep {π : Equiv.Perm (Fin n)} {D : Orientation n} {u v : Fin n} :
    u ∈ (tightStep π D).inN v ↔
      u ∈ D.inN v ∨
        (¬ D.Adjacent u v ∧ (TransLink D u v ∨ FratLink D u v) ∧ π u < π v) := by
  rw [show (tightStep π D).inN v = D.inN v ∪
      pick (fun u => ¬ D.Adjacent u v ∧ (TransLink D u v ∨ FratLink D u v) ∧ π u < π v) from rfl,
    Finset.mem_union]
  exact or_congr Iff.rfl mem_pick

/-- The canonical chain keeps its arcs `π`-increasing. -/
def PiIncreasing (π : Equiv.Perm (Fin n)) (D : Orientation n) : Prop :=
  ∀ u v, u ∈ D.inN v → π u < π v

theorem piIncreasing_baseOr (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) :
    PiIncreasing π (baseOr G π) := fun _ _ h => (mem_baseOr.1 h).2

theorem piIncreasing_tightStep {π : Equiv.Perm (Fin n)} {D : Orientation n}
    (h : PiIncreasing π D) : PiIncreasing π (tightStep π D) := by
  intro u v hu
  rcases mem_tightStep.1 hu with hu | hu
  · exact h u v hu
  · exact hu.2.2

/-- On a `π`-increasing orientation a transitive link is `π`-increasing:
`π u < π w < π v`. -/
theorem lt_of_transLink {π : Equiv.Perm (Fin n)} {D : Orientation n}
    (h : PiIncreasing π D) {u v : Fin n} (huv : TransLink D u v) : π u < π v := by
  obtain ⟨w, huw, hwv⟩ := huv
  exact (h u w huw).trans (h w v hwv)

/-- A round of the canonical chain is an augmentation step. -/
theorem augStep_tightStep {π : Equiv.Perm (Fin n)} {D : Orientation n}
    (h : PiIncreasing π D) : AugStep D (tightStep π D) where
  mono _ _ hu := mem_tightStep.2 (Or.inl hu)
  trans_cov u v _ hlink := by
    by_cases hadj : D.Adjacent u v
    · rcases hadj with hadj | hadj
      · exact Or.inl (mem_tightStep.2 (Or.inl hadj))
      · exact Or.inr (mem_tightStep.2 (Or.inl hadj))
    · exact Or.inl (mem_tightStep.2 (Or.inr ⟨hadj, Or.inl hlink, lt_of_transLink h hlink⟩))
  frat_cov u v hne hlink := by
    by_cases hadj : D.Adjacent u v
    · rcases hadj with hadj | hadj
      · exact Or.inl (mem_tightStep.2 (Or.inl hadj))
      · exact Or.inr (mem_tightStep.2 (Or.inl hadj))
    · rcases lt_or_gt_of_ne (fun hc : π u = π v => hne (π.injective hc)) with hlt | hlt
      · exact Or.inl (mem_tightStep.2 (Or.inr ⟨hadj, Or.inr hlink, hlt⟩))
      · exact Or.inr
          (mem_tightStep.2 (Or.inr ⟨fun hc => hadj (adjacent_comm hc), Or.inr hlink.symm, hlt⟩))
  tight u v hu := by
    rcases mem_tightStep.1 hu with hu | ⟨-, hu, -⟩
    · exact Or.inl hu
    · exact Or.inr hu

/-- The `wreach` invariant doubles along a round of the canonical
chain. -/
theorem wreachBound_tightStep {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {s : ℕ}
    {D : Orientation n} (hD : WreachBound G π s D) (hs : 1 ≤ s) :
    WreachBound G π (2 * s) (tightStep π D) := by
  intro u v hu
  rcases mem_tightStep.1 hu with hu | ⟨-, hlink, hlt⟩
  · exact wreach_mono (by omega) (hD u v hu)
  · rcases hlink with hlink | hlink
    · exact wreach_of_transLink hD hlink
    · exact wreach_of_fratLink hD hlink hlt.le

/-- The canonical chain of an ordering. -/
noncomputable def canonChain (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) :
    ℕ → Orientation n
  | 0 => baseOr G π
  | i + 1 => tightStep π (canonChain G π i)

theorem piIncreasing_canonChain (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) :
    ∀ i, PiIncreasing π (canonChain G π i)
  | 0 => piIncreasing_baseOr G π
  | i + 1 => piIncreasing_tightStep (piIncreasing_canonChain G π i)

theorem wreachBound_canonChain (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) :
    ∀ i, WreachBound G π (2 ^ i) (canonChain G π i)
  | 0 => by simpa using baseOr_wreach G π
  | i + 1 => by
      have := wreachBound_tightStep (wreachBound_canonChain G π i) (Nat.one_le_two_pow)
      intro u v hu
      have h2 : 2 * 2 ^ i = 2 ^ (i + 1) := by ring
      exact h2 ▸ this u v hu

theorem isAugChain_canonChain (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) (r : ℕ) :
    IsAugChain G (canonChain G π) r :=
  ⟨baseOr_orients G π, fun i _ => augStep_tightStep (piIncreasing_canonChain G π i)⟩

/-- The in-degrees of the canonical chain are bounded by the size of a
weak reachability set. -/
theorem canonChain_inDeg_le {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {L : ℕ}
    {i : ℕ} (hi : 2 ^ i ≤ L) (v : Fin n) :
    ((canonChain G π i).inN v).card ≤ (wreach G π L v).ncard := by
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard (fun u hu => ?_) (Set.toFinite _)
  exact wreach_mono hi (wreachBound_canonChain G π i u v hu)

/-- The fraternity graph of a round of the canonical chain has small
back-degrees under `π`: a fraternal pair taken from its `π`-smaller end is
weakly `2 ^ (i+1)`-reachable. -/
theorem canonChain_fratGraph_backDegree {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)}
    {L : ℕ} {i : ℕ} (hi : 2 ^ (i + 1) ≤ L) (v : Fin n) :
    {u | (fratGraph (canonChain G π i)).Adj u v ∧ π u < π v}.ncard ≤
      (wreach G π L v).ncard := by
  refine Set.ncard_le_ncard (fun u hu => ?_) (Set.toFinite _)
  obtain ⟨⟨-, hlink⟩, hlt⟩ := hu
  have h2 : 2 * 2 ^ i = 2 ^ (i + 1) := by ring
  exact wreach_mono hi (h2 ▸ wreach_of_fratLink (wreachBound_canonChain G π i) hlink hlt.le)

/-! ### Fraternity densification

The load-bearing sparse-combinatorics lemma, independent of any ordering:
a dense piece of the fraternity graph forces a dense depth-1 minor of the
oriented graph itself.  Each fraternal pair carries a private witness `w`
with `u → w ← v`; the pairs whose witness lies inside the set account for
at most `d²` each, and a witness outside the set is contracted into the
one of its in-neighbours that lies on the most of its pairs, which by
averaging realizes at least a `1/d` fraction of them as edges of a
depth-1 minor on the set. -/

/-- The realized pairs of a contraction form a depth-1 minor on `S`, so
there are at most `D₁ · |S|` of them.  `Used w` marks the witnesses that
were contracted, `a w` the vertex of `S` they were contracted into, and
`R` the pairs realized this way, listed once each. -/
private theorem card_le_of_realized {H : SimpleGraph (Fin n)} {D : Orientation n} {D₁ : ℕ}
    (harc : ∀ u v : Fin n, u ∈ D.inN v → H.Adj u v)
    (hdens : Lax12.ShallowMinorDensity.HasDensityAtMost H 1 D₁)
    {S : Finset (Fin n)} (hS : S.Nonempty) (a : Fin n → Fin n) (Used : Fin n → Prop)
    (hUsed : ∀ w, Used w → w ∉ S ∧ a w ∈ D.inN w)
    (R : Finset (Fin n × Fin n))
    (hR : ∀ p ∈ R, p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2 ∧
      ∃ w, Used w ∧ a w = p.1 ∧ p.2 ∈ D.inN w)
    (hRasymm : ∀ p ∈ R, (p.2, p.1) ∉ R) :
    R.card ≤ D₁ * S.card := by
  classical
  have hs : 0 < S.card := Finset.card_pos.mpr hS
  set f : Fin S.card → Fin n := fun i => ((S.equivFin.symm i : {x // x ∈ S}) : Fin n)
    with hfdef
  have hfS : ∀ i, f i ∈ S := fun i => (S.equivFin.symm i).2
  have hfinj : Function.Injective f := fun i j hij =>
    S.equivFin.symm.injective (Subtype.ext hij)
  set g : Fin n → Fin S.card := fun x => if h : x ∈ S then S.equivFin ⟨x, h⟩ else ⟨0, hs⟩
    with hgdef
  have hfg : ∀ x ∈ S, f (g x) = x := by
    intro x hx
    simp [hfdef, hgdef, hx]
  set M : SimpleGraph (Fin S.card) :=
    { Adj := fun i j => (f i, f j) ∈ R ∨ (f j, f i) ∈ R
      symm := fun _ _ h => Or.symm h
      loopless := ⟨fun i h => by rcases h with h | h <;> exact (hR _ h).2.2.1 rfl⟩ }
    with hMdef
  have hMadj : ∀ i j, M.Adj i j ↔ ((f i, f j) ∈ R ∨ (f j, f i) ∈ R) := fun _ _ => Iff.rfl
  -- the depth-1 minor: contract every used witness into its target
  have hminor : Lax12.NowhereDenseClasses.HasShallowMinor H 1 M := by
    refine ⟨{ branch := fun i => insert (f i) {w | Used w ∧ a w = f i}
              center := f
              center_mem := fun i => Set.mem_insert _ _
              disjoint := ?_
              radius_le := ?_
              adj := ?_ }⟩
    · intro i j hij
      refine Set.disjoint_left.2 ?_
      rintro x (rfl | ⟨hx, hax⟩) hxj
      · rcases hxj with hc | ⟨hc, -⟩
        · exact hij (hfinj hc)
        · exact (hUsed _ hc).1 (hfS i)
      · rcases hxj with rfl | ⟨-, hax'⟩
        · exact (hUsed _ hx).1 (hfS j)
        · exact hij (hfinj (hax.symm.trans hax'))
    · rintro i x (rfl | ⟨hx, hax⟩)
      · exact ⟨SimpleGraph.Walk.nil, by simp, by simp⟩
      · have hadj : H.Adj (f i) x := hax ▸ harc (a x) x (hUsed x hx).2
        refine ⟨hadj.toWalk, by simp, fun y hy => ?_⟩
        have : y = f i ∨ y = x := by simpa using hy
        rcases this with rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ ⟨hx, hax⟩
    · intro i j hij
      have key : ∀ i j : Fin S.card, (f i, f j) ∈ R →
          ∃ x ∈ insert (f i) {w | Used w ∧ a w = f i},
            ∃ y ∈ insert (f j) {w | Used w ∧ a w = f j}, H.Adj x y := by
        intro i j hij
        obtain ⟨-, -, -, w, hw, haw, hmem⟩ := hR _ hij
        exact ⟨w, Set.mem_insert_of_mem _ ⟨hw, haw⟩, f j, Set.mem_insert _ _,
          (harc (f j) w hmem).symm⟩
      rcases (hMadj i j).1 hij with h | h
      · exact key i j h
      · obtain ⟨y, hy, x, hx, hadj⟩ := key j i h
        exact ⟨x, hx, y, hy, hadj.symm⟩
  -- the realized pairs inject into the edge set of the minor
  have himg : (R.image (fun p => s(g p.1, g p.2))).card = R.card := by
    refine Finset.card_image_of_injOn ?_
    intro p hp q hq hpq
    obtain ⟨hp1, hp2, hpne, -⟩ := hR p hp
    obtain ⟨hq1, hq2, -, -⟩ := hR q hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 : p.1 = q.1 := by rw [← hfg _ hp1, ← hfg _ hq1, h1]
      have e2 : p.2 = q.2 := by rw [← hfg _ hp2, ← hfg _ hq2, h2]
      exact Prod.ext e1 e2
    · have e1 : p.1 = q.2 := by rw [← hfg _ hp1, ← hfg _ hq2, h1]
      have e2 : p.2 = q.1 := by rw [← hfg _ hp2, ← hfg _ hq1, h2]
      exact absurd (show (p.2, p.1) ∈ R from by rw [e1, e2]; exact hq) (hRasymm p hp)
  have hsub : (↑(R.image (fun p => s(g p.1, g p.2))) : Set (Sym2 (Fin S.card))) ⊆ M.edgeSet := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨hp1, hp2, -, -⟩ := hR p hp
    refine (SimpleGraph.mem_edgeSet M).2 ((hMadj _ _).2 (Or.inl ?_))
    rw [hfg _ hp1, hfg _ hp2]
    exact hp
  have hle : R.card ≤ M.edgeSet.ncard := by
    rw [← himg, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  exact hle.trans (hdens S.card M hminor)

/-- The ordered pairs of adjacent vertices inside `S`. -/
noncomputable def pairsIn (F : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  @Finset.filter _ (fun p => F.Adj p.1 p.2) (Classical.decPred _) (S ×ˢ S)

theorem mem_pairsIn {F : SimpleGraph (Fin n)} {S : Finset (Fin n)} {p : Fin n × Fin n} :
    p ∈ pairsIn F S ↔ p.1 ∈ S ∧ p.2 ∈ S ∧ F.Adj p.1 p.2 := by
  rw [pairsIn, @Finset.mem_filter _ _ (Classical.decPred _), Finset.mem_product]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- Ordered pairs counted by their second vertex. -/
theorem card_pairsIn (F : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    (pairsIn F S).card = ∑ v ∈ S, (nbrsIn F S v).card := by
  classical
  have hEq : pairsIn F S = S.biUnion (fun v => (nbrsIn F S v).image (fun u => (u, v))) := by
    ext p
    simp only [mem_pairsIn, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨p.2, h2, p.1, mem_nbrsIn.2 ⟨h1, h3⟩, rfl⟩
    · rintro ⟨v, hv, u, hu, rfl⟩
      obtain ⟨hu1, hu2⟩ := mem_nbrsIn.1 hu
      exact ⟨hu1, hv, hu2⟩
  rw [hEq, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun v _ =>
      Finset.card_image_of_injective _ (fun x y h => (Prod.ext_iff.1 h).1)
  · intro x _ y _ hxy
    refine Finset.disjoint_left.2 fun p hp hp' => hxy ?_
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨u', -, hu'⟩ := Finset.mem_image.1 hp'
    exact ((Prod.ext_iff.1 hu').2).symm

/--
**Fraternity densification.**  If an orientation of `H` has in-degree at
most `d` and every depth-1 minor of `H` on `m` vertices has at most
`D₁ · m` edges, then the fraternity graph of the orientation is
`(d² + d · D₁)`-degenerate in the elimination sense: every nonempty set of
vertices carries a vertex of fraternity degree at most `d² + d · D₁`
inside it.

# Proof

Suppose every vertex of `S` had more than `d² + d · D₁` fraternity
neighbours inside `S`, so that the ordered fraternal pairs inside `S`
number more than `|S| · (d² + d · D₁)`.  Give each pair a witness `w`,
symmetrically in the two ends.

Pairs whose witness lies in `S` are charged to that witness: both ends
are in-neighbours of it, so each `w ∈ S` carries at most `d²` of them,
and there are at most `|S| · d²` in total.

For a witness `w` outside `S`, all its pairs live inside
`A_w = N⁻(w) ∩ S`, of size at most `d`.  Contract `w` into the vertex
`a w ∈ A_w` lying on the most of them: by averaging over `A_w` that is at
least a `1/d` fraction.  The contracted pairs are the edges of a depth-1
minor of `H` on the vertex set `S` — the branch set of `x ∈ S` is `x`
together with the witnesses contracted into it, each an out-neighbour of
`x` — and distinct pairs are distinct edges of it because a pair has only
one witness.  So the density bound caps them at `D₁ · |S|`, and the pairs
with a witness outside `S` at `d · D₁ · |S|`.

Adding the two counts contradicts the assumed lower bound.
-/
theorem fratGraph_lowDegreeVertex {H : SimpleGraph (Fin n)} {D : Orientation n} {d D₁ : ℕ}
    (harc : ∀ u v : Fin n, u ∈ D.inN v → H.Adj u v) (hd : D.InDegLE d)
    (hdens : Lax12.ShallowMinorDensity.HasDensityAtMost H 1 D₁) :
    LowDegreeVertices (fratGraph D) (d * d + d * D₁) := by
  classical
  intro S hS
  by_contra hcon
  push Not at hcon
  have hscard : 0 < S.card := Finset.card_pos.mpr hS
  -- the ordered fraternal pairs inside `S`, with the assumed lower bound
  have hPlow : S.card * (d * d + d * D₁ + 1) ≤ (pairsIn (fratGraph D) S).card := by
    rw [card_pairsIn]
    calc S.card * (d * d + d * D₁ + 1) = ∑ _v ∈ S, (d * d + d * D₁ + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ S, (nbrsIn (fratGraph D) S v).card :=
          Finset.sum_le_sum fun v hv => hcon v hv
  -- a witness for every fraternal pair, symmetric in the two ends
  have hexw : ∀ u v : Fin n, ∃ w : Fin n, FratLink D u v → (u ∈ D.inN w ∧ v ∈ D.inN w) := by
    intro u v
    by_cases h : FratLink D u v
    · obtain ⟨w, hu, hv⟩ := h
      exact ⟨w, fun _ => ⟨hu, hv⟩⟩
    · exact ⟨u, fun hc => absurd hc h⟩
  choose wit0 hwit0 using hexw
  set W : Fin n → Fin n → Fin n := fun u v => if u ≤ v then wit0 u v else wit0 v u with hWdef
  have hWsymm : ∀ u v, W u v = W v u := by
    intro u v
    rcases lt_trichotomy u v with h | rfl | h
    · simp [hWdef, h.le, not_le.2 h]
    · rfl
    · simp [hWdef, h.le, not_le.2 h]
  have hW : ∀ u v, FratLink D u v → (u ∈ D.inN (W u v) ∧ v ∈ D.inN (W u v)) := by
    intro u v h
    by_cases huv : u ≤ v
    · simpa [hWdef, huv] using hwit0 u v h
    · have h' := hwit0 v u h.symm
      simp only [hWdef, huv, if_false]
      exact ⟨h'.2, h'.1⟩
  -- the pairs whose witness lies outside `S`
  obtain ⟨Pout, hPout⟩ : ∃ Q : Finset (Fin n × Fin n), ∀ p,
      p ∈ Q ↔ (p ∈ pairsIn (fratGraph D) S ∧ W p.1 p.2 ∉ S) :=
    ⟨(pairsIn (fratGraph D) S).filter (fun p => W p.1 p.2 ∉ S), fun _ => Finset.mem_filter⟩
  have hsplit : (pairsIn (fratGraph D) S).card ≤
      ((pairsIn (fratGraph D) S).filter (fun p => W p.1 p.2 ∈ S)).card + Pout.card := by
    refine le_trans (Finset.card_le_card (fun p hp => ?_)) (Finset.card_union_le _ _)
    by_cases h : W p.1 p.2 ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hp, h⟩)
    · exact Finset.mem_union_right _ ((hPout p).2 ⟨hp, h⟩)
  -- witnesses inside `S` carry at most `d²` pairs each
  have hPin_le :
      ((pairsIn (fratGraph D) S).filter (fun p => W p.1 p.2 ∈ S)).card ≤ S.card * (d * d) := by
    have hfib : ∀ p ∈ (pairsIn (fratGraph D) S).filter (fun p => W p.1 p.2 ∈ S),
        W p.1 p.2 ∈ S := fun p hp => (Finset.mem_filter.1 hp).2
    rw [Finset.card_eq_sum_card_fiberwise hfib]
    refine le_trans (Finset.sum_le_sum (fun w _ => ?_)) (by rw [Finset.sum_const, smul_eq_mul])
    have hsub : ((pairsIn (fratGraph D) S).filter (fun p => W p.1 p.2 ∈ S)).filter
        (fun p => W p.1 p.2 = w) ⊆ (D.inN w) ×ˢ (D.inN w) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      obtain ⟨-, -, hadj⟩ := mem_pairsIn.1 (Finset.mem_filter.1 hp1).1
      have hmem := hW p.1 p.2 hadj.2
      rw [hp2] at hmem
      exact Finset.mem_product.2 hmem
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Finset.card_product]
    exact Nat.mul_le_mul (hd w) (hd w)
  -- unpacking a pair with a witness outside `S`
  have hPoutMem : ∀ p ∈ Pout, p.1 ∈ D.inN (W p.1 p.2) ∧ p.2 ∈ D.inN (W p.1 p.2) ∧
      p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2 ∧ W p.1 p.2 ∉ S := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := (hPout p).1 hp
    obtain ⟨h1, h2, hadj⟩ := mem_pairsIn.1 hp1
    obtain ⟨hm1, hm2⟩ := hW p.1 p.2 hadj.2
    exact ⟨hm1, hm2, h1, h2, hadj.1, hp2⟩
  -- contract each outside witness into the in-neighbour carrying most of its pairs
  have hA : ∀ w : Fin n, ∃ x : Fin n, (D.inN w ∩ S).Nonempty →
      (x ∈ D.inN w ∩ S ∧ ∀ y ∈ D.inN w ∩ S,
        (Pout.filter (fun p => W p.1 p.2 = w ∧ p.1 = y)).card ≤
          (Pout.filter (fun p => W p.1 p.2 = w ∧ p.1 = x)).card) := by
    intro w
    by_cases h : (D.inN w ∩ S).Nonempty
    · obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image (D.inN w ∩ S)
        (fun x => (Pout.filter (fun p => W p.1 p.2 = w ∧ p.1 = x)).card) h
      exact ⟨x, fun _ => ⟨hx, hmax⟩⟩
    · exact ⟨w, fun hc => absurd hc h⟩
  choose a ha using hA
  obtain ⟨R, hR⟩ : ∃ Q : Finset (Fin n × Fin n), ∀ p,
      p ∈ Q ↔ (p ∈ Pout ∧ a (W p.1 p.2) = p.1) :=
    ⟨Pout.filter (fun p => a (W p.1 p.2) = p.1), fun _ => Finset.mem_filter⟩
  -- averaging over the in-neighbourhood of a witness
  have hPout_le : Pout.card ≤ d * R.card := by
    have hfib : ∀ p ∈ Pout, W p.1 p.2 ∈ Pout.image (fun p => W p.1 p.2) :=
      fun p hp => Finset.mem_image_of_mem _ hp
    have hfibR : ∀ p ∈ R, W p.1 p.2 ∈ Pout.image (fun p => W p.1 p.2) :=
      fun p hp => Finset.mem_image_of_mem _ ((hR p).1 hp).1
    rw [Finset.card_eq_sum_card_fiberwise hfib, Finset.card_eq_sum_card_fiberwise hfibR,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨p₀, hp₀, hp₀w⟩ := Finset.mem_image.1 hw
    have hne : (D.inN w ∩ S).Nonempty := by
      refine ⟨p₀.1, Finset.mem_inter.2 ⟨?_, (hPoutMem p₀ hp₀).2.2.1⟩⟩
      rw [← hp₀w]; exact (hPoutMem p₀ hp₀).1
    obtain ⟨-, hamax⟩ := ha w hne
    have hfib1 : ∀ p ∈ Pout.filter (fun p => W p.1 p.2 = w), p.1 ∈ D.inN w ∩ S := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      refine Finset.mem_inter.2 ⟨?_, (hPoutMem p hp1).2.2.1⟩
      rw [← hp2]; exact (hPoutMem p hp1).1
    rw [Finset.card_eq_sum_card_fiberwise hfib1]
    have hRfib : R.filter (fun p => W p.1 p.2 = w) =
        Pout.filter (fun p => W p.1 p.2 = w ∧ p.1 = a w) := by
      ext p
      simp only [Finset.mem_filter, hR]
      constructor
      · rintro ⟨⟨hp, hpa⟩, hpw⟩
        exact ⟨hp, hpw, by rw [← hpw]; exact hpa.symm⟩
      · rintro ⟨hp, hpw, hpa⟩
        exact ⟨⟨hp, by rw [hpw]; exact hpa.symm⟩, hpw⟩
    rw [hRfib]
    have hterm : ∀ x ∈ D.inN w ∩ S,
        ((Pout.filter (fun p => W p.1 p.2 = w)).filter (fun p => p.1 = x)).card ≤
          (Pout.filter (fun p => W p.1 p.2 = w ∧ p.1 = a w)).card := by
      intro x hx
      rw [Finset.filter_filter]
      exact hamax x hx
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _
      (le_trans (Finset.card_le_card Finset.inter_subset_left) (hd w))
  -- the contracted pairs are the edges of a depth-1 minor on `S`
  have hR_le : R.card ≤ D₁ * S.card := by
    refine card_le_of_realized harc hdens hS a
      (fun w => (D.inN w ∩ S).Nonempty ∧ w ∉ S) ?_ R ?_ ?_
    · rintro w ⟨hne, hnS⟩
      exact ⟨hnS, (Finset.mem_inter.1 (ha w hne).1).1⟩
    · intro p hp
      obtain ⟨hpP, hpa⟩ := (hR p).1 hp
      obtain ⟨hm1, hm2, h1, h2, hne', hwS⟩ := hPoutMem p hpP
      exact ⟨h1, h2, hne', W p.1 p.2, ⟨⟨p.1, Finset.mem_inter.2 ⟨hm1, h1⟩⟩, hwS⟩, hpa, hm2⟩
    · intro p hp hq
      obtain ⟨hpP, hpa⟩ := (hR p).1 hp
      obtain ⟨-, hqa⟩ := (hR (p.2, p.1)).1 hq
      simp only at hqa
      rw [hWsymm p.2 p.1] at hqa
      exact (hPoutMem p hpP).2.2.2.2.1 (hpa.symm.trans hqa)
  -- the two counts contradict the assumed lower bound
  have hfinal : S.card * (d * d + d * D₁ + 1) ≤ S.card * (d * d + d * D₁) :=
    calc S.card * (d * d + d * D₁ + 1) ≤ (pairsIn (fratGraph D) S).card := hPlow
      _ ≤ ((pairsIn (fratGraph D) S).filter (fun p => W p.1 p.2 ∈ S)).card + Pout.card := hsplit
      _ ≤ S.card * (d * d) + d * (D₁ * S.card) :=
          Nat.add_le_add hPin_le (le_trans hPout_le (Nat.mul_le_mul_left d hR_le))
      _ = S.card * (d * d + d * D₁) := by ring
  have hexpand : S.card * (d * d + d * D₁ + 1) = S.card * (d * d + d * D₁) + S.card := by ring
  omega

/-! ### The augmentation density theorem -/

/-- Every graph carries an `r`-round augmentation chain whose in-degrees
and whose per-round fraternity back-degrees are bounded by its weak
`2 ^ r`-coloring number: take the canonical chain of an ordering
attaining `wcol G (2 ^ r)`. -/
theorem exists_augChain_wcol (G : SimpleGraph (Fin n)) (r : ℕ) :
    ∃ (D : ℕ → Orientation n) (σ : Fin n → ℕ), Function.Injective σ ∧
      IsAugChain G D r ∧
      (∀ i ≤ r, (D i).InDegLE (wcol G (2 ^ r))) ∧
      (∀ i < r, BackDegLE (fratGraph (D i)) σ (wcol G (2 ^ r))) := by
  obtain ⟨π, hπ⟩ := exists_ordering_wreach_le_wcol G (2 ^ r)
  refine ⟨canonChain G π, fun v => ((π v : Fin n) : ℕ),
    Fin.val_injective.comp π.injective, isAugChain_canonChain G π r, ?_, ?_⟩
  · intro i hi v
    exact (canonChain_inDeg_le (Nat.pow_le_pow_right (by omega) hi) v).trans (hπ v)
  · intro i hi v
    exact (canonChain_fratGraph_backDegree (Nat.pow_le_pow_right (by omega) hi) v).trans (hπ v)

/--
**Augmentation density theorem.**  For every nowhere dense class `C`,
every number of rounds `r` and every `δ > 0` there is a constant `c` such
that every subgraph `G` of a member, on `m` vertices, carries an
`r`-round tight transitive–fraternal augmentation chain in which

* every in-degree of every round is at most `c · m ^ δ`, and
* the fraternity graph of every round has back-degrees at most `c · m ^ δ`
  under a single vertex ranking `σ`.

The second clause is the "moreover" the greedy algorithm needs: together
with `inDegLE_of_augStep`, which charges a round at most `d + d² + k`
where `k` is the fraternal in-degree it chose, and `fratIn_le_of_backDegLE`,
which reads that in-degree off the ranking, it says that orienting the
fraternity graph along `σ` stays inside the budget.
-/
theorem exists_augChain_subpolynomial (C : GraphClass) (hC : NowhereDense C)
    (r : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∃ (D : ℕ → Orientation m) (σ : Fin m → ℕ) (k : ℕ),
          Function.Injective σ ∧
          IsAugChain G D r ∧ (k : ℝ) ≤ c * (m : ℝ) ^ δ ∧
          (∀ i ≤ r, (D i).InDegLE k) ∧
          (∀ i < r, BackDegLE (fratGraph (D i)) σ k) := by
  obtain ⟨c, hc⟩ :=
    Lax12Proofs.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense C hC (2 ^ r) δ hδ
  refine ⟨c, fun n Gn hGn m G hsub => ?_⟩
  obtain ⟨D, σ, hinj, hchain, hdeg, hback⟩ := exists_augChain_wcol G r
  exact ⟨D, σ, wcol G (2 ^ r), hinj, hchain, hc n Gn hGn m G hsub, hdeg, hback⟩

/-- The in-degree half of the augmentation density theorem, in the
`c · m ^ δ` form. -/
theorem exists_augChain_inDeg_subpolynomial (C : GraphClass) (hC : NowhereDense C)
    (r : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∃ D : ℕ → Orientation m, IsAugChain G D r ∧
          ∀ i ≤ r, ∀ v, (((D i).inN v).card : ℝ) ≤ c * (m : ℝ) ^ δ := by
  obtain ⟨c, hc⟩ := exists_augChain_subpolynomial C hC r δ hδ
  refine ⟨c, fun n Gn hGn m G hsub => ?_⟩
  obtain ⟨D, σ, k, -, hchain, hk, hdeg, -⟩ := hc n Gn hGn m G hsub
  exact ⟨D, hchain, fun i hi v => le_trans (by exact_mod_cast hdeg i hi v) hk⟩

/-- The fraternity half of the augmentation density theorem: along the
chain of `exists_augChain_subpolynomial`, every round's fraternity graph
is `⌊c · m ^ δ⌋`-degenerate. -/
theorem exists_augChain_fratGraph_degeneracy (C : GraphClass) (hC : NowhereDense C)
    (r : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∃ (D : ℕ → Orientation m) (k : ℕ), IsAugChain G D r ∧ (k : ℝ) ≤ c * (m : ℝ) ^ δ ∧
          ∀ i < r, DegeneracyLE (fratGraph (D i)) k := by
  obtain ⟨c, hc⟩ := exists_augChain_subpolynomial C hC r δ hδ
  refine ⟨c, fun n Gn hGn m G hsub => ?_⟩
  obtain ⟨D, σ, k, hinj, hchain, hk, -, hback⟩ := hc n Gn hGn m G hsub
  exact ⟨D, k, hchain, hk, fun i hi => ⟨σ, hinj, hback i hi⟩⟩

/-! ### The greedy chain

The chain of `exists_augChain_subpolynomial` is one good chain, built from
a weak-coloring ordering.  The algorithm of Grohe–Kreutzer–Siebertz builds
its own, orienting each round's fraternity graph by a greedy elimination
ordering.  What one such round costs is `exists_greedy_round`, proved
unconditionally from the depth-1 density of the round's graph; what a
whole greedy chain costs is `greedy_chain_inDegLE`, which carries that
density as a hypothesis.

`AugmentedDepthOneDensity` is the one statement of this file that is not
proved: that the *augmented* graphs of a nowhere dense input again have
subpolynomial depth-1 minor density.  Its proof is the shallow-minor
transfer of Nešetřil–Ossona de Mendez — a depth-1 minor of an augmented
graph is a bounded-depth minor of the previous round's graph — which the
path invariant alone does not give, since the realizing walks of distinct
arcs are not disjoint. -/

/-- Every round's augmented graph has depth-1 minor density at most `D₁`.
This is the hypothesis the greedy chain bound is stated over. -/
def AugmentedDepthOneDensity (D : ℕ → Orientation n) (r D₁ : ℕ) : Prop :=
  ∀ i < r, Lax12.ShallowMinorDensity.HasDensityAtMost (D i).toGraph 1 D₁

/-- The round oriented its fraternal edges along a ranking that is as
good as the degeneracy of the fraternity graph allows: the specification
of a greedy elimination ordering. -/
def GreedyFratRound (D D' : Orientation n) : Prop :=
  ∀ k : ℕ, LowDegreeVertices (fratGraph D) k →
    ∃ σ : Fin n → ℕ, BackDegLE (fratGraph D) σ k ∧
      ∀ u v, u ∈ D'.inN v → (fratGraph D).Adj u v → σ u < σ v

/-- The in-degree budget after `i` greedy rounds from a starting
in-degree `d`, given a depth-1 density bound `D₁`: old arcs, `d²`
transitive arcs, and a fraternity graph of degeneracy `d² + d · D₁`. -/
def budget (d D₁ : ℕ) : ℕ → ℕ
  | 0 => d
  | i + 1 => budget d D₁ i + budget d D₁ i * budget d D₁ i +
      (budget d D₁ i * budget d D₁ i + budget d D₁ i * D₁)

/-- **One greedy round.**  If the round's orientation has in-degree at
most `d` and every depth-1 minor of `H` on `m` vertices has at most
`D₁ · m` edges, then the fraternity graph is `(d² + d · D₁)`-degenerate,
and any augmentation step orienting its fraternal edges along a witnessing
ranking has in-degree at most `d + d² + (d² + d · D₁)`. -/
theorem exists_greedy_round {H : SimpleGraph (Fin n)} {D : Orientation n} {d D₁ : ℕ}
    (harc : ∀ u v : Fin n, u ∈ D.inN v → H.Adj u v) (hd : D.InDegLE d)
    (hdens : Lax12.ShallowMinorDensity.HasDensityAtMost H 1 D₁) :
    ∃ σ : Fin n → ℕ, Function.Injective σ ∧
      BackDegLE (fratGraph D) σ (d * d + d * D₁) ∧
      ∀ D' : Orientation n, AugStep D D' →
        (∀ u v, u ∈ D'.inN v → (fratGraph D).Adj u v → σ u < σ v) →
        D'.InDegLE (d + d * d + (d * d + d * D₁)) := by
  obtain ⟨σ, hinj, hσ⟩ :=
    degeneracyLE_of_lowDegreeVertices (fratGraph_lowDegreeVertex harc hd hdens)
  exact ⟨σ, hinj, hσ, fun D' hstep hor =>
    inDegLE_of_augStep hstep hd (fratIn_le_of_backDegLE hσ hor)⟩

/-- **The greedy chain.**  Along a chain whose rounds orient their
fraternity graphs greedily, the in-degrees follow the budget recursion —
given the depth-1 density of the augmented graphs, the one input this file
carries as a hypothesis rather than proving. -/
theorem greedy_chain_inDegLE {G : SimpleGraph (Fin n)} {D : ℕ → Orientation n}
    {r d D₁ : ℕ} (hchain : IsAugChain G D r)
    (hdens : AugmentedDepthOneDensity D r D₁)
    (hgreedy : ∀ i < r, GreedyFratRound (D i) (D (i + 1)))
    (hd0 : (D 0).InDegLE d) :
    ∀ i ≤ r, (D i).InDegLE (budget d D₁ i) := by
  intro i
  induction i with
  | zero => intro _; exact hd0
  | succ i ih =>
      intro hi
      have hdi := ih (by omega)
      have hlow : LowDegreeVertices (fratGraph (D i))
          (budget d D₁ i * budget d D₁ i + budget d D₁ i * D₁) :=
        fratGraph_lowDegreeVertex (fun _ _ h => Or.inl h) hdi (hdens i (by omega))
      obtain ⟨σ, hσ, hor⟩ := hgreedy i (by omega) _ hlow
      exact inDegLE_of_augStep (hchain.2 i (by omega)) hdi
        (fratIn_le_of_backDegLE hσ hor)

end Lax3Proofs.Augmentation
