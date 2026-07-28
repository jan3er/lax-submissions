import Lax3Proofs.SyntaxLemmas
import Lax3Proofs.WalkDistance

/-!
The **edgeless base case** of the model-checking evaluator: satisfaction
of distance logic in the graph `⊥` on `Fin n`, the arena at which
`Lax3Proofs.Evaluator` stops descending and returns `Sat` itself. The
RAM driver has to *evaluate* that value, by color lookups and counting;
the lemmas below are the bridge it evaluates along.

An edgeless graph has no walks but the empty ones, so every distance in
it is zero or infinite. Two vertices are within distance `d` exactly when
they are equal, at every radius, and the distance from a vertex to a
color class is smaller than `r` exactly when the vertex itself carries
the color and `r` is positive. All five atoms therefore reduce to two
questions about the environment — which of its entries are equal, and
which colors each entry carries — and those same two questions decide
every formula, because neither quantifier can reach anything else:

* a *local* quantifier collapses to a finite disjunction over its guard
  set, `sat_exL_bot`, since the only vertex within any radius of `m i`
  is `m i` itself. A local formula is thus decided by reading the rows
  of the entries already in scope, with no search over the vertex set at
  all — which is why a local sentence, whose guard set is empty, is
  simply false, and why the evaluator's scatter atoms are the only place
  a search survives;
* an *unrestricted* quantifier does range over all of `Fin n`, but it
  sees a witness only through the witness's *row* — the colors it
  carries — and through the witness's equalities with the tuple already
  in scope. Two vertices with equal rows that both lie off the tuple are
  therefore interchangeable as witnesses, `sat_exU_bot_swap`, so a
  witness search need only try the entries of the tuple and one
  representative of each row realized off it: `sat_exU_bot_of_repr`.
  There are at most `2 ^ L` rows, `ncard_le_of_injOn_rowOf`, so the
  search runs over at most `k + 2 ^ L` candidates however large `n` is.
  That is the sense in which the base case is finite.

# The permutation trick

Interchangeability of equal-row witnesses is *not* proved by an
induction carrying a hypothesis that two environments have matching rows
and matching equality patterns. That induction does not close: at an
unrestricted quantifier it must turn a witness for the first environment
into a witness for the second, and a vertex off the second tuple with
the prescribed row need not exist — over `Fin 2` and `Fin 1` with no
colors the two one-element environments match, and `∃ y, y ≠ x` separates
them.

What does close is moving the whole structure rather than the
environment. A permutation of the vertices preserving every color class
is an automorphism of an edgeless colored graph, so it preserves
satisfaction outright: `sat_perm_bot`, the diagonal case of the transport
`sat_congr_bot_of_bij` along a color-preserving bijection between two
vertex sets. The transposition of two off-tuple vertices of equal rows is
such a permutation, and it fixes the tuple pointwise, so only the witness
moves — which is exactly `sat_exU_bot_swap`.

# Formalization notes

Nothing here hands a concept-side definition to a tactic. `Sat` and
`WithinDist` are taken apart through the clause lemmas of
`Lax3Proofs.SyntaxLemmas` and through the atom lemmas of this file, which
are their edgeless specializations; `rowOf`, introduced here, is unfolded
freely.

`withinDist_bot` and `exists_walk_bot_lt` are stated for an arbitrary
vertex type, as the walk-distance lemmas of `Lax3Proofs.WalkDistance`
are; everything about `Sat` is tied to `Fin n`, as `Sat` itself is.

The row of a vertex is a `Set (Fin L)`, matching the `Set`-valued color
classes of `Lax3.ColoredGraphs`; row equality and the pointwise
color-agreement the transfer lemmas ask for are the same statement, and
`rowOf_eq_iff` is the translation.
-/

namespace Lax3Proofs.BotEval

open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.SyntaxLemmas Lax3Proofs.WalkDistance

/-! ### Walks in an edgeless graph

The only walks of `⊥` are the empty ones: a `cons` would carry an edge.
Both facts below are that observation, read off at the two shapes the
distance atoms of the logic use — a non-strict bound between two
vertices, and a strict bound to a color class.
-/

section Walks

variable {V : Type*} {u v : V} {d r : ℕ}

/-- **Distance in an edgeless graph is equality.** At every radius, and
in particular at radius `0`. -/
theorem withinDist_bot : WithinDist (⊥ : SimpleGraph V) d u v ↔ u = v := by
  rw [withinDist_iff]
  constructor
  · rintro ⟨w, -⟩
    cases w with
    | nil => rfl
    | cons h _ => exact absurd h (by simp)
  · rintro rfl
    exact ⟨.nil, by simp⟩

/-- A strictly bounded walk in an edgeless graph exists exactly when its
endpoints coincide and the bound is positive: the empty walk is the only
candidate, and its length is `0`. -/
theorem exists_walk_bot_lt :
    (∃ w : (⊥ : SimpleGraph V).Walk u v, w.length < r) ↔ u = v ∧ 0 < r := by
  constructor
  · rintro ⟨w, hw⟩
    cases w with
    | nil => exact ⟨rfl, by simpa using hw⟩
    | cons h _ => exact absurd h (by simp)
  · rintro ⟨rfl, hr⟩
    exact ⟨.nil, by simpa using hr⟩

end Walks

/-! ### The atoms

The five atoms of the logic on an edgeless arena. Adjacency is never
satisfied, both distance atoms degenerate into their radius-zero
readings, and equality and color atoms are what they always are: the
whole table is a question about the equalities and the colors of the
environment's entries.
-/

section Atoms

variable {L n k : ℕ} {col : Coloring n L} {m : Fin k → Fin n}

/-- An adjacency atom is never satisfied on an edgeless arena. -/
theorem sat_adj_bot (i j : Fin k) :
    Sat (⊥ : SimpleGraph (Fin n)) col m (.adj i j) ↔ False := by
  rw [sat_adj]
  simp

/-- An equality atom reads the environment, edgeless or not. -/
theorem sat_eq_bot (i j : Fin k) :
    Sat (⊥ : SimpleGraph (Fin n)) col m (.eq i j) ↔ m i = m j := sat_eq i j

/-- A color atom reads the coloring, edgeless or not. -/
theorem sat_color_bot (c : Fin L) (i : Fin k) :
    Sat (⊥ : SimpleGraph (Fin n)) col m (.color c i) ↔ m i ∈ col c := sat_color c i

/-- **A binary distance atom is an equality test on an edgeless arena**,
whatever its radius. -/
theorem sat_distLe_bot (d : ℕ) (i j : Fin k) :
    Sat (⊥ : SimpleGraph (Fin n)) col m (.distLe d i j) ↔ m i = m j := by
  rw [sat_distLe, withinDist_bot]

/-- **A unary distance atom is a color lookup at the variable itself on
an edgeless arena**: the only vertex the walk can reach is `m i`, so the
atom holds exactly when `m i` carries the color and the strict radius
leaves room for the empty walk. -/
theorem sat_distColorLt_bot (r : ℕ) (c : Fin L) (i : Fin k) :
    Sat (⊥ : SimpleGraph (Fin n)) col m (.distColorLt r c i) ↔ 0 < r ∧ m i ∈ col c := by
  rw [sat_distColorLt]
  constructor
  · rintro ⟨y, hy, hw⟩
    obtain ⟨rfl, hr⟩ := exists_walk_bot_lt.mp hw
    exact ⟨hr, hy⟩
  · rintro ⟨hr, hi⟩
    exact ⟨m i, hi, exists_walk_bot_lt.mpr ⟨rfl, hr⟩⟩

end Atoms

/-! ### The collapse of local quantification -/

section Local

variable {L n k : ℕ} {col : Coloring n L} {m : Fin k → Fin n}

/-- **A local quantifier over an edgeless arena is a finite disjunction
over its guard set.** The guard asks for a vertex within radius `r` of
some `m i`, and on an edgeless arena the only such vertex is `m i`, so
the quantifier ranges over the entries of the environment named by the
guard set and over nothing else. Several guard variables may name the
same vertex; the disjunction then merely repeats a disjunct, which is
why the equivalence needs no injectivity side condition.

In particular a local *sentence* is decided outright, its guard set
being a `Finset (Fin 0)`. -/
theorem sat_exL_bot (r : ℕ) (g : Finset (Fin k)) (φ : DistFO L (k + 1)) :
    Sat (⊥ : SimpleGraph (Fin n)) col m (.exL r g φ) ↔
      ∃ i ∈ g, Sat (⊥ : SimpleGraph (Fin n)) col (Fin.snoc m (m i)) φ := by
  rw [sat_exL]
  constructor
  · rintro ⟨v, ⟨i, hi, hd⟩, hsat⟩
    exact ⟨i, hi, by rwa [withinDist_bot.mp hd]⟩
  · rintro ⟨i, hi, hsat⟩
    exact ⟨m i, ⟨i, hi, withinDist_bot.mpr rfl⟩, hsat⟩

end Local

/-! ### Transporting satisfaction along a color-preserving bijection

An edgeless colored graph is a pure unary structure, so any bijection of
its vertices matching the color classes is an isomorphism of it, and
satisfaction travels along. The induction is the trivial one: the two
distance atoms have already become equality tests, and both quantifiers
push their witness through the bijection.
-/

section Transfer

variable {L n n' : ℕ}

/-- **Satisfaction on edgeless arenas transports along a
color-preserving bijection of the vertex sets.** -/
theorem sat_congr_bot_of_bij (e : Fin n ≃ Fin n') {col : Coloring n L} {col' : Coloring n' L}
    (hcol : ∀ (c : Fin L) (v : Fin n), v ∈ col c ↔ e v ∈ col' c) {k : ℕ} (φ : DistFO L k)
    (m : Fin k → Fin n) :
    Sat (⊥ : SimpleGraph (Fin n)) col m φ ↔ Sat (⊥ : SimpleGraph (Fin n')) col' (⇑e ∘ m) φ := by
  induction φ with
  | adj i j => rw [sat_adj_bot, sat_adj_bot]
  | eq i j => rw [sat_eq_bot, sat_eq_bot]; exact (e.apply_eq_iff_eq).symm
  | color c i => rw [sat_color_bot, sat_color_bot]; exact hcol c (m i)
  | distLe r i j => rw [sat_distLe_bot, sat_distLe_bot]; exact (e.apply_eq_iff_eq).symm
  | distColorLt r c i =>
    rw [sat_distColorLt_bot, sat_distColorLt_bot]
    exact and_congr_right fun _ => hcol c (m i)
  | not φ ih => rw [sat_not, sat_not, ih m]
  | and φ ψ ihφ ihψ => rw [sat_and, sat_and, ihφ m, ihψ m]
  | exU φ ih =>
    rw [sat_exU, sat_exU]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨e v, ?_⟩
      have h := (ih (Fin.snoc m v)).mp hv
      rwa [Fin.comp_snoc] at h
    · rintro ⟨v', hv'⟩
      refine ⟨e.symm v', (ih (Fin.snoc m (e.symm v'))).mpr ?_⟩
      rw [Fin.comp_snoc]
      simpa using hv'
  | exL r g φ ih =>
    rw [sat_exL_bot, sat_exL_bot]
    refine exists_congr fun i => and_congr_right fun _ => ?_
    have h := ih (Fin.snoc m (m i))
    rwa [Fin.comp_snoc] at h

/-- **A color-preserving permutation of the vertices preserves
satisfaction on an edgeless arena.** The diagonal case of
`sat_congr_bot_of_bij`: such a permutation is an automorphism of the
edgeless colored graph, there being no edges for it to respect. -/
theorem sat_perm_bot {σ : Equiv.Perm (Fin n)} {col : Coloring n L}
    (hσ : ∀ (c : Fin L) (v : Fin n), v ∈ col c ↔ σ v ∈ col c) {k : ℕ} (φ : DistFO L k)
    (m : Fin k → Fin n) :
    Sat (⊥ : SimpleGraph (Fin n)) col m φ ↔ Sat (⊥ : SimpleGraph (Fin n)) col (⇑σ ∘ m) φ :=
  sat_congr_bot_of_bij σ hσ φ m

end Transfer

/-! ### Interchanging witnesses -/

section Witness

variable {L n k : ℕ} {col : Coloring n L} {m : Fin k → Fin n}

/-- **Two off-tuple vertices with equal rows are interchangeable as
witnesses.** Their transposition preserves every color class — it moves
only those two vertices, which agree on all of them — and fixes the
tuple pointwise, so `sat_perm_bot` moves the witness and nothing else.
-/
theorem sat_exU_bot_swap (φ : DistFO L (k + 1)) {v v' : Fin n}
    (hrow : ∀ c : Fin L, v ∈ col c ↔ v' ∈ col c) (hv : ∀ i, m i ≠ v) (hv' : ∀ i, m i ≠ v') :
    Sat (⊥ : SimpleGraph (Fin n)) col (Fin.snoc m v) φ ↔
      Sat (⊥ : SimpleGraph (Fin n)) col (Fin.snoc m v') φ := by
  have hswap : ∀ (c : Fin L) (u : Fin n), u ∈ col c ↔ Equiv.swap v v' u ∈ col c := by
    intro c u
    rcases eq_or_ne u v with rfl | hu
    · rw [Equiv.swap_apply_left]
      exact hrow c
    · rcases eq_or_ne u v' with rfl | hu'
      · rw [Equiv.swap_apply_right]
        exact (hrow c).symm
      · rw [Equiv.swap_apply_of_ne_of_ne hu hu']
  have hm : ⇑(Equiv.swap v v') ∘ m = m :=
    funext fun i => Equiv.swap_apply_of_ne_of_ne (hv i) (hv' i)
  have hlast : Equiv.swap v v' v = v' := Equiv.swap_apply_left v v'
  rw [sat_perm_bot hswap φ (Fin.snoc m v), Fin.comp_snoc, hm, hlast]

/-- The color row of a vertex: the set of colors it carries. On an
edgeless arena the row and the equalities with the environment are all a
formula can see of a vertex. -/
def rowOf (col : Coloring n L) (v : Fin n) : Set (Fin L) := {c | v ∈ col c}

/-- Membership in a row is carrying the color. -/
theorem mem_rowOf {v : Fin n} {c : Fin L} : c ∈ rowOf col v ↔ v ∈ col c := Iff.rfl

/-- Two vertices have the same row exactly when they carry the same
colors: the translation between the two shapes of the transfer
hypothesis. -/
theorem rowOf_eq_iff {v w : Fin n} :
    rowOf col v = rowOf col w ↔ ∀ c : Fin L, v ∈ col c ↔ w ∈ col c := Set.ext_iff

/-- **The witness search of an unrestricted quantifier is finite.** A
set `W` is an *off-tuple representative system* when every vertex off the
environment's range has a same-row companion in `W` that is also off the
range; against such a `W`, a quantifier is satisfied exactly when one of
the environment's own entries or one of the off-tuple representatives
satisfies its body. Nothing about `W` is needed beyond the hypothesis —
in particular no minimality — so the base-case program may use whatever
representative system it has built. -/
theorem sat_exU_bot_of_repr (φ : DistFO L (k + 1)) (W : Set (Fin n))
    (hW : ∀ v ∉ Set.range m, ∃ w ∈ W, w ∉ Set.range m ∧ ∀ c : Fin L, v ∈ col c ↔ w ∈ col c) :
    Sat (⊥ : SimpleGraph (Fin n)) col m (.exU φ) ↔
      (∃ i, Sat (⊥ : SimpleGraph (Fin n)) col (Fin.snoc m (m i)) φ) ∨
        ∃ w ∈ W, w ∉ Set.range m ∧ Sat (⊥ : SimpleGraph (Fin n)) col (Fin.snoc m w) φ := by
  rw [sat_exU]
  constructor
  · rintro ⟨v, hv⟩
    by_cases hmem : v ∈ Set.range m
    · obtain ⟨i, rfl⟩ := hmem
      exact Or.inl ⟨i, hv⟩
    · obtain ⟨w, hwW, hwr, hrow⟩ := hW v hmem
      exact Or.inr ⟨w, hwW, hwr,
        (sat_exU_bot_swap φ hrow (fun i hi => hmem ⟨i, hi⟩) (fun i hi => hwr ⟨i, hi⟩)).mp hv⟩
  · rintro (⟨i, hi⟩ | ⟨w, -, -, hw⟩)
    · exact ⟨m i, hi⟩
    · exact ⟨w, hw⟩

/-- **An off-tuple representative system always exists**, and one taking
each realized row exactly once: choose, for each row realized off the
environment's range, one vertex realizing it. The choice is by
`Exists.choose` at the row, so two members of the system with equal rows
are the same choice, which is the injectivity claim. -/
theorem exists_offRepr (col : Coloring n L) (m : Fin k → Fin n) :
    ∃ W : Set (Fin n), Set.InjOn (rowOf col) W ∧
      ∀ v ∉ Set.range m, ∃ w ∈ W, w ∉ Set.range m ∧ ∀ c : Fin L, v ∈ col c ↔ w ∈ col c := by
  refine ⟨{w | ∃ (s : Set (Fin L)) (h : ∃ u, u ∉ Set.range m ∧ rowOf col u = s), w = h.choose},
    ?_, ?_⟩
  · rintro w₁ ⟨s₁, h₁, rfl⟩ w₂ ⟨s₂, h₂, rfl⟩ hrow
    have hs : s₁ = s₂ := by rw [← h₁.choose_spec.2, ← h₂.choose_spec.2, hrow]
    subst hs
    rfl
  · intro v hv
    have h : ∃ u, u ∉ Set.range m ∧ rowOf col u = rowOf col v := ⟨v, hv, rfl⟩
    exact ⟨h.choose, ⟨rowOf col v, h, rfl⟩, h.choose_spec.1,
      rowOf_eq_iff.mp h.choose_spec.2.symm⟩

/-- **There are at most `2 ^ L` rows**, so a representative system taking
each row once has at most that many members: the witness search of an
unrestricted quantifier runs over at most `k + 2 ^ L` candidates,
however large the arena. -/
theorem ncard_le_of_injOn_rowOf {W : Set (Fin n)} (h : Set.InjOn (rowOf col) W) :
    W.ncard ≤ 2 ^ L := by
  classical
  have hcard : Nat.card (Set (Fin L)) = 2 ^ L := by
    rw [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_fin]
  calc W.ncard = (rowOf col '' W).ncard := h.ncard_image.symm
    _ ≤ (Set.univ : Set (Set (Fin L))).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    _ = 2 ^ L := by rw [Set.ncard_univ, hcard]

end Witness

end Lax3Proofs.BotEval
