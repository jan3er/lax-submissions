import Lax11Proofs.MsoAdequacy

/-!
Composition: gluing two regions along their marked overlap.

This is the make-or-break theorem of the type algebra (plan decision
C3.3, rev 4). Stated as a *congruence*, like everything else here: no
function on types is constructed, and no structure is ever glued. Two
regions `X`, `Y` of one ambient graph, overlapping only in marked
vertices and with no edges between their private parts, have a union
whose `q`-type is determined by the two `q`-types — *across ambients*,
so the same two types occurring in a different graph give the same type
of the union there. That is exactly the statement the tree fold needs:
it is what says a table entry exists at all.

The marks are handled with a **shared pool**. The union's marks are one
tuple `m : Fin c → Fin n`, and the two sides read their own marks off it
through index maps `σ : Fin a → Fin c` and `τ : Fin b → Fin c`; the
hypotheses `Glue` collects (marks lie in their region, the pool is
covered by the two sides, the overlap is marked on both sides, no edges
between the private parts) are then all statements about the pool. Plan
C3.3 asks for *concatenated* marks, which is the instance
`c = a + b, σ = Fin.castAdd, τ = Fin.natAdd` — `typ_append_congr` at the
end of the file, five lines. The pool form is the one to prove, for two
reasons: the vertex-move step extends the pool by `Fin.snoc` and both
sides' index maps then re-index by lemmas that already exist
(`snoc_comp_liftLast`, `Fin.snoc_comp_castSucc`), so the induction
contains *no* mark bookkeeping at all; and the sequential fold of C4
grows one pool as it absorbs children, which is the pool form applied
repeatedly rather than an `Fin.append`-associativity argument each time.

Where the content actually sits:

* the atomic layer (`atomic_union_congr`), and inside it the cross pair
  `adj_of_cross` — an edge from `X` to `Y` has an endpoint in the
  overlap, hence is *recorded in one of the two diagrams*, and the
  overlap pattern moves it to the other ambient. This is the only place
  the no-edges hypothesis is used, and it is used at every rank, since
  the diagram is a component of every type;
* the vertex move, where the new mark's overlap pattern has to be
  re-established (`v` is a mark of the other side iff its counterpart
  `w` is) — the diagram of the transferred type does it;
* the set move, where `S` splits as `(S ∩ X, S ∩ Y)`; the two witnesses
  produced on the other side agree on the overlap because the overlap
  is marked and the diagram records the memberships of marks. Their
  union is the witness, and `typ_congr_inter` throws away the parts
  outside each region.

One general fact about `typ` is proved on the way, because the vertex
move needs the *other* side's hypothesis one rank down:
`typ_succ_congr`, the type of rank `q+1` determines the type of rank `q`.
-/

namespace Lax11Proofs.MsoTypes

variable {n n₁ n₂ c a b q r s : ℕ}

/-! ### The gluing hypotheses -/

/-- The hypotheses under which `X` and `Y` may be glued: their marks —
read off the shared pool `m` by `σ` and `τ` — lie in their own region,
every pool position is a mark of one of the sides, every vertex of the
overlap is marked on both sides, and no edge of `G` joins `X ∖ Y` to
`Y ∖ X`. -/
structure Glue (G : SimpleGraph (Fin n)) (X Y : Set (Fin n)) (m : Fin c → Fin n)
    (σ : Fin a → Fin c) (τ : Fin b → Fin c) : Prop where
  /-- `X`'s marks lie in `X`. -/
  markX : ∀ i, m (σ i) ∈ X
  /-- `Y`'s marks lie in `Y`. -/
  markY : ∀ j, m (τ j) ∈ Y
  /-- Every mark of the pool belongs to one of the two sides. -/
  cover : ∀ k, (∃ i, σ i = k) ∨ (∃ j, τ j = k)
  /-- A vertex of the overlap is a mark of `X`. -/
  interX : ∀ v ∈ X, v ∈ Y → ∃ i, m (σ i) = v
  /-- A vertex of the overlap is a mark of `Y`. -/
  interY : ∀ v ∈ X, v ∈ Y → ∃ j, m (τ j) = v
  /-- No edges between `X ∖ Y` and `Y ∖ X`: an edge from `X` to `Y` has
  an endpoint in the overlap. -/
  sep : ∀ u ∈ X, ∀ v ∈ Y, G.Adj u v → u ∈ Y ∨ v ∈ X

variable {G : SimpleGraph (Fin n)} {X Y : Set (Fin n)} {m : Fin c → Fin n}
  {σ : Fin a → Fin c} {τ : Fin b → Fin c}

/-- Gluing is symmetric in the two sides. -/
theorem Glue.symm (h : Glue G X Y m σ τ) : Glue G Y X m τ σ where
  markX := h.markY
  markY := h.markX
  cover k := (h.cover k).symm
  interX v hv hv' := h.interY v hv' hv
  interY v hv hv' := h.interX v hv' hv
  sep u hu v hv huv := (h.sep v hv u hu huv.symm).symm

/-- Every mark of the pool lies in the union. -/
theorem Glue.mem_union (h : Glue G X Y m σ τ) (k : Fin c) : m k ∈ X ∪ Y := by
  obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ := h.cover k
  · exact Or.inl (h.markX i)
  · exact Or.inr (h.markY j)

/-! ### The atomic layer

The rank-`0` case, and — since the diagram is a component of a type of
every rank — the diagram component of every case above it. -/

variable {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
  {X₁ Y₁ : Set (Fin n₁)} {X₂ Y₂ : Set (Fin n₂)}
  {m₁ : Fin c → Fin n₁} {m₂ : Fin c → Fin n₂}
  {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)}

/-- **The cross pair.** An edge between a mark of `X` and a mark of `Y`
transfers to the other ambient graph. It cannot be read off either
diagram directly — the two marks are on different sides — but by the
no-edges hypothesis one of its endpoints lies in the overlap, and is
therefore *also* a mark of the other side, where the diagram does record
the edge; the overlap pattern then identifies the two mark positions in
the second ambient as well. -/
theorem adj_of_cross (g₁ : Glue G₁ X₁ Y₁ m₁ σ τ)
    (hpat : ∀ i j, m₁ (σ i) = m₁ (τ j) ↔ m₂ (σ i) = m₂ (τ j))
    (hX : Atomic.of G₁ (m₁ ∘ σ) A₁ = Atomic.of G₂ (m₂ ∘ σ) A₂)
    (hY : Atomic.of G₁ (m₁ ∘ τ) A₁ = Atomic.of G₂ (m₂ ∘ τ) A₂)
    (i : Fin a) (j : Fin b) (h : G₁.Adj (m₁ (σ i)) (m₁ (τ j))) :
    G₂.Adj (m₂ (σ i)) (m₂ (τ j)) := by
  rcases g₁.sep _ (g₁.markX i) _ (g₁.markY j) h with hu | hv
  · -- `m₁ (σ i)` is in the overlap: it is a mark of `Y` too.
    obtain ⟨j', hj'⟩ := g₁.interY _ (g₁.markX i) hu
    have hadj : G₂.Adj (m₂ (τ j')) (m₂ (τ j)) := by
      have := adj_iff_of_diagram_eq hY j' j
      simp only [Function.comp_apply] at this
      exact this.mp (hj' ▸ h)
    have : m₂ (σ i) = m₂ (τ j') := (hpat i j').mp hj'.symm
    rwa [this]
  · -- `m₁ (τ j)` is in the overlap: it is a mark of `X` too.
    obtain ⟨i', hi'⟩ := g₁.interX _ hv (g₁.markY j)
    have hadj : G₂.Adj (m₂ (σ i)) (m₂ (σ i')) := by
      have := adj_iff_of_diagram_eq hX i i'
      simp only [Function.comp_apply] at this
      exact this.mp (hi' ▸ h)
    have : m₂ (σ i') = m₂ (τ j) := (hpat i' j).mp hi'
    rwa [this] at hadj

/-- **The atomic layer of composition.** The diagram of the union is
determined by the diagrams of the two sides together with the overlap
pattern. -/
theorem atomic_union_congr (g₁ : Glue G₁ X₁ Y₁ m₁ σ τ) (g₂ : Glue G₂ X₂ Y₂ m₂ σ τ)
    (hpat : ∀ i j, m₁ (σ i) = m₁ (τ j) ↔ m₂ (σ i) = m₂ (τ j))
    (hX : Atomic.of G₁ (m₁ ∘ σ) A₁ = Atomic.of G₂ (m₂ ∘ σ) A₂)
    (hY : Atomic.of G₁ (m₁ ∘ τ) A₁ = Atomic.of G₂ (m₂ ∘ τ) A₂) :
    Atomic.of G₁ m₁ A₁ = Atomic.of G₂ m₂ A₂ := by
  have hpat' : ∀ i j, m₂ (σ i) = m₂ (τ j) ↔ m₁ (σ i) = m₁ (τ j) := fun i j => (hpat i j).symm
  refine Atomic.ext (funext fun k => funext fun k' => ?_) (funext fun k => funext fun k' => ?_)
    (funext fun k => funext fun y => ?_)
  · -- adjacency
    refine Bool.eq_iff_iff.mpr ?_
    simp only [Atomic.of_adj]
    obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ := g₁.cover k <;> obtain ⟨i', rfl⟩ | ⟨j', rfl⟩ := g₁.cover k'
    · simpa using adj_iff_of_diagram_eq hX i i'
    · exact ⟨adj_of_cross g₁ hpat hX hY i j',
        adj_of_cross g₂ hpat' hX.symm hY.symm i j'⟩
    · exact ⟨fun h => (adj_of_cross g₁ hpat hX hY i' j h.symm).symm,
        fun h => (adj_of_cross g₂ hpat' hX.symm hY.symm i' j h.symm).symm⟩
    · simpa using adj_iff_of_diagram_eq hY j j'
  · -- equality
    refine Bool.eq_iff_iff.mpr ?_
    simp only [Atomic.of_eq]
    obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ := g₁.cover k <;> obtain ⟨i', rfl⟩ | ⟨j', rfl⟩ := g₁.cover k'
    · simpa using eq_iff_of_diagram_eq hX i i'
    · exact hpat i j'
    · exact ⟨fun h => ((hpat i' j).mp h.symm).symm, fun h => ((hpat' i' j).mp h.symm).symm⟩
    · simpa using eq_iff_of_diagram_eq hY j j'
  · -- membership
    refine Bool.eq_iff_iff.mpr ?_
    simp only [Atomic.of_mem]
    obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ := g₁.cover k
    · simpa using mem_iff_of_diagram_eq hX i y
    · simpa using mem_iff_of_diagram_eq hY j y

/-! ### Lower ranks

The vertex move of the composition splits the rank-`q+1` hypothesis of
*one* side; the other side's hypothesis has to come down a rank on its
own. That the type of rank `q+1` determines the type of rank `q` is the
same induction as everything else here. -/

/-- A type of rank `q+1` determines the type of rank `q`. -/
theorem typ_succ_congr :
    ∀ (q : ℕ) {r s n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
      {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
      {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
      {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
      typ G₁ X₁ (q + 1) m₁ A₁ = typ G₂ X₂ (q + 1) m₂ A₂ →
      typ G₁ X₁ q m₁ A₁ = typ G₂ X₂ q m₂ A₂ := by
  intro q
  induction q with
  | zero =>
      intro r s n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      simpa [typ_zero] using congrArg T.diagram h
  | succ q ih =>
      intro r s n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      have vstep : ∀ {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
          {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
          {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          typ G₁ X₁ (q + 2) m₁ A₁ = typ G₂ X₂ (q + 2) m₂ A₂ →
          ∀ t : T q (r + 1) s, (typ G₁ X₁ (q + 1) m₁ A₁).vMoves t = true →
            (typ G₂ X₂ (q + 1) m₂ A₂).vMoves t = true := by
        intro n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h t ht
        rw [vMoves_typ] at ht ⊢
        obtain ⟨v, hv, hvt⟩ := ht
        have h₁ := vMoves_typ_snoc (G := G₁) (X := X₁) (q := q + 1) (m := m₁) (A := A₁) hv
        rw [h, vMoves_typ] at h₁
        obtain ⟨w, hw, hwt⟩ := h₁
        exact ⟨w, hw, by rw [ih hwt, hvt]⟩
      have sstep : ∀ {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
          {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
          {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          typ G₁ X₁ (q + 2) m₁ A₁ = typ G₂ X₂ (q + 2) m₂ A₂ →
          ∀ t : T q r (s + 1), (typ G₁ X₁ (q + 1) m₁ A₁).sMoves t = true →
            (typ G₂ X₂ (q + 1) m₂ A₂).sMoves t = true := by
        intro n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h t ht
        rw [sMoves_typ] at ht ⊢
        obtain ⟨S, hS, hSt⟩ := ht
        have h₁ := sMoves_typ_snoc (G := G₁) (X := X₁) (q := q + 1) (m := m₁) (A := A₁) hS
        rw [h, sMoves_typ] at h₁
        obtain ⟨S', hS', hS't⟩ := h₁
        exact ⟨S', hS', by rw [ih hS't, hSt]⟩
      refine T.ext ?_ (funext fun t => ?_) (funext fun t => ?_)
      · simpa using congrArg T.diagram h
      · exact Bool.eq_iff_iff.mpr ⟨vstep h t, vstep h.symm t⟩
      · exact Bool.eq_iff_iff.mpr ⟨sstep h t, sstep h.symm t⟩

/-! ### Extending the pool

The two bookkeeping lemmas of the vertex move. Marking one more vertex
`v ∈ X` appends `v` to the pool; `X`'s index map becomes `liftLast σ`
and `Y`'s becomes `Fin.castSucc ∘ τ`, so that both sides' mark tuples
come out as `Fin.snoc (m ∘ σ) v` and `m ∘ τ` — no re-indexing lemma is
needed beyond the two below and `snoc_comp_liftLast` from the mark
lemmas. The gluing hypotheses survive verbatim; the *overlap pattern*
does not, and `pat_snoc` is where it is re-established. -/

@[simp] theorem snoc_liftLast_apply {v : Fin n} (i : Fin (a + 1)) :
    (Fin.snoc m v : Fin (c + 1) → Fin n) (liftLast σ i)
      = (Fin.snoc (m ∘ σ) v : Fin (a + 1) → Fin n) i :=
  congrFun (snoc_comp_liftLast m v σ) i

@[simp] theorem snoc_castSucc_apply {v : Fin n} (j : Fin b) :
    (Fin.snoc m v : Fin (c + 1) → Fin n) ((Fin.castSucc ∘ τ) j) = m (τ j) := by
  simp

/-- Marking one more vertex of `X`: the gluing hypotheses survive. -/
theorem Glue.snocX (h : Glue G X Y m σ τ) {v : Fin n} (hv : v ∈ X) :
    Glue G X Y (Fin.snoc m v) (liftLast σ) (Fin.castSucc ∘ τ) where
  markX i := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hv
    · simpa using h.markX i
  markY j := by simpa using h.markY j
  cover k := by
    refine Fin.lastCases ?_ (fun k => ?_) k
    · exact Or.inl ⟨Fin.last _, by simp [liftLast]⟩
    · rcases h.cover k with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · exact Or.inl ⟨i.castSucc, by simp [liftLast]⟩
      · exact Or.inr ⟨j, rfl⟩
  interX u hu hu' := by
    obtain ⟨i, hi⟩ := h.interX u hu hu'
    exact ⟨i.castSucc, by simpa using hi⟩
  interY u hu hu' := by
    obtain ⟨j, hj⟩ := h.interY u hu hu'
    exact ⟨j, by simpa using hj⟩
  sep := h.sep

/-- **The new mark's overlap pattern.** After marking `v ∈ X₁` and its
counterpart `w ∈ X₂`, the extended mark tuples still have the same
overlap pattern. The new position is the only thing to check: `v` is a
mark of `Y₁` exactly when `w` is a mark of `Y₂`, because a vertex of the
overlap is marked on both sides (so `v` is *also* an `X₁`-mark) and the
transferred type's diagram says which `X`-mark it is. -/
theorem pat_snoc (g₁ : Glue G₁ X₁ Y₁ m₁ σ τ) (g₂ : Glue G₂ X₂ Y₂ m₂ σ τ)
    (hpat : ∀ i j, m₁ (σ i) = m₁ (τ j) ↔ m₂ (σ i) = m₂ (τ j))
    {v : Fin n₁} {w : Fin n₂} (hv : v ∈ X₁) (hw : w ∈ X₂)
    (hd : ∀ i, v = m₁ (σ i) ↔ w = m₂ (σ i)) (i : Fin (a + 1)) (j : Fin b) :
    (Fin.snoc m₁ v : Fin (c + 1) → Fin n₁) (liftLast σ i)
        = (Fin.snoc m₁ v : Fin (c + 1) → Fin n₁) ((Fin.castSucc ∘ τ) j) ↔
      (Fin.snoc m₂ w : Fin (c + 1) → Fin n₂) (liftLast σ i)
        = (Fin.snoc m₂ w : Fin (c + 1) → Fin n₂) ((Fin.castSucc ∘ τ) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [snoc_liftLast_apply, snoc_castSucc_apply, Fin.snoc_last]
    constructor
    · intro h
      obtain ⟨i, hi⟩ := g₁.interX v hv (h ▸ g₁.markY j)
      have := (hpat i j).mp (hi.trans h)
      rw [← this, ← (hd i).mp hi.symm]
    · intro h
      obtain ⟨i, hi⟩ := g₂.interX w hw (h ▸ g₂.markY j)
      have := (hpat i j).mpr (hi.trans h)
      rw [← this, (hd i).mpr hi.symm]
  · simp only [snoc_liftLast_apply, Function.comp_apply, Fin.snoc_castSucc]
    exact hpat i j

/-- The two set witnesses on the second side agree on the overlap: a
vertex of `X₂ ∩ Y₂` is marked on both sides, and the two diagrams record
its membership against the *same* set on the first side. -/
theorem set_witness_agree (g₂ : Glue G₂ X₂ Y₂ m₂ σ τ)
    (hpat : ∀ i j, m₁ (σ i) = m₁ (τ j) ↔ m₂ (σ i) = m₂ (τ j))
    {S : Set (Fin n₁)} {SX SY : Set (Fin n₂)}
    (hdX : ∀ i, m₂ (σ i) ∈ SX ↔ m₁ (σ i) ∈ S)
    (hdY : ∀ j, m₂ (τ j) ∈ SY ↔ m₁ (τ j) ∈ S)
    {z : Fin n₂} (hzX : z ∈ X₂) (hzY : z ∈ Y₂) : z ∈ SX ↔ z ∈ SY := by
  obtain ⟨i, hi⟩ := g₂.interX z hzX hzY
  obtain ⟨j, hj⟩ := g₂.interY z hzX hzY
  have hij : m₁ (σ i) = m₁ (τ j) := (hpat i j).mpr (hi.trans hj.symm)
  calc z ∈ SX ↔ m₂ (σ i) ∈ SX := by rw [hi]
    _ ↔ m₁ (σ i) ∈ S := hdX i
    _ ↔ m₁ (τ j) ∈ S := by rw [hij]
    _ ↔ m₂ (τ j) ∈ SY := (hdY j).symm
    _ ↔ z ∈ SY := by rw [hj]

/-- The overlap pattern read from the other side. -/
theorem pat_symm (hpat : ∀ i j, m₁ (σ i) = m₁ (τ j) ↔ m₂ (σ i) = m₂ (τ j)) :
    ∀ j i, m₁ (τ j) = m₁ (σ i) ↔ m₂ (τ j) = m₂ (σ i) :=
  fun j i => eq_comm.trans ((hpat i j).trans eq_comm)

/-! ### Composition -/

/-- **Composition, the cross-ambient congruence** (plan C3.3, rev 4).
Two regions of one graph that overlap only in marked vertices and have
no edges between their private parts have a union whose `q`-type is
determined by their two `q`-types and the overlap pattern — and the
determination does not depend on the ambient graph, so two regions of
*another* graph with the same pair of types have a union of the same
type. This is the theorem that lets a tree decomposition be folded: the
table entry for a pair of types exists because the union's type does not
depend on which structures realized them.

The induction is on the rank, with `c`, `a`, `b` and `s` moving. A
vertex move on the union is a vertex move of one side (with the other
side's hypothesis dropped a rank by `typ_succ_congr`); a set move
`S ⊆ X ∪ Y` is the pair of moves `S ∩ X` and `S ∩ Y`, and the two
witnesses obtained on the other side are glued back by their union,
which is legitimate because they agree on the overlap. -/
theorem typ_union_congr :
    ∀ (q : ℕ) {c a b s n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
      {X₁ Y₁ : Set (Fin n₁)} {X₂ Y₂ : Set (Fin n₂)}
      {m₁ : Fin c → Fin n₁} {m₂ : Fin c → Fin n₂}
      {σ : Fin a → Fin c} {τ : Fin b → Fin c}
      {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
      Glue G₁ X₁ Y₁ m₁ σ τ → Glue G₂ X₂ Y₂ m₂ σ τ →
      (∀ i j, m₁ (σ i) = m₁ (τ j) ↔ m₂ (σ i) = m₂ (τ j)) →
      typ G₁ X₁ q (m₁ ∘ σ) A₁ = typ G₂ X₂ q (m₂ ∘ σ) A₂ →
      typ G₁ Y₁ q (m₁ ∘ τ) A₁ = typ G₂ Y₂ q (m₂ ∘ τ) A₂ →
      typ G₁ (X₁ ∪ Y₁) q m₁ A₁ = typ G₂ (X₂ ∪ Y₂) q m₂ A₂ := by
  intro q
  induction q with
  | zero =>
      intro c a b s n₁ n₂ G₁ G₂ X₁ Y₁ X₂ Y₂ m₁ m₂ σ τ A₁ A₂ g₁ g₂ hpat hX hY
      exact atomic_union_congr g₁ g₂ hpat hX hY
  | succ q ih =>
      intro c a b s n₁ n₂ G₁ G₂ X₁ Y₁ X₂ Y₂ m₁ m₂ σ τ A₁ A₂ g₁ g₂ hpat hX hY
      -- One vertex move, with the moved vertex on the `X` side: the
      -- transferred witness `w` together with the union's type at rank `q`.
      have vkey : ∀ {c a b s n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)}
          {G₂ : SimpleGraph (Fin n₂)} {X₁ Y₁ : Set (Fin n₁)} {X₂ Y₂ : Set (Fin n₂)}
          {m₁ : Fin c → Fin n₁} {m₂ : Fin c → Fin n₂}
          {σ : Fin a → Fin c} {τ : Fin b → Fin c}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          Glue G₁ X₁ Y₁ m₁ σ τ → Glue G₂ X₂ Y₂ m₂ σ τ →
          (∀ i j, m₁ (σ i) = m₁ (τ j) ↔ m₂ (σ i) = m₂ (τ j)) →
          typ G₁ X₁ (q + 1) (m₁ ∘ σ) A₁ = typ G₂ X₂ (q + 1) (m₂ ∘ σ) A₂ →
          typ G₁ Y₁ (q + 1) (m₁ ∘ τ) A₁ = typ G₂ Y₂ (q + 1) (m₂ ∘ τ) A₂ →
          ∀ v ∈ X₁, ∃ w ∈ X₂,
            typ G₂ (X₂ ∪ Y₂) q (Fin.snoc m₂ w) A₂
              = typ G₁ (X₁ ∪ Y₁) q (Fin.snoc m₁ v) A₁ := by
        intro c a b s n₁ n₂ G₁ G₂ X₁ Y₁ X₂ Y₂ m₁ m₂ σ τ A₁ A₂ g₁ g₂ hpat hX hY v hv
        have h₁ := vMoves_typ_snoc (G := G₁) (X := X₁) (q := q) (m := m₁ ∘ σ) (A := A₁) hv
        rw [hX, vMoves_typ] at h₁
        obtain ⟨w, hw, hwt⟩ := h₁
        refine ⟨w, hw, ?_⟩
        have hd : ∀ i, v = m₁ (σ i) ↔ w = m₂ (σ i) := by
          intro i
          have := eq_iff_of_diagram_eq (by simpa using congrArg T.diagram hwt)
            (Fin.last a) i.castSucc
          simpa using this.symm
        refine (ih (g₁.snocX hv) (g₂.snocX hw) (pat_snoc g₁ g₂ hpat hv hw hd) ?_ ?_).symm
        · rw [snoc_comp_liftLast, snoc_comp_liftLast]
          exact hwt.symm
        · have e₁ : (Fin.snoc m₁ v : Fin (c + 1) → Fin n₁) ∘ (Fin.castSucc ∘ τ) = m₁ ∘ τ := by
            funext j; simp
          have e₂ : (Fin.snoc m₂ w : Fin (c + 1) → Fin n₂) ∘ (Fin.castSucc ∘ τ) = m₂ ∘ τ := by
            funext j; simp
          rw [e₁, e₂]
          exact typ_succ_congr q hY
      -- The vertex-move component, one direction.
      have vstep : ∀ {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
          {X₁ Y₁ : Set (Fin n₁)} {X₂ Y₂ : Set (Fin n₂)}
          {m₁ : Fin c → Fin n₁} {m₂ : Fin c → Fin n₂}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          Glue G₁ X₁ Y₁ m₁ σ τ → Glue G₂ X₂ Y₂ m₂ σ τ →
          (∀ i j, m₁ (σ i) = m₁ (τ j) ↔ m₂ (σ i) = m₂ (τ j)) →
          typ G₁ X₁ (q + 1) (m₁ ∘ σ) A₁ = typ G₂ X₂ (q + 1) (m₂ ∘ σ) A₂ →
          typ G₁ Y₁ (q + 1) (m₁ ∘ τ) A₁ = typ G₂ Y₂ (q + 1) (m₂ ∘ τ) A₂ →
          ∀ t : T q (c + 1) s, (typ G₁ (X₁ ∪ Y₁) (q + 1) m₁ A₁).vMoves t = true →
            (typ G₂ (X₂ ∪ Y₂) (q + 1) m₂ A₂).vMoves t = true := by
        intro n₁ n₂ G₁ G₂ X₁ Y₁ X₂ Y₂ m₁ m₂ A₁ A₂ g₁ g₂ hpat hX hY t ht
        rw [vMoves_typ] at ht ⊢
        obtain ⟨v, hv, hvt⟩ := ht
        rcases hv with hv | hv
        · obtain ⟨w, hw, hwt⟩ := vkey g₁ g₂ hpat hX hY v hv
          exact ⟨w, Or.inl hw, by rw [hwt, hvt]⟩
        · obtain ⟨w, hw, hwt⟩ := vkey g₁.symm g₂.symm (pat_symm hpat) hY hX v hv
          rw [Set.union_comm Y₂ X₂, Set.union_comm Y₁ X₁] at hwt
          exact ⟨w, Or.inr hw, by rw [hwt, hvt]⟩
      -- The set-move component, one direction.
      have sstep : ∀ {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
          {X₁ Y₁ : Set (Fin n₁)} {X₂ Y₂ : Set (Fin n₂)}
          {m₁ : Fin c → Fin n₁} {m₂ : Fin c → Fin n₂}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          Glue G₁ X₁ Y₁ m₁ σ τ → Glue G₂ X₂ Y₂ m₂ σ τ →
          (∀ i j, m₁ (σ i) = m₁ (τ j) ↔ m₂ (σ i) = m₂ (τ j)) →
          typ G₁ X₁ (q + 1) (m₁ ∘ σ) A₁ = typ G₂ X₂ (q + 1) (m₂ ∘ σ) A₂ →
          typ G₁ Y₁ (q + 1) (m₁ ∘ τ) A₁ = typ G₂ Y₂ (q + 1) (m₂ ∘ τ) A₂ →
          ∀ t : T q c (s + 1), (typ G₁ (X₁ ∪ Y₁) (q + 1) m₁ A₁).sMoves t = true →
            (typ G₂ (X₂ ∪ Y₂) (q + 1) m₂ A₂).sMoves t = true := by
        intro n₁ n₂ G₁ G₂ X₁ Y₁ X₂ Y₂ m₁ m₂ A₁ A₂ g₁ g₂ hpat hX hY t ht
        rw [sMoves_typ] at ht ⊢
        obtain ⟨S, hS, hSt⟩ := ht
        -- the two halves of `S`, transferred one side at a time
        have hSX := sMoves_typ_snoc (G := G₁) (X := X₁) (q := q) (m := m₁ ∘ σ) (A := A₁)
          (S := S ∩ X₁) Set.inter_subset_right
        rw [hX, sMoves_typ] at hSX
        obtain ⟨SX, hSXsub, hSXt⟩ := hSX
        have hSY := sMoves_typ_snoc (G := G₁) (X := Y₁) (q := q) (m := m₁ ∘ τ) (A := A₁)
          (S := S ∩ Y₁) Set.inter_subset_right
        rw [hY, sMoves_typ] at hSY
        obtain ⟨SY, hSYsub, hSYt⟩ := hSY
        -- what the two diagrams say about the marks
        have hdX : ∀ i, m₂ (σ i) ∈ SX ↔ m₁ (σ i) ∈ S := by
          intro i
          have := mem_iff_of_diagram_eq (by simpa using congrArg T.diagram hSXt) i (Fin.last s)
          simp only [Function.comp_apply, Fin.snoc_last] at this
          exact this.trans ⟨fun h => h.1, fun h => ⟨h, g₁.markX i⟩⟩
        have hdY : ∀ j, m₂ (τ j) ∈ SY ↔ m₁ (τ j) ∈ S := by
          intro j
          have := mem_iff_of_diagram_eq (by simpa using congrArg T.diagram hSYt) j (Fin.last s)
          simp only [Function.comp_apply, Fin.snoc_last] at this
          exact this.trans ⟨fun h => h.1, fun h => ⟨h, g₁.markY j⟩⟩
        have hagree : ∀ z ∈ X₂, z ∈ Y₂ → (z ∈ SX ↔ z ∈ SY) := fun z hz hz' =>
          set_witness_agree g₂ hpat hdX hdY hz hz'
        -- the witness on the other side, and the two sides' rank-`q` equalities
        have hunionX : (SX ∪ SY) ∩ X₂ = SX ∩ X₂ := by
          refine Set.ext fun z => ⟨fun h => ⟨?_, h.2⟩, fun h => ⟨Or.inl h.1, h.2⟩⟩
          rcases h.1 with h' | h'
          · exact h'
          · exact (hagree z h.2 (hSYsub h')).mpr h'
        have hunionY : (SX ∪ SY) ∩ Y₂ = SY ∩ Y₂ := by
          refine Set.ext fun z => ⟨fun h => ⟨?_, h.2⟩, fun h => ⟨Or.inr h.1, h.2⟩⟩
          rcases h.1 with h' | h'
          · exact (hagree z (hSXsub h') h.2).mp h'
          · exact h'
        have eX : typ G₂ X₂ q (m₂ ∘ σ) (Fin.snoc A₂ (SX ∪ SY))
            = typ G₂ X₂ q (m₂ ∘ σ) (Fin.snoc A₂ SX) := by
          refine typ_congr_inter G₂ X₂ q _ _ _ (fun i => g₂.markX i) fun j => ?_
          refine Fin.lastCases ?_ (fun j => by simp) j
          simpa using hunionX
        have eY : typ G₂ Y₂ q (m₂ ∘ τ) (Fin.snoc A₂ (SX ∪ SY))
            = typ G₂ Y₂ q (m₂ ∘ τ) (Fin.snoc A₂ SY) := by
          refine typ_congr_inter G₂ Y₂ q _ _ _ (fun j => g₂.markY j) fun j => ?_
          refine Fin.lastCases ?_ (fun j => by simp) j
          simpa using hunionY
        have fX : typ G₁ X₁ q (m₁ ∘ σ) (Fin.snoc A₁ S)
            = typ G₁ X₁ q (m₁ ∘ σ) (Fin.snoc A₁ (S ∩ X₁)) := by
          refine typ_congr_inter G₁ X₁ q _ _ _ (fun i => g₁.markX i) fun j => ?_
          refine Fin.lastCases ?_ (fun j => by simp) j
          simp [Set.inter_assoc]
        have fY : typ G₁ Y₁ q (m₁ ∘ τ) (Fin.snoc A₁ S)
            = typ G₁ Y₁ q (m₁ ∘ τ) (Fin.snoc A₁ (S ∩ Y₁)) := by
          refine typ_congr_inter G₁ Y₁ q _ _ _ (fun j => g₁.markY j) fun j => ?_
          refine Fin.lastCases ?_ (fun j => by simp) j
          simp [Set.inter_assoc]
        refine ⟨SX ∪ SY, Set.union_subset_union hSXsub hSYsub, ?_⟩
        rw [← hSt, ← ih g₁ g₂ hpat (by rw [fX, eX]; exact hSXt.symm)
          (by rw [fY, eY]; exact hSYt.symm)]
      refine T.ext ?_ (funext fun t => ?_) (funext fun t => ?_)
      · have hdX : Atomic.of G₁ (m₁ ∘ σ) A₁ = Atomic.of G₂ (m₂ ∘ σ) A₂ := by
          simpa using congrArg T.diagram hX
        have hdY : Atomic.of G₁ (m₁ ∘ τ) A₁ = Atomic.of G₂ (m₂ ∘ τ) A₂ := by
          simpa using congrArg T.diagram hY
        simpa using atomic_union_congr g₁ g₂ hpat hdX hdY
      · exact Bool.eq_iff_iff.mpr ⟨vstep g₁ g₂ hpat hX hY t,
          vstep g₂ g₁ (fun i j => (hpat i j).symm) hX.symm hY.symm t⟩
      · exact Bool.eq_iff_iff.mpr ⟨sstep g₁ g₂ hpat hX hY t,
          sstep g₂ g₁ (fun i j => (hpat i j).symm) hX.symm hY.symm t⟩

/-! ### Concatenated marks

The interface plan C3.3 asks for: the two sides keep their own mark
tuples and the union's marks are their concatenation. It is the pool
form at `c = a + b`, `σ = Fin.castAdd`, `τ = Fin.natAdd`, and it is a
rewrite away. -/

/-- The gluing hypotheses for concatenated marks, stated without
mentioning the pool. -/
theorem Glue.append {mX : Fin a → Fin n} {mY : Fin b → Fin n}
    (markX : ∀ i, mX i ∈ X) (markY : ∀ j, mY j ∈ Y)
    (interX : ∀ v ∈ X, v ∈ Y → ∃ i, mX i = v)
    (interY : ∀ v ∈ X, v ∈ Y → ∃ j, mY j = v)
    (sep : ∀ u ∈ X, ∀ v ∈ Y, G.Adj u v → u ∈ Y ∨ v ∈ X) :
    Glue G X Y (Fin.append mX mY) (Fin.castAdd b) (Fin.natAdd a) where
  markX i := by simpa using markX i
  markY j := by simpa using markY j
  cover k := Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun j => Or.inr ⟨j, rfl⟩) k
  interX v hv hv' := by obtain ⟨i, hi⟩ := interX v hv hv'; exact ⟨i, by simpa using hi⟩
  interY v hv hv' := by obtain ⟨j, hj⟩ := interY v hv hv'; exact ⟨j, by simpa using hj⟩
  sep := sep

variable {mX₁ : Fin a → Fin n₁} {mY₁ : Fin b → Fin n₁}
  {mX₂ : Fin a → Fin n₂} {mY₂ : Fin b → Fin n₂}

/-- **Composition, with concatenated marks.** Plan C3.3's shape: each
side carries its own full mark tuple, the overlap pattern is the
equality relation between the two tuples' positions, and the union is
marked by the concatenation. -/
theorem typ_append_congr (q : ℕ)
    (g₁ : Glue G₁ X₁ Y₁ (Fin.append mX₁ mY₁) (Fin.castAdd b) (Fin.natAdd a))
    (g₂ : Glue G₂ X₂ Y₂ (Fin.append mX₂ mY₂) (Fin.castAdd b) (Fin.natAdd a))
    (hpat : ∀ i j, mX₁ i = mY₁ j ↔ mX₂ i = mY₂ j)
    (hX : typ G₁ X₁ q mX₁ A₁ = typ G₂ X₂ q mX₂ A₂)
    (hY : typ G₁ Y₁ q mY₁ A₁ = typ G₂ Y₂ q mY₂ A₂) :
    typ G₁ (X₁ ∪ Y₁) q (Fin.append mX₁ mY₁) A₁
      = typ G₂ (X₂ ∪ Y₂) q (Fin.append mX₂ mY₂) A₂ := by
  have eX₁ : Fin.append mX₁ mY₁ ∘ Fin.castAdd b = mX₁ := by funext i; simp
  have eY₁ : Fin.append mX₁ mY₁ ∘ Fin.natAdd a = mY₁ := by funext j; simp
  have eX₂ : Fin.append mX₂ mY₂ ∘ Fin.castAdd b = mX₂ := by funext i; simp
  have eY₂ : Fin.append mX₂ mY₂ ∘ Fin.natAdd a = mY₂ := by funext j; simp
  refine typ_union_congr q g₁ g₂ (by simpa using hpat) ?_ ?_
  · rw [eX₁, eX₂]; exact hX
  · rw [eY₁, eY₂]; exact hY

/-! ### The milestone's acceptance, and a non-vacuity check

The two ranks the checkpoint asks for, as instances of the general
theorem. `q = 0` is composition of atomic diagrams; `q = 1` already has
both move components, and is the case in which the whole shape of the
induction is visible. -/

/-- Composition at rank `0`. -/
example (g₁ : Glue G₁ X₁ Y₁ m₁ σ τ) (g₂ : Glue G₂ X₂ Y₂ m₂ σ τ)
    (hpat : ∀ i j, m₁ (σ i) = m₁ (τ j) ↔ m₂ (σ i) = m₂ (τ j))
    (hX : typ G₁ X₁ 0 (m₁ ∘ σ) A₁ = typ G₂ X₂ 0 (m₂ ∘ σ) A₂)
    (hY : typ G₁ Y₁ 0 (m₁ ∘ τ) A₁ = typ G₂ Y₂ 0 (m₂ ∘ τ) A₂) :
    typ G₁ (X₁ ∪ Y₁) 0 m₁ A₁ = typ G₂ (X₂ ∪ Y₂) 0 m₂ A₂ :=
  typ_union_congr 0 g₁ g₂ hpat hX hY

/-- Composition at rank `1`. -/
example (g₁ : Glue G₁ X₁ Y₁ m₁ σ τ) (g₂ : Glue G₂ X₂ Y₂ m₂ σ τ)
    (hpat : ∀ i j, m₁ (σ i) = m₁ (τ j) ↔ m₂ (σ i) = m₂ (τ j))
    (hX : typ G₁ X₁ 1 (m₁ ∘ σ) A₁ = typ G₂ X₂ 1 (m₂ ∘ σ) A₂)
    (hY : typ G₁ Y₁ 1 (m₁ ∘ τ) A₁ = typ G₂ Y₂ 1 (m₂ ∘ τ) A₂) :
    typ G₁ (X₁ ∪ Y₁) 1 m₁ A₁ = typ G₂ (X₂ ∪ Y₂) 1 m₂ A₂ :=
  typ_union_congr 1 g₁ g₂ hpat hX hY

/-- The hypotheses are satisfiable in the intended way, and by the
intended objects: the path `0 — 1 — 2` split at its middle vertex, each
side marked with the single shared vertex `1`. Without a check like this
a congruence with six hypotheses can be vacuously true. -/
example :
    Glue (SimpleGraph.fromRel fun u v : Fin 3 => u.val + 1 = v.val)
      ({0, 1} : Set (Fin 3)) ({1, 2} : Set (Fin 3))
      (Fin.append ![(1 : Fin 3)] ![(1 : Fin 3)]) (Fin.castAdd 1) (Fin.natAdd 1) := by
  refine Glue.append (fun i => ?_) (fun j => ?_) (fun v hv hv' => ⟨0, ?_⟩)
    (fun v hv hv' => ⟨0, ?_⟩) (fun u hu v hv h => ?_)
  · fin_cases i; simp
  · fin_cases j; simp
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hv'
    rcases hv with rfl | rfl <;> rcases hv' with h | h <;> simp_all
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hv'
    rcases hv with rfl | rfl <;> rcases hv' with h | h <;> simp_all
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv ⊢
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> revert h <;> decide

end Lax11Proofs.MsoTypes
