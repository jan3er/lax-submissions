import Lax11Proofs.MsoComposition
import Lax11Proofs.CliqueExpr

/-!
The congruences of the clique-width operations (plan decision C13).

One lemma per operation of a `k`-expression, each saying that the
operation is a *congruence* for `q`-types: applying it to two boundaried
regions of equal type — in two different ambient graphs, as always here —
leaves them of equal type. Together with the type algebra of
`MsoTypes.lean` and adequacy these are everything the main induction of
the next milestone needs; the table itself is then extracted from
`Fintype` and choice, and nothing below constructs a function on types.

Labels are set parameters (plan C12): a `k`-labelled region is an
ambient subset with `r = 0` marks and `s = k` set parameters, so the
outer statements of the four results have no marks at all. Marks do
appear inside every proof — the vertex move of the rank recursion adds
one — which is why each theorem is stated for a general mark tuple and
proved by the same induction on the rank as everything else in this
development.

The four results, in the order the plan lists them:

* `typ_disjUnion` — disjoint union `⊕`, the `c = 0` instance of the
  cross-ambient composition lemma `typ_union_congr`. The empty mark
  pool makes the four mark clauses of `Glue` vacuous and disjointness
  makes the two overlap clauses vacuous, so eleven hypotheses collapse
  to the two that matter: the sides are disjoint, and no edge joins
  them. This is the whole content of the cliquewidth pivot's central
  claim, and it is nine lines.
* `typ_setRemap` — a new set assignment in which each new parameter is
  the union of a chosen subfamily of the old ones. `typ_relabel` (`ρ`)
  and `typ_forgetAll` (the root's set-forget, which is what lets
  adequacy consume the root type of a sentence) are instances.
* `typ_addEdges` — the edge addition `η`, the only cross-*graph* lemma
  here in the strong sense that the two ambients genuinely change. It
  needs no hypothesis beyond equality of types: the new adjacency is
  built from the old adjacency, the equality of marks, and the
  membership of marks in the two label parameters, and all three are
  recorded in the atomic diagram. In particular `i ≠ j` is never
  used — validity carries it for fidelity to the standard definition of
  clique-width, not because the mathematics wants it.
* `typ_singleton` — the base of the main induction: a one-vertex region
  has a type depending only on which label parameters the vertex lies
  in, not on the ambient graph and not on which vertex it is.

One general fact about `typ` had to be proved on the way, and it is the
answer to the plan's open question: **`typ` does not depend on edges
outside the region** (`typ_congr_edges`) is *not* implicit in the M4
development — `Atomic.of` reads `G.Adj (m i) (m j)` for arbitrary marks,
so the statement is false without the hypothesis that the marks lie in
`X`, and with it it is the same cheap rank induction as everything else.
The main induction will need it at every `⊕` node, where the children's
types were computed in the children's graphs but the union's type is
read in the parent's larger graph; `typ_sup_of_avoids` is that instance.

Everything general about `typ` lives in namespace `Lax11Proofs.MsoTypes`
and would belong in `MsoTypes.lean` if that file were not frozen; the two
bridging lemmas to `CliqueExpr` are in its namespace at the end.
-/

namespace Lax11Proofs.MsoTypes

variable {n n₁ n₂ q r s : ℕ}

/-! ### Only the edges inside the region matter

The fact the plan asked us to check for. It is not a consequence of
anything in `MsoTypes.lean`: the diagram of a type records the
adjacencies of the *marks*, which the definition of `typ` does not
require to lie in `X`. Under that hypothesis — which every use site
has — a type is blind to the edges outside `X`, by the usual induction:
a vertex move adds a mark inside `X`, so the hypothesis is preserved,
and a set move does not touch the marks at all. -/

/-- The atomic layer: a diagram whose marks lie in `X` sees only the
edges of `G` inside `X`. -/
theorem Atomic.of_congr_edges {G G' : SimpleGraph (Fin n)} {X : Set (Fin n)}
    (m : Fin r → Fin n) (A : Fin s → Set (Fin n))
    (hE : ∀ u ∈ X, ∀ v ∈ X, (G.Adj u v ↔ G'.Adj u v)) (hm : ∀ i, m i ∈ X) :
    Atomic.of G m A = Atomic.of G' m A := by
  refine Atomic.ext (funext fun a => funext fun b => ?_) rfl rfl
  simp only [Atomic.of, decide_eq_decide]
  exact hE _ (hm a) _ (hm b)

/-- **The type of a region depends only on the edges inside it.** Two
ambient graphs that agree on `X` give `X` — marked inside `X` — the same
type, at every rank. -/
theorem typ_congr_edges :
    ∀ (q : ℕ) {r s n : ℕ} {G G' : SimpleGraph (Fin n)} {X : Set (Fin n)}
      {m : Fin r → Fin n} {A : Fin s → Set (Fin n)},
      (∀ u ∈ X, ∀ v ∈ X, (G.Adj u v ↔ G'.Adj u v)) → (∀ i, m i ∈ X) →
      typ G X q m A = typ G' X q m A := by
  intro q
  induction q with
  | zero =>
      intro r s n G G' X m A hE hm
      exact Atomic.of_congr_edges m A hE hm
  | succ q ih =>
      intro r s n G G' X m A hE hm
      refine T.ext ?_ (funext fun t => ?_) (funext fun t => ?_)
      · simpa using Atomic.of_congr_edges m A hE hm
      · refine Bool.eq_iff_iff.mpr ?_
        simp only [vMoves_typ]
        refine exists_congr fun v => and_congr_right fun hv => ?_
        rw [ih hE (fun i => Fin.lastCases (by simpa using hv)
          (fun i => by simpa using hm i) i)]
      · refine Bool.eq_iff_iff.mpr ?_
        simp only [sMoves_typ]
        refine exists_congr fun S => and_congr_right fun _ => ?_
        rw [ih hE hm]

/-- The instance the `⊕` case of the main induction needs: adding edges
that avoid `X` does not change the type of `X`. -/
theorem typ_sup_of_avoids {G H : SimpleGraph (Fin n)} {X : Set (Fin n)}
    {m : Fin r → Fin n} {A : Fin s → Set (Fin n)}
    (hH : ∀ u ∈ X, ∀ v ∈ X, ¬ H.Adj u v) (hm : ∀ i, m i ∈ X) :
    typ (G ⊔ H) X q m A = typ G X q m A :=
  typ_congr_edges q (fun u hu v hv => by
    simp only [SimpleGraph.sup_adj, or_iff_left (hH u hu v hv)]) hm

/-! ### Disjoint union

The composition lemma at the empty mark pool. `Glue` has six clauses;
with `c = a = b = 0` the four that speak about marks hold vacuously, the
two overlap clauses hold vacuously because the regions are disjoint, and
only the separation clause carries content. The overlap pattern is a
statement about `Fin 0 × Fin 0`, so it too is vacuous. -/

/-- **Disjoint union.** Two disjoint regions with no edges between them
have a union whose `q`-type is determined by their two `q`-types, across
ambients. This is the binary composition the clique-width fold uses, and
it is the `c = 0` instance of `typ_union_congr`. -/
theorem typ_disjUnion (q : ℕ) {s n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)}
    {G₂ : SimpleGraph (Fin n₂)} {X₁ Y₁ : Set (Fin n₁)} {X₂ Y₂ : Set (Fin n₂)}
    {m₁ : Fin 0 → Fin n₁} {m₂ : Fin 0 → Fin n₂}
    {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)}
    (d₁ : Disjoint X₁ Y₁) (d₂ : Disjoint X₂ Y₂)
    (sep₁ : ∀ u ∈ X₁, ∀ v ∈ Y₁, G₁.Adj u v → u ∈ Y₁ ∨ v ∈ X₁)
    (sep₂ : ∀ u ∈ X₂, ∀ v ∈ Y₂, G₂.Adj u v → u ∈ Y₂ ∨ v ∈ X₂)
    (hX : typ G₁ X₁ q m₁ A₁ = typ G₂ X₂ q m₂ A₂)
    (hY : typ G₁ Y₁ q m₁ A₁ = typ G₂ Y₂ q m₂ A₂) :
    typ G₁ (X₁ ∪ Y₁) q m₁ A₁ = typ G₂ (X₂ ∪ Y₂) q m₂ A₂ := by
  have g₁ : Glue G₁ X₁ Y₁ m₁ (id : Fin 0 → Fin 0) id :=
    { markX := fun i => i.elim0, markY := fun j => j.elim0, cover := fun k => k.elim0
      interX := fun v hv hv' => absurd hv' (Set.disjoint_left.mp d₁ hv)
      interY := fun v hv hv' => absurd hv' (Set.disjoint_left.mp d₁ hv)
      sep := sep₁ }
  have g₂ : Glue G₂ X₂ Y₂ m₂ (id : Fin 0 → Fin 0) id :=
    { markX := fun i => i.elim0, markY := fun j => j.elim0, cover := fun k => k.elim0
      interX := fun v hv hv' => absurd hv' (Set.disjoint_left.mp d₂ hv)
      interY := fun v hv hv' => absurd hv' (Set.disjoint_left.mp d₂ hv)
      sep := sep₂ }
  exact typ_union_congr q g₁ g₂ (fun i _ => i.elim0) hX hY

/-! ### Remapping the set parameters

The unary move on the *set* side: the new `j`-th parameter is the union
of the old parameters named by `f j`. The rank-`0` case is the
observation that membership in such a union is a disjunction of the
membership atoms the diagram already records; the rank step is the same
bookkeeping as the mark lemma's, with `liftLastF` playing the role of
`liftLast` — the set a quantifier has just bound is named by the new last
index and by nothing else. -/

/-- The set assignment obtained by naming, for each new index `j`, the
union of the old parameters in `f j`. -/
def setRemap {n s s' : ℕ} (f : Fin s' → Finset (Fin s)) (A : Fin s → Set (Fin n)) :
    Fin s' → Set (Fin n) := fun j => ⋃ i ∈ f j, A i

/-- `f` extended to keep the set a quantifier has just bound: old indices
name the old sets, the new last index names the new set alone. -/
def liftLastF {s s' : ℕ} (f : Fin s' → Finset (Fin s)) :
    Fin (s' + 1) → Finset (Fin (s + 1)) :=
  Fin.snoc (fun j => (f j).image Fin.castSucc) {Fin.last s}

@[simp] theorem setRemap_apply {n s s' : ℕ} (f : Fin s' → Finset (Fin s))
    (A : Fin s → Set (Fin n)) (j : Fin s') : setRemap f A j = ⋃ i ∈ f j, A i := rfl

/-- Extending an assignment and then remapping is remapping and then
extending — the set-side counterpart of `snoc_comp_liftLast`. -/
theorem setRemap_snoc {n s s' : ℕ} (f : Fin s' → Finset (Fin s))
    (A : Fin s → Set (Fin n)) (S : Set (Fin n)) :
    setRemap (liftLastF f) (Fin.snoc A S) = Fin.snoc (setRemap f A) S := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [setRemap, liftLastF]
  · simp only [liftLastF, Fin.snoc_castSucc, setRemap]
    ext x
    simp only [Set.mem_iUnion, Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨i, ⟨a, ha, rfl⟩, hx⟩
      exact ⟨a, ha, by simpa using hx⟩
    · rintro ⟨a, ha, hx⟩
      exact ⟨a.castSucc, ⟨a, ha, rfl⟩, by simpa using hx⟩

/-- The atomic layer of the set remap: membership in a union of
parameters is a disjunction of membership atoms. -/
theorem Atomic.of_setRemap {s' : ℕ} (f : Fin s' → Finset (Fin s))
    {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
    {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)}
    (h : Atomic.of G₁ m₁ A₁ = Atomic.of G₂ m₂ A₂) :
    Atomic.of G₁ m₁ (setRemap f A₁) = Atomic.of G₂ m₂ (setRemap f A₂) := by
  refine Atomic.ext (funext fun a => funext fun b => ?_) (funext fun a => funext fun b => ?_)
    (funext fun a => funext fun j => ?_)
  · simpa [Atomic.of] using adj_iff_of_diagram_eq h a b
  · simpa [Atomic.of] using eq_iff_of_diagram_eq h a b
  · simp only [Atomic.of, setRemap, decide_eq_decide, Set.mem_iUnion, exists_prop]
    exact exists_congr fun i => and_congr_right fun _ => mem_iff_of_diagram_eq h a i

/-- **Remapping the set parameters.** Replacing the assignment by one in
which each parameter is a union of old parameters is a congruence for
types. Relabelling and the root's set-forget are instances. -/
theorem typ_setRemap :
    ∀ (q : ℕ) {r s s' n₁ n₂ : ℕ} (f : Fin s' → Finset (Fin s))
      {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
      {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
      {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
      {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
      typ G₁ X₁ q m₁ A₁ = typ G₂ X₂ q m₂ A₂ →
      typ G₁ X₁ q m₁ (setRemap f A₁) = typ G₂ X₂ q m₂ (setRemap f A₂) := by
  intro q
  induction q with
  | zero =>
      intro r s s' n₁ n₂ f G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      exact Atomic.of_setRemap f h
  | succ q ih =>
      intro r s s' n₁ n₂ f G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      have vstep : ∀ {r n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
          {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
          {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          typ G₁ X₁ (q + 1) m₁ A₁ = typ G₂ X₂ (q + 1) m₂ A₂ →
          ∀ t : T q (r + 1) s', (typ G₁ X₁ (q + 1) m₁ (setRemap f A₁)).vMoves t = true →
            (typ G₂ X₂ (q + 1) m₂ (setRemap f A₂)).vMoves t = true := by
        intro r n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h t ht
        rw [vMoves_typ] at ht ⊢
        obtain ⟨v, hv, hvt⟩ := ht
        have h₁ := vMoves_typ_snoc (G := G₁) (X := X₁) (q := q) (m := m₁) (A := A₁) hv
        rw [h, vMoves_typ] at h₁
        obtain ⟨w, hw, hwt⟩ := h₁
        exact ⟨w, hw, by rw [ih f hwt, hvt]⟩
      have sstep : ∀ {r n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
          {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
          {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          typ G₁ X₁ (q + 1) m₁ A₁ = typ G₂ X₂ (q + 1) m₂ A₂ →
          ∀ t : T q r (s' + 1), (typ G₁ X₁ (q + 1) m₁ (setRemap f A₁)).sMoves t = true →
            (typ G₂ X₂ (q + 1) m₂ (setRemap f A₂)).sMoves t = true := by
        intro r n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h t ht
        rw [sMoves_typ] at ht ⊢
        obtain ⟨S, hS, hSt⟩ := ht
        have h₁ := sMoves_typ_snoc (G := G₁) (X := X₁) (q := q) (m := m₁) (A := A₁) hS
        rw [h, sMoves_typ] at h₁
        obtain ⟨S', hS', hS't⟩ := h₁
        refine ⟨S', hS', ?_⟩
        have key := ih (liftLastF f) hS't
        rw [setRemap_snoc, setRemap_snoc] at key
        rw [key, hSt]
      refine T.ext ?_ (funext fun t => ?_) (funext fun t => ?_)
      · have hd : Atomic.of G₁ m₁ A₁ = Atomic.of G₂ m₂ A₂ := by
          simpa using congrArg T.diagram h
        simpa using Atomic.of_setRemap f hd
      · exact Bool.eq_iff_iff.mpr ⟨vstep h t, vstep h.symm t⟩
      · exact Bool.eq_iff_iff.mpr ⟨sstep h t, sstep h.symm t⟩

/-! #### The two instances

Relabelling (`ρ i j`: class `i` is poured into class `j` and empties) and
the root's set-forget. -/

/-- The set assignment after `ρ i j`. -/
def relabelSets {n s : ℕ} (A : Fin s → Set (Fin n)) (i j : Fin s) : Fin s → Set (Fin n) :=
  fun t => if t = j then A i ∪ A j else if t = i then ∅ else A t

/-- The family of index sets that realizes `ρ i j` as a set remap. -/
def relabelF {s : ℕ} (i j : Fin s) : Fin s → Finset (Fin s) :=
  fun t => if t = j then {i, j} else if t = i then ∅ else {t}

theorem setRemap_relabelF {n s : ℕ} (A : Fin s → Set (Fin n)) (i j : Fin s) :
    setRemap (relabelF i j) A = relabelSets A i j := by
  funext t
  simp only [setRemap, relabelF, relabelSets]
  split
  · ext x; simp
  · split
    · simp
    · ext x; simp

/-- **Relabelling is a congruence.** The `ρ` instance of
`typ_setRemap`. -/
theorem typ_relabel (q : ℕ) {r s n₁ n₂ : ℕ} (i j : Fin s)
    {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
    {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
    {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)}
    (h : typ G₁ X₁ q m₁ A₁ = typ G₂ X₂ q m₂ A₂) :
    typ G₁ X₁ q m₁ (relabelSets A₁ i j) = typ G₂ X₂ q m₂ (relabelSets A₂ i j) := by
  rw [← setRemap_relabelF, ← setRemap_relabelF]
  exact typ_setRemap q (relabelF i j) h

/-- **Forgetting every set parameter is a congruence.** The `s' = 0`
instance; this is what lets adequacy consume the root type of a
*sentence*, whose set parameters are the label classes. -/
theorem typ_forgetAll (q : ℕ) {r s n₁ n₂ : ℕ}
    {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
    {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
    {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)}
    (B₁ : Fin 0 → Set (Fin n₁)) (B₂ : Fin 0 → Set (Fin n₂))
    (h : typ G₁ X₁ q m₁ A₁ = typ G₂ X₂ q m₂ A₂) :
    typ G₁ X₁ q m₁ B₁ = typ G₂ X₂ q m₂ B₂ := by
  have := typ_setRemap q (Fin.elim0 : Fin 0 → Finset (Fin s)) h
  rwa [Subsingleton.elim (setRemap (Fin.elim0 : Fin 0 → Finset (Fin s)) A₁) B₁,
    Subsingleton.elim (setRemap (Fin.elim0 : Fin 0 → Finset (Fin s)) A₂) B₂] at this

/-! ### Adding edges

The `η` operation: join every vertex of the parameter `A i` to every
vertex of the parameter `A j`. This is the only one of the four in which
the ambient graph genuinely changes, and the only one the plan expected
to have content — the content is entirely at rank `0`, where the new
adjacency of two marks is built from three atoms the diagram already
records: their old adjacency, their equality, and their membership in
the two parameters. Above rank `0` there is nothing but the usual
recursion, with the two parameter indices carried along as
`Fin.castSucc` images when a set move extends the assignment.

Note what is *not* assumed: `i ≠ j`. The standard definition of
clique-width restricts `η` to distinct labels and `CliqueExpr.Valid`
records that, but the congruence holds either way. -/

/-- The graph obtained by joining the parameter `A i` to the parameter
`A j`. -/
def addEdgesG {n s : ℕ} (G : SimpleGraph (Fin n)) (A : Fin s → Set (Fin n)) (i j : Fin s) :
    SimpleGraph (Fin n) :=
  G ⊔ SimpleGraph.fromRel fun u v => u ∈ A i ∧ v ∈ A j

@[simp] theorem addEdgesG_adj {n s : ℕ} {G : SimpleGraph (Fin n)} {A : Fin s → Set (Fin n)}
    {i j : Fin s} {u v : Fin n} :
    (addEdgesG G A i j).Adj u v ↔
      G.Adj u v ∨ (u ≠ v ∧ ((u ∈ A i ∧ v ∈ A j) ∨ (v ∈ A i ∧ u ∈ A j))) := by
  simp [addEdgesG]

/-- Extending the assignment leaves the joined graph alone, provided the
two parameter indices are read through `Fin.castSucc`. -/
@[simp] theorem addEdgesG_snoc {n s : ℕ} (G : SimpleGraph (Fin n)) (A : Fin s → Set (Fin n))
    (S : Set (Fin n)) (i j : Fin s) :
    addEdgesG G (Fin.snoc A S) i.castSucc j.castSucc = addEdgesG G A i j := by
  simp [addEdgesG]

/-- The atomic layer of `η`: the new diagram is a function of the old
one. -/
theorem Atomic.of_addEdges (i j : Fin s)
    {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
    {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)}
    (h : Atomic.of G₁ m₁ A₁ = Atomic.of G₂ m₂ A₂) :
    Atomic.of (addEdgesG G₁ A₁ i j) m₁ A₁ = Atomic.of (addEdgesG G₂ A₂ i j) m₂ A₂ := by
  refine Atomic.ext (funext fun a => funext fun b => ?_) (funext fun a => funext fun b => ?_)
    (funext fun a => funext fun t => ?_)
  · simp only [Atomic.of, decide_eq_decide, addEdgesG_adj]
    have hadj := adj_iff_of_diagram_eq h a b
    have heq := eq_iff_of_diagram_eq h a b
    have hi := mem_iff_of_diagram_eq h a i
    have hi' := mem_iff_of_diagram_eq h b i
    have hj := mem_iff_of_diagram_eq h a j
    have hj' := mem_iff_of_diagram_eq h b j
    rw [hadj, hi, hi', hj, hj', ne_eq, ne_eq, heq]
  · simpa [Atomic.of] using eq_iff_of_diagram_eq h a b
  · simpa [Atomic.of] using mem_iff_of_diagram_eq h a t

/-- **Adding edges is a congruence.** Two regions of equal type, each
with the join of its own two label parameters added to its own ambient
graph, still have equal types. No hypothesis beyond the equality of the
types: the new adjacency is a Boolean function of atoms the diagram
already carries. -/
theorem typ_addEdges :
    ∀ (q : ℕ) {r s n₁ n₂ : ℕ} (i j : Fin s)
      {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
      {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
      {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
      {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
      typ G₁ X₁ q m₁ A₁ = typ G₂ X₂ q m₂ A₂ →
      typ (addEdgesG G₁ A₁ i j) X₁ q m₁ A₁ = typ (addEdgesG G₂ A₂ i j) X₂ q m₂ A₂ := by
  intro q
  induction q with
  | zero =>
      intro r s n₁ n₂ i j G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      exact Atomic.of_addEdges i j h
  | succ q ih =>
      intro r s n₁ n₂ i j G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      have vstep : ∀ {r n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
          {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
          {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          typ G₁ X₁ (q + 1) m₁ A₁ = typ G₂ X₂ (q + 1) m₂ A₂ →
          ∀ t : T q (r + 1) s,
            (typ (addEdgesG G₁ A₁ i j) X₁ (q + 1) m₁ A₁).vMoves t = true →
            (typ (addEdgesG G₂ A₂ i j) X₂ (q + 1) m₂ A₂).vMoves t = true := by
        intro r n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h t ht
        rw [vMoves_typ] at ht ⊢
        obtain ⟨v, hv, hvt⟩ := ht
        have h₁ := vMoves_typ_snoc (G := G₁) (X := X₁) (q := q) (m := m₁) (A := A₁) hv
        rw [h, vMoves_typ] at h₁
        obtain ⟨w, hw, hwt⟩ := h₁
        exact ⟨w, hw, by rw [ih i j hwt, hvt]⟩
      have sstep : ∀ {r n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
          {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
          {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          typ G₁ X₁ (q + 1) m₁ A₁ = typ G₂ X₂ (q + 1) m₂ A₂ →
          ∀ t : T q r (s + 1),
            (typ (addEdgesG G₁ A₁ i j) X₁ (q + 1) m₁ A₁).sMoves t = true →
            (typ (addEdgesG G₂ A₂ i j) X₂ (q + 1) m₂ A₂).sMoves t = true := by
        intro r n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h t ht
        rw [sMoves_typ] at ht ⊢
        obtain ⟨S, hS, hSt⟩ := ht
        have h₁ := sMoves_typ_snoc (G := G₁) (X := X₁) (q := q) (m := m₁) (A := A₁) hS
        rw [h, sMoves_typ] at h₁
        obtain ⟨S', hS', hS't⟩ := h₁
        refine ⟨S', hS', ?_⟩
        have key := ih i.castSucc j.castSucc hS't
        rw [addEdgesG_snoc, addEdgesG_snoc] at key
        rw [key, hSt]
      refine T.ext ?_ (funext fun t => ?_) (funext fun t => ?_)
      · have hd : Atomic.of G₁ m₁ A₁ = Atomic.of G₂ m₂ A₂ := by
          simpa using congrArg T.diagram h
        simpa using Atomic.of_addEdges i j hd
      · exact Bool.eq_iff_iff.mpr ⟨vstep h t, vstep h.symm t⟩
      · exact Bool.eq_iff_iff.mpr ⟨sstep h t, sstep h.symm t⟩

/-! ### A single vertex

The base of the main induction. A one-vertex region has only one vertex
move, which duplicates the single vertex, and only two set moves, `∅`
and the vertex itself, so its type is determined by the label pattern of
the vertex — which parameters it lies in. The ambient graph never enters:
the only adjacency the diagram can ask about is the vertex with itself,
and a simple graph is irreflexive.

The statement is proved for a general mark tuple, all of whose entries
are the single vertex, because that is what the vertex move produces. -/

/-- The atomic layer of a one-vertex region: the only adjacency it can
record is the vertex with itself, which a simple graph never has, and the
only equality is the vertex with itself, which always holds. -/
theorem Atomic.of_singleton {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {v₁ : Fin n₁} {v₂ : Fin n₂} {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
    {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)}
    (hm₁ : ∀ a, m₁ a = v₁) (hm₂ : ∀ a, m₂ a = v₂)
    (hA : ∀ t, v₁ ∈ A₁ t ↔ v₂ ∈ A₂ t) :
    Atomic.of G₁ m₁ A₁ = Atomic.of G₂ m₂ A₂ := by
  refine Atomic.ext (funext fun a => funext fun b => ?_)
    (funext fun a => funext fun b => ?_) (funext fun a => funext fun t => ?_)
  · simp [Atomic.of, hm₁, hm₂]
  · simp [Atomic.of, hm₁, hm₂]
  · simp [Atomic.of, hm₁, hm₂, hA t]

/-- **A one-vertex region.** Its type depends only on which set
parameters the vertex belongs to: not on the ambient graph, and not on
which vertex it is. -/
theorem typ_singleton :
    ∀ (q : ℕ) {r s n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
      {v₁ : Fin n₁} {v₂ : Fin n₂}
      {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
      {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
      (∀ a, m₁ a = v₁) → (∀ a, m₂ a = v₂) → (∀ t, v₁ ∈ A₁ t ↔ v₂ ∈ A₂ t) →
      typ G₁ {v₁} q m₁ A₁ = typ G₂ {v₂} q m₂ A₂ := by
  intro q
  induction q with
  | zero =>
      intro r s n₁ n₂ G₁ G₂ v₁ v₂ m₁ m₂ A₁ A₂ hm₁ hm₂ hA
      exact Atomic.of_singleton hm₁ hm₂ hA
  | succ q ih =>
      intro r s n₁ n₂ G₁ G₂ v₁ v₂ m₁ m₂ A₁ A₂ hm₁ hm₂ hA
      have hs₁ : ∀ a : Fin (r + 1), (Fin.snoc m₁ v₁ : Fin (r + 1) → Fin n₁) a = v₁ := by
        intro a; refine Fin.lastCases ?_ (fun i => ?_) a <;> simp [hm₁]
      have hs₂ : ∀ a : Fin (r + 1), (Fin.snoc m₂ v₂ : Fin (r + 1) → Fin n₂) a = v₂ := by
        intro a; refine Fin.lastCases ?_ (fun i => ?_) a <;> simp [hm₂]
      -- one direction of the set move; the other is the same with the sides exchanged
      have sstep : ∀ {r s n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
          {v₁ : Fin n₁} {v₂ : Fin n₂}
          {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          (∀ a, m₁ a = v₁) → (∀ a, m₂ a = v₂) → (∀ t, v₁ ∈ A₁ t ↔ v₂ ∈ A₂ t) →
          ∀ t : T q r (s + 1), (typ G₁ {v₁} (q + 1) m₁ A₁).sMoves t = true →
            (typ G₂ {v₂} (q + 1) m₂ A₂).sMoves t = true := by
        intro r s n₁ n₂ G₁ G₂ v₁ v₂ m₁ m₂ A₁ A₂ hm₁ hm₂ hA t ht
        classical
        rw [sMoves_typ] at ht ⊢
        obtain ⟨S, hS, hSt⟩ := ht
        refine ⟨if v₁ ∈ S then {v₂} else ∅, ?_, ?_⟩
        · split <;> simp
        · rw [← hSt]
          refine ih hm₂ hm₁ fun u => ?_
          refine Fin.lastCases ?_ (fun u => ?_) u
          · simp only [Fin.snoc_last]
            by_cases hv : v₁ ∈ S <;> simp [hv]
          · simpa using (hA u).symm
      refine T.ext ?_ (funext fun t => ?_) (funext fun t => ?_)
      · simpa using Atomic.of_singleton hm₁ hm₂ hA
      · refine Bool.eq_iff_iff.mpr ?_
        simp only [vMoves_typ, Set.mem_singleton_iff, exists_eq_left]
        rw [ih hs₁ hs₂ hA]
      · exact Bool.eq_iff_iff.mpr
          ⟨sstep hm₁ hm₂ hA t, sstep hm₂ hm₁ (fun t => (hA t).symm) t⟩

end Lax11Proofs.MsoTypes

/-! ### The bridge to `k`-expressions

Two lemmas connecting the evaluator of `CliqueExpr.lean` to the shapes
above: the `Finset` disjointness of the two sides of a `⊕`, restated
over the `Set` coercion the composition lemma wants, and the fact that
the evaluated graph of an `η` node is `addEdgesG` applied to the label
classes read as set parameters. Session 12's decision stands: these are
*added* lemmas, the definitions are untouched. -/

namespace Lax11Proofs.CliqueExpr

open Lax11Proofs.MsoTypes

variable {n k : ℕ}

/-- `Valid.disjoint` over the `Set` coercion — the form `typ_disjUnion`
consumes. -/
theorem Valid.disjoint_coe {e₁ e₂ : Expr n k} (h : Valid (.union e₁ e₂)) :
    Disjoint (verts e₁ : Set (Fin n)) (verts e₂ : Set (Fin n)) :=
  Finset.disjoint_coe.mpr (Valid.disjoint h)

/-- The evaluated graph of an `η` node is the join of the two label
classes, read as set parameters — the form `typ_addEdges` consumes. -/
theorem graph_addEdges_eq (i j : Fin k) (e : Expr n k) :
    graph (.addEdges i j e) = addEdgesG (graph e) (fun t => (cls e t : Set (Fin n))) i j := rfl

/-- A child of a `⊕` may have its type read in its *own* graph: the other
side contributes no edge inside this one. The instance of
`typ_congr_edges` that the main induction needs at every `⊕` node, where
the children's types were computed before the parent's graph existed. -/
theorem typ_graph_union_left {q r s : ℕ} {e₁ e₂ : Expr n k} (h : Valid (.union e₁ e₂))
    {m : Fin r → Fin n} {A : Fin s → Set (Fin n)}
    (hm : ∀ i, m i ∈ (verts e₁ : Set (Fin n))) :
    typ (graph (.union e₁ e₂)) (verts e₁ : Set (Fin n)) q m A
      = typ (graph e₁) (verts e₁ : Set (Fin n)) q m A := by
  refine typ_sup_of_avoids (fun u hu v _ huv => ?_) hm
  exact Set.disjoint_left.mp (Valid.disjoint_coe h) hu (by simpa using (mem_verts_of_adj e₂ huv).1)

/-- The same on the right. -/
theorem typ_graph_union_right {q r s : ℕ} {e₁ e₂ : Expr n k} (h : Valid (.union e₁ e₂))
    {m : Fin r → Fin n} {A : Fin s → Set (Fin n)}
    (hm : ∀ i, m i ∈ (verts e₂ : Set (Fin n))) :
    typ (graph (.union e₁ e₂)) (verts e₂ : Set (Fin n)) q m A
      = typ (graph e₂) (verts e₂ : Set (Fin n)) q m A := by
  rw [graph_union, sup_comm]
  refine typ_sup_of_avoids (fun u hu v _ huv => ?_) hm
  exact Set.disjoint_right.mp (Valid.disjoint_coe h) hu (by simpa using (mem_verts_of_adj e₁ huv).1)

/-- The label classes of a `ρ i j` node are the relabelled parameters —
the form `typ_relabel` consumes. -/
theorem cls_relabel_eq (i j : Fin k) (e : Expr n k) :
    (fun t => (cls (.relabel i j e) t : Set (Fin n)))
      = relabelSets (fun t => (cls e t : Set (Fin n))) i j := by
  funext t
  simp only [cls_relabel, relabelSets]
  split
  · simp
  · split <;> simp

/-- Non-vacuity, on the intended object: the path expression of the smoke
test is valid, and the disjointness hypothesis of `typ_disjUnion` at its
outer `⊕` is then literally `Valid.disjoint_coe`. A congruence with
hypotheses that no expression satisfies would be worthless. -/
example : Disjoint
    ((verts (.addEdges 0 1 (.union (.leaf (0 : Fin 3) (0 : Fin 2))
      (.leaf 1 1))) : Finset (Fin 3)) : Set (Fin 3))
    ((verts (.leaf (2 : Fin 3) (0 : Fin 2)) : Finset (Fin 3)) : Set (Fin 3)) :=
  Valid.disjoint_coe (Valid.of_addEdges (⟨by decide, by decide⟩ : Valid pathExpr))

end Lax11Proofs.CliqueExpr
