import Lax11Proofs.Mso

/-!
Adequacy, and the mark lemmas.

Two theorems, both congruences in the sense of `MsoTypes`' closing
paragraph — no function on types is ever constructed, here or later; the
table is extracted at the end from `Fintype` and choice (plan decision
C5).

*Adequacy* (`satIn_congr`): if two boundaried regions — in two
*different* ambient graphs — have the same `q`-type, then they satisfy
exactly the same formulas of quantifier rank at most `q`. This is the
theorem that makes `T q r s` worth defining: it is a finite type, so a
sentence of rank `q` is decided by a finite amount of information about
a region, and that is the whole content of "MSO model checking is a tree
automaton" without any automaton. The proof is an induction on the
formula in which the rank case does no work at all: a vertex move of the
type is *by definition* a type realized by marking a vertex of the
region, which is exactly the witness an existential quantifier asks for.

*The mark lemmas* (`typ_comp_congr`): the type of a region under
*remapped* marks is determined by its type under the original marks —
for an arbitrary remapping `σ : Fin r' → Fin r` of vertex marks and
`τ : Fin s' → Fin s` of set names, simultaneously. Forgetting a mark
(`σ = Fin.castSucc`), permuting marks (`σ` a bijection), duplicating one
(`σ` non-injective) and reordering set names are all this one lemma at
different `σ`, and so is the re-indexing that the composition lemma's
concatenated mark tuples need (`σ = Fin.castAdd`/`Fin.natAdd`). Proving
them separately would be the same induction three times.

The point of stating both cross-ambient — two graphs `G₁`, `G₂` on
different vertex counts — is that the composition lemma is cross-ambient
(plan C3.3, rev 4), so everything it consumes must be. It costs nothing:
`T q r s` mentions no graph, so the hypothesis `typ G₁ X₁ q m₁ A₁ =
typ G₂ X₂ q m₂ A₂` typechecks as it stands.
-/

namespace Lax11Proofs.MsoTypes

/-! ### Remapping marks

`liftLast σ` is `σ` extended to the position a quantifier binds: old
marks go to old marks, and the new last mark to the new last mark. It is
the only bookkeeping in the file, and `snoc_comp_liftLast` is why the
`Fin.snoc` convention was chosen for both `typ` and `Sat`. -/

/-- A remapping of `r'` marks by `r` marks, extended to keep the mark a
quantifier has just bound. -/
def liftLast {r r' : ℕ} (σ : Fin r' → Fin r) : Fin (r' + 1) → Fin (r + 1) :=
  Fin.snoc (Fin.castSucc ∘ σ) (Fin.last r)

@[simp] theorem liftLast_castSucc {r r' : ℕ} (σ : Fin r' → Fin r) (i : Fin r') :
    liftLast σ i.castSucc = (σ i).castSucc := by
  simp [liftLast]

@[simp] theorem liftLast_last {r r' : ℕ} (σ : Fin r' → Fin r) :
    liftLast σ (Fin.last r') = Fin.last r := by
  simp [liftLast]

/-- Extending a tuple and then remapping is remapping and then
extending. -/
theorem snoc_comp_liftLast {α : Type*} {r r' : ℕ} (f : Fin r → α) (v : α)
    (σ : Fin r' → Fin r) : Fin.snoc f v ∘ liftLast σ = Fin.snoc (f ∘ σ) v := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

/-- The atomic diagram read through a remapping of the marks and the set
names. -/
def Atomic.remap {r s r' s' : ℕ} (σ : Fin r' → Fin r) (τ : Fin s' → Fin s)
    (a : Atomic r s) : Atomic r' s' where
  adj i j := a.adj (σ i) (σ j)
  eq i j := a.eq (σ i) (σ j)
  mem i j := a.mem (σ i) (τ j)

theorem Atomic.of_comp {n r s r' s' : ℕ} (G : SimpleGraph (Fin n)) (m : Fin r → Fin n)
    (A : Fin s → Set (Fin n)) (σ : Fin r' → Fin r) (τ : Fin s' → Fin s) :
    Atomic.of G (m ∘ σ) (A ∘ τ) = (Atomic.of G m A).remap σ τ := rfl

/-! ### The mark lemmas -/

/-- **The mark lemma.** Remapping the marks and the set names of a
region — forgetting, permuting, duplicating, reordering, all at once — is
a congruence for types: regions of equal type keep equal types after any
remapping. The remapping is arbitrary, so every interface the fold needs
is an instance of this one statement; it is proved by the same induction
on the rank that everything about `typ` is proved by. -/
theorem typ_comp_congr :
    ∀ (q : ℕ) {r s r' s' : ℕ} (σ : Fin r' → Fin r) (τ : Fin s' → Fin s)
      {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
      {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
      {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
      {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
      typ G₁ X₁ q m₁ A₁ = typ G₂ X₂ q m₂ A₂ →
      typ G₁ X₁ q (m₁ ∘ σ) (A₁ ∘ τ) = typ G₂ X₂ q (m₂ ∘ σ) (A₂ ∘ τ) := by
  intro q
  induction q with
  | zero =>
      intro r s r' s' σ τ n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      exact congrArg (Atomic.remap σ τ) h
  | succ q ih =>
      intro r s r' s' σ τ n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      -- One direction of each move component; the other is the same with
      -- the two sides exchanged.
      have vstep : ∀ {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
          {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
          {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          typ G₁ X₁ (q + 1) m₁ A₁ = typ G₂ X₂ (q + 1) m₂ A₂ →
          ∀ t : T q (r' + 1) s', (typ G₁ X₁ (q + 1) (m₁ ∘ σ) (A₁ ∘ τ)).vMoves t = true →
            (typ G₂ X₂ (q + 1) (m₂ ∘ σ) (A₂ ∘ τ)).vMoves t = true := by
        intro n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h t ht
        rw [vMoves_typ] at ht ⊢
        obtain ⟨v, hv, hvt⟩ := ht
        have h₁ := vMoves_typ_snoc (G := G₁) (X := X₁) (q := q) (m := m₁) (A := A₁) hv
        rw [h, vMoves_typ] at h₁
        obtain ⟨w, hw, hwt⟩ := h₁
        refine ⟨w, hw, ?_⟩
        have := ih (liftLast σ) τ hwt
        rw [snoc_comp_liftLast, snoc_comp_liftLast] at this
        rw [this, hvt]
      have sstep : ∀ {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
          {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
          {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          typ G₁ X₁ (q + 1) m₁ A₁ = typ G₂ X₂ (q + 1) m₂ A₂ →
          ∀ t : T q r' (s' + 1), (typ G₁ X₁ (q + 1) (m₁ ∘ σ) (A₁ ∘ τ)).sMoves t = true →
            (typ G₂ X₂ (q + 1) (m₂ ∘ σ) (A₂ ∘ τ)).sMoves t = true := by
        intro n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h t ht
        rw [sMoves_typ] at ht ⊢
        obtain ⟨S, hS, hSt⟩ := ht
        have h₁ := sMoves_typ_snoc (G := G₁) (X := X₁) (q := q) (m := m₁) (A := A₁) hS
        rw [h, sMoves_typ] at h₁
        obtain ⟨S', hS', hS't⟩ := h₁
        refine ⟨S', hS', ?_⟩
        have := ih σ (liftLast τ) hS't
        rw [snoc_comp_liftLast, snoc_comp_liftLast] at this
        rw [this, hSt]
      refine T.ext ?_ (funext fun t => ?_) (funext fun t => ?_)
      · have hd : Atomic.of G₁ m₁ A₁ = Atomic.of G₂ m₂ A₂ := by
          simpa using congrArg T.diagram h
        simp only [diagram_typ, Atomic.of_comp, hd]
      · exact Bool.eq_iff_iff.mpr ⟨vstep h t, vstep h.symm t⟩
      · exact Bool.eq_iff_iff.mpr ⟨sstep h t, sstep h.symm t⟩

variable {n₁ n₂ q r s : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
  {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}

/-- Forgetting the last mark is a congruence for types. This is the
`Fin.castSucc` instance of `typ_comp_congr`, and the one the tree fold
uses when a child's private vertices leave the boundary. -/
theorem typ_forgetV_congr {m₁ : Fin (r + 1) → Fin n₁} {m₂ : Fin (r + 1) → Fin n₂}
    {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)}
    (h : typ G₁ X₁ q m₁ A₁ = typ G₂ X₂ q m₂ A₂) :
    typ G₁ X₁ q (m₁ ∘ Fin.castSucc) A₁ = typ G₂ X₂ q (m₂ ∘ Fin.castSucc) A₂ := by
  simpa using typ_comp_congr q Fin.castSucc id h

/-- Forgetting the last set name is a congruence for types. -/
theorem typ_forgetS_congr {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
    {A₁ : Fin (s + 1) → Set (Fin n₁)} {A₂ : Fin (s + 1) → Set (Fin n₂)}
    (h : typ G₁ X₁ q m₁ A₁ = typ G₂ X₂ q m₂ A₂) :
    typ G₁ X₁ q m₁ (A₁ ∘ Fin.castSucc) = typ G₂ X₂ q m₂ (A₂ ∘ Fin.castSucc) := by
  simpa using typ_comp_congr q id Fin.castSucc h

/-- Permuting and duplicating marks are the same lemma: here the two
marks are swapped and then the first is duplicated. -/
example {m₁ : Fin 2 → Fin n₁} {m₂ : Fin 2 → Fin n₂}
    {A₁ : Fin 0 → Set (Fin n₁)} {A₂ : Fin 0 → Set (Fin n₂)}
    (h : typ G₁ X₁ q m₁ A₁ = typ G₂ X₂ q m₂ A₂) :
    typ G₁ X₁ q (m₁ ∘ ![1, 1, 0]) (A₁ ∘ id) = typ G₂ X₂ q (m₂ ∘ ![1, 1, 0]) (A₂ ∘ id) :=
  typ_comp_congr q ![1, 1, 0] id h

/-! ### Adequacy

The atomic cases go through the diagram, which the two types share; the
quantifier cases go through the move sets, which is where the rank is
spent. Nothing else happens. -/

/-- Regions of equal type have the same adjacencies between marks. -/
theorem adj_iff_of_diagram_eq {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
    {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)}
    (hd : Atomic.of G₁ m₁ A₁ = Atomic.of G₂ m₂ A₂) (i j : Fin r) :
    G₁.Adj (m₁ i) (m₁ j) ↔ G₂.Adj (m₂ i) (m₂ j) := by
  have := congrArg (fun a => Atomic.adj a i j) hd
  simpa [Atomic.of] using this

/-- Regions of equal type have the same equalities between marks. -/
theorem eq_iff_of_diagram_eq {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
    {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)}
    (hd : Atomic.of G₁ m₁ A₁ = Atomic.of G₂ m₂ A₂) (i j : Fin r) :
    m₁ i = m₁ j ↔ m₂ i = m₂ j := by
  have := congrArg (fun a => Atomic.eq a i j) hd
  simpa [Atomic.of] using this

/-- Regions of equal type have the same memberships of marks in named
sets. -/
theorem mem_iff_of_diagram_eq {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
    {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)}
    (hd : Atomic.of G₁ m₁ A₁ = Atomic.of G₂ m₂ A₂) (i : Fin r) (Y : Fin s) :
    m₁ i ∈ A₁ Y ↔ m₂ i ∈ A₂ Y := by
  have := congrArg (fun a => Atomic.mem a i Y) hd
  simpa [Atomic.of] using this

/-- **Adequacy.** A formula of quantifier rank at most `q` cannot tell
apart two boundaried regions of the same `q`-type — not even in two
different ambient graphs. Truth of a rank-`q` formula on a region is
therefore a function of a single element of the finite type `T q r s`,
which is the finiteness a linear-time table needs. -/
theorem satIn_congr : ∀ {r s : ℕ} (φ : MSO r s) {q : ℕ}, rank φ ≤ q →
    ∀ {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
      {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
      {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
      {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
      typ G₁ X₁ q m₁ A₁ = typ G₂ X₂ q m₂ A₂ →
      (SatIn G₁ X₁ m₁ A₁ φ ↔ SatIn G₂ X₂ m₂ A₂ φ) := by
  intro r s φ
  induction φ with
  | adj i j =>
      intro q _ n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      exact adj_iff_of_diagram_eq (by simpa using congrArg T.diagram h) i j
  | eq i j =>
      intro q _ n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      exact eq_iff_of_diagram_eq (by simpa using congrArg T.diagram h) i j
  | mem i Y =>
      intro q _ n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      exact mem_iff_of_diagram_eq (by simpa using congrArg T.diagram h) i Y
  | not φ ih =>
      intro q hq n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      exact not_congr (ih hq h)
  | and φ ψ ihφ ihψ =>
      intro q hq n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      exact and_congr (ihφ (le_trans (le_max_left _ _) hq) h)
        (ihψ (le_trans (le_max_right _ _) hq) h)
  | exV φ ih =>
      rename_i r s
      intro q hq n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      rw [rank_exV] at hq
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hφ : rank φ ≤ q := by omega
      have key : ∀ {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
          {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
          {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          typ G₁ X₁ (q + 1) m₁ A₁ = typ G₂ X₂ (q + 1) m₂ A₂ →
          SatIn G₁ X₁ m₁ A₁ φ.exV → SatIn G₂ X₂ m₂ A₂ φ.exV := by
        intro n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h hs
        obtain ⟨v, hv, hsv⟩ := hs
        have h₁ := vMoves_typ_snoc (G := G₁) (X := X₁) (q := q) (m := m₁) (A := A₁) hv
        rw [h, vMoves_typ] at h₁
        obtain ⟨w, hw, hwt⟩ := h₁
        exact ⟨w, hw, (ih hφ hwt.symm).mp hsv⟩
      exact ⟨key h, key h.symm⟩
  | exS φ ih =>
      rename_i r s
      intro q hq n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h
      rw [rank_exS] at hq
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hφ : rank φ ≤ q := by omega
      have key : ∀ {n₁ n₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
          {X₁ : Set (Fin n₁)} {X₂ : Set (Fin n₂)}
          {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
          {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)},
          typ G₁ X₁ (q + 1) m₁ A₁ = typ G₂ X₂ (q + 1) m₂ A₂ →
          SatIn G₁ X₁ m₁ A₁ φ.exS → SatIn G₂ X₂ m₂ A₂ φ.exS := by
        intro n₁ n₂ G₁ G₂ X₁ X₂ m₁ m₂ A₁ A₂ h hs
        obtain ⟨S, hS, hsS⟩ := hs
        have h₁ := sMoves_typ_snoc (G := G₁) (X := X₁) (q := q) (m := m₁) (A := A₁) hS
        rw [h, sMoves_typ] at h₁
        obtain ⟨S', hS', hS't⟩ := h₁
        exact ⟨S', hS', (ih hφ hS't.symm).mp hsS⟩
      exact ⟨key h, key h.symm⟩

/-- Adequacy for the whole graph: the type of the ambient graph as a
region decides every sentence of rank at most `q`. This is the form the
driver consumes — the accepting set of C9 is the set of types of rank
`q = rank φ` whose realizations satisfy `φ`. -/
theorem sat_congr {r s : ℕ} (φ : MSO r s) {q : ℕ} (hq : rank φ ≤ q)
    {m₁ : Fin r → Fin n₁} {m₂ : Fin r → Fin n₂}
    {A₁ : Fin s → Set (Fin n₁)} {A₂ : Fin s → Set (Fin n₂)}
    (h : typ G₁ Set.univ q m₁ A₁ = typ G₂ Set.univ q m₂ A₂) :
    (Sat G₁ m₁ A₁ φ ↔ Sat G₂ m₂ A₂ φ) := by
  rw [← satIn_univ φ m₁ A₁, ← satIn_univ φ m₂ A₂]
  exact satIn_congr φ hq h

/-- Adequacy for sentences, spelled out: two graphs whose `q`-types
agree satisfy the same sentences of rank at most `q`. -/
theorem sat_congr_sentence (φ : MSO 0 0) {q : ℕ} (hq : rank φ ≤ q)
    (h : typ G₁ Set.univ q Fin.elim0 Fin.elim0 = typ G₂ Set.univ q Fin.elim0 Fin.elim0) :
    (Sat G₁ Fin.elim0 Fin.elim0 φ ↔ Sat G₂ Fin.elim0 Fin.elim0 φ) :=
  sat_congr φ hq h

end Lax11Proofs.MsoTypes
