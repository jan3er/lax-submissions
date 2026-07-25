import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Image

/-!
Rank-`j` local Ehrenfeucht–Fraïssé types of decorated balls.

For a graph `H` on a finite vertex type, a decoration `dec : V → D`
into a finite type, a center `c` and a radius `R`, the *local type*
`ltype H dec c R j t` of a tuple `t` is a hereditarily finite tree
invariant: at level `0` it records the atomic data of the tuple
(adjacency, equality, decorations, and distance-to-center thresholds up
to `R`), and at level `j+1` additionally the finite set of level-`j`
types of all one-point extensions of the tuple by elements of the
radius-`R` ball around the center.

Equality of local types is exactly `j`-round EF equivalence of the
decorated pointed balls, but no formulas or games appear: the extension
lemma `ltype_ext` *is* the back-and-forth property, the restriction
lemma `ltype_mono` lowers the round budget, and `ltype_wle_transfer`
shows walk-distances up to `2^j` between tuple entries are preserved.
The value type `LType D R j ℓ` is finite with a cardinality independent
of the graph, which replaces "finitely many formulas of quantifier rank
`j` up to equivalence" throughout the Adler–Adler argument.
-/

set_option synthInstance.maxSize 400

namespace Lax5Proofs.LocalTypes

/-! ### Bounded-length walk reachability -/

section WLE

variable {V : Type}

/-- There is a walk of length at most `d` from `a` to `b` in `H`. -/
def WLE (H : SimpleGraph V) (a b : V) (d : ℕ) : Prop :=
  ∃ p : H.Walk a b, p.length ≤ d

theorem WLE.refl (H : SimpleGraph V) (a : V) (d : ℕ) : WLE H a a d :=
  ⟨.nil, Nat.zero_le _⟩

theorem WLE.symm {H : SimpleGraph V} {a b : V} {d : ℕ} (h : WLE H a b d) :
    WLE H b a d := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by rwa [SimpleGraph.Walk.length_reverse]⟩

theorem WLE.mono {H : SimpleGraph V} {a b : V} {d d' : ℕ} (hd : d ≤ d')
    (h : WLE H a b d) : WLE H a b d' := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.trans hd⟩

theorem WLE.trans {H : SimpleGraph V} {a b z : V} {d₁ d₂ : ℕ}
    (h₁ : WLE H a z d₁) (h₂ : WLE H z b d₂) : WLE H a b (d₁ + d₂) := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  exact ⟨p.append q, by rw [SimpleGraph.Walk.length_append]; omega⟩

theorem wle_zero {H : SimpleGraph V} {a b : V} : WLE H a b 0 ↔ a = b := by
  constructor
  · rintro ⟨p, hp⟩
    exact SimpleGraph.Walk.eq_of_length_eq_zero (Nat.le_zero.mp hp)
  · rintro rfl
    exact WLE.refl H a 0

theorem wle_one {H : SimpleGraph V} {a b : V} :
    WLE H a b 1 ↔ a = b ∨ H.Adj a b := by
  constructor
  · rintro ⟨p, hp⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with h0 | h1
    · exact Or.inl (SimpleGraph.Walk.eq_of_length_eq_zero h0)
    · exact Or.inr (SimpleGraph.Walk.adj_of_length_eq_one h1)
  · rintro (rfl | hadj)
    · exact WLE.refl H a 1
    · exact ⟨.cons hadj .nil, le_refl _⟩

/-- A walk of length at most `d₁ + d₂` splits at a midpoint. -/
theorem wle_split {H : SimpleGraph V} (d₁ : ℕ) :
    ∀ {a b : V} {d₂ : ℕ}, WLE H a b (d₁ + d₂) →
      ∃ z : V, WLE H a z d₁ ∧ WLE H z b d₂ := by
  induction d₁ with
  | zero =>
    intro a b d₂ h
    exact ⟨a, WLE.refl H a 0, by simpa using h⟩
  | succ d₁ ih =>
    intro a b d₂ h
    obtain ⟨p, hp⟩ := h
    cases p with
    | nil => exact ⟨a, WLE.refl H a _, WLE.refl H a _⟩
    | cons hadj p' =>
      obtain ⟨z, hz₁, hz₂⟩ := ih (d₂ := d₂) ⟨p', by
        simp only [SimpleGraph.Walk.length_cons] at hp; omega⟩
      obtain ⟨q, hq⟩ := hz₁
      exact ⟨z, ⟨.cons hadj q, by
        simp only [SimpleGraph.Walk.length_cons]; omega⟩, hz₂⟩

/-- The radius-`R` ball around `c` in `H`, as a finset. -/
noncomputable def ballFinset [Fintype V] (H : SimpleGraph V) (c : V)
    (R : ℕ) : Finset V :=
  letI := Classical.dec
  Finset.univ.filter fun x => WLE H c x R

theorem mem_ballFinset [Fintype V] {H : SimpleGraph V} {c x : V} {R : ℕ} :
    x ∈ ballFinset H c R ↔ WLE H c x R := by
  simp [ballFinset]

end WLE

/-! ### Atomic data and the type tower -/

/-- Classical proposition-to-Bool conversion. -/
noncomputable def pb (p : Prop) : Bool :=
  @decide p (Classical.propDecidable p)

theorem pb_eq_pb {p q : Prop} : pb p = pb q ↔ (p ↔ q) := decide_eq_decide

/-- Atomic data of an `ℓ`-tuple: adjacency and equality patterns, the
decorations of the entries, and their distance-to-center thresholds up
to `R`. -/
abbrev AtomData (D : Type) (R ℓ : ℕ) : Type :=
  (Fin ℓ → Fin ℓ → Bool) × (Fin ℓ → Fin ℓ → Bool) × (Fin ℓ → D) ×
    (Fin ℓ → Fin (R + 1) → Bool)

/-- The level-`j` local type values for `ℓ`-tuples: a hereditarily
finite tree over atomic data. -/
def LType (D : Type) (R : ℕ) : ℕ → ℕ → Type
  | 0, ℓ => AtomData D R ℓ
  | j + 1, ℓ => AtomData D R ℓ × Finset (LType D R j (ℓ + 1))

section Instances

variable {D : Type}

noncomputable instance instDecEqLType [DecidableEq D] (R : ℕ) :
    ∀ j ℓ, DecidableEq (LType D R j ℓ)
  | 0, ℓ => inferInstanceAs (DecidableEq (AtomData D R ℓ))
  | j + 1, ℓ =>
    letI := instDecEqLType R j (ℓ + 1)
    inferInstanceAs (DecidableEq (AtomData D R ℓ × Finset (LType D R j (ℓ + 1))))

noncomputable instance instFintypeLType [DecidableEq D] [Fintype D] (R : ℕ) :
    ∀ j ℓ, Fintype (LType D R j ℓ)
  | 0, ℓ => inferInstanceAs (Fintype (AtomData D R ℓ))
  | j + 1, ℓ =>
    letI := instFintypeLType R j (ℓ + 1)
    letI := instDecEqLType (D := D) R j (ℓ + 1)
    inferInstanceAs (Fintype (AtomData D R ℓ × Finset (LType D R j (ℓ + 1))))

end Instances

section LtypeDef

variable {V D : Type} [Fintype V] [DecidableEq D]

/-- The atomic data of a tuple. -/
noncomputable def atom (H : SimpleGraph V) (dec : V → D) (c : V) (R : ℕ)
    {ℓ : ℕ} (t : Fin ℓ → V) : AtomData D R ℓ :=
  (fun i i' => pb (H.Adj (t i) (t i')),
   fun i i' => pb (t i = t i'),
   fun i => dec (t i),
   fun i d => pb (WLE H c (t i) d))

/-- The level-`j` local type of a tuple relative to a decorated pointed
ball. -/
noncomputable def ltype (H : SimpleGraph V) (dec : V → D) (c : V) (R : ℕ) :
    ∀ (j : ℕ) {ℓ : ℕ} (_ : Fin ℓ → V), LType D R j ℓ
  | 0, _, t => atom H dec c R t
  | j + 1, _, t =>
    (atom H dec c R t,
     (ballFinset H c R).image fun x => ltype H dec c R j (Fin.snoc t x))

/-- The atomic-data component of a local type value. -/
def LType.atomPart {R : ℕ} : ∀ {j ℓ : ℕ}, LType D R j ℓ → AtomData D R ℓ
  | 0, _, a => a
  | _ + 1, _, a => a.1

theorem atomPart_ltype {H : SimpleGraph V} {dec : V → D} {c : V} {R : ℕ}
    {j ℓ : ℕ} (t : Fin ℓ → V) :
    (ltype H dec c R j t).atomPart = atom H dec c R t := by
  cases j <;> rfl

end LtypeDef

/-! ### Consequences of local type equality -/

section Transfer

variable {V D : Type} [Fintype V] [DecidableEq D]
variable {H : SimpleGraph V} {dec : V → D} {c c' : V} {R : ℕ}

section Fixed

variable {j ℓ : ℕ} {t t' : Fin ℓ → V}

/-- Equal local types give matching atomic data. -/
theorem ltype_atom_eq (h : ltype H dec c R j t = ltype H dec c' R j t') :
    atom H dec c R t = atom H dec c' R t' := by
  have := congrArg LType.atomPart h
  rwa [atomPart_ltype, atomPart_ltype] at this

theorem ltype_adj_iff (h : ltype H dec c R j t = ltype H dec c' R j t')
    (i i' : Fin ℓ) : H.Adj (t i) (t i') ↔ H.Adj (t' i) (t' i') := by
  have := congrFun (congrFun (congrArg Prod.fst (ltype_atom_eq h)) i) i'
  exact pb_eq_pb.mp this

theorem ltype_eq_iff (h : ltype H dec c R j t = ltype H dec c' R j t')
    (i i' : Fin ℓ) : t i = t i' ↔ t' i = t' i' := by
  have := congrFun (congrFun (congrArg (fun a => a.2.1) (ltype_atom_eq h)) i) i'
  exact pb_eq_pb.mp this

theorem ltype_dec_eq (h : ltype H dec c R j t = ltype H dec c' R j t')
    (i : Fin ℓ) : dec (t i) = dec (t' i) :=
  congrFun (congrArg (fun a => a.2.2.1) (ltype_atom_eq h)) i

theorem ltype_cdist_iff (h : ltype H dec c R j t = ltype H dec c' R j t')
    (i : Fin ℓ) (d : Fin (R + 1)) :
    WLE H c (t i) d ↔ WLE H c' (t' i) d := by
  have := congrFun (congrFun (congrArg (fun a => a.2.2.2) (ltype_atom_eq h)) i) d
  exact pb_eq_pb.mp this

/-- Distance-to-center thresholds transfer for any bound at most `R`. -/
theorem ltype_cdist_iff' (h : ltype H dec c R j t = ltype H dec c' R j t')
    (i : Fin ℓ) {d : ℕ} (hd : d ≤ R) :
    WLE H c (t i) d ↔ WLE H c' (t' i) d := by
  have := ltype_cdist_iff h i ⟨d, by omega⟩
  simpa using this

/-- The forth property: a one-point extension by a ball element on the
left is matched by a ball element on the right with equal level-`j`
types. -/
theorem ltype_ext (h : ltype H dec c R (j + 1) t = ltype H dec c' R (j + 1) t')
    {x : V} (hx : x ∈ ballFinset H c R) :
    ∃ x' ∈ ballFinset H c' R,
      ltype H dec c R j (Fin.snoc t x) = ltype H dec c' R j (Fin.snoc t' x') := by
  have himg : ((ballFinset H c R).image fun z => ltype H dec c R j (Fin.snoc t z)) =
      (ballFinset H c' R).image fun z => ltype H dec c' R j (Fin.snoc t' z) :=
    congrArg Prod.snd h
  have hmem : ltype H dec c R j (Fin.snoc t x) ∈
      (ballFinset H c' R).image fun z => ltype H dec c' R j (Fin.snoc t' z) := by
    rw [← himg]
    exact Finset.mem_image_of_mem _ hx
  obtain ⟨x', hx', hx'eq⟩ := Finset.mem_image.mp hmem
  exact ⟨x', hx', hx'eq.symm⟩

end Fixed

/-- Lowering the level: equal level-`(j+1)` types give equal level-`j`
types. -/
theorem ltype_mono :
    ∀ {j ℓ : ℕ} {t t' : Fin ℓ → V},
      ltype H dec c R (j + 1) t = ltype H dec c' R (j + 1) t' →
      ltype H dec c R j t = ltype H dec c' R j t'
  | 0, ℓ, t, t', h => ltype_atom_eq h
  | j + 1, ℓ, t, t', h => by
    refine Prod.ext (ltype_atom_eq h) ?_
    show ((ballFinset H c R).image fun z => ltype H dec c R j (Fin.snoc t z)) =
        (ballFinset H c' R).image fun z => ltype H dec c' R j (Fin.snoc t' z)
    apply Finset.ext
    intro v
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨x', hx', hx'eq⟩ := ltype_ext h hx
      exact ⟨x', hx', (ltype_mono hx'eq).symm⟩
    · rintro ⟨x', hx', rfl⟩
      obtain ⟨x, hx, hxeq⟩ := ltype_ext h.symm hx'
      exact ⟨x, hx, ltype_mono hxeq.symm⟩

/-- Lowering the level by any amount. -/
theorem ltype_mono_le {j j' ℓ : ℕ} {t t' : Fin ℓ → V} (hj : j' ≤ j)
    (h : ltype H dec c R j t = ltype H dec c' R j t') :
    ltype H dec c R j' t = ltype H dec c' R j' t' := by
  induction hj with
  | refl => exact h
  | step _ ih => exact ih (ltype_mono h)

/-! ### Distance transfer -/

/-- Walk-distances up to `2^j` between tuple entries transfer along
level-`j` local type equality, as long as the walks fit inside the
ball: the hypothesis `ra + d ≤ R` places the entry `t i` at distance
`ra` from the center with room `d` to spare. -/
theorem ltype_wle_transfer :
    ∀ {j ℓ : ℕ} {t t' : Fin ℓ → V},
      ltype H dec c R j t = ltype H dec c' R j t' →
      ∀ (i i' : Fin ℓ) (d ra : ℕ), d ≤ 2 ^ j →
        WLE H c (t i) ra → ra + d ≤ R →
        WLE H (t i) (t i') d → WLE H (t' i) (t' i') d := by
  intro j
  induction j with
  | zero =>
    intro ℓ t t' h i i' d ra hd _ _ hw
    have hd1 : d ≤ 1 := by simpa using hd
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd1 with rfl | rfl
    · exact wle_zero.mpr ((ltype_eq_iff h i i').mp (wle_zero.mp hw))
    · rcases wle_one.mp hw with heq | hadj
      · exact (wle_zero.mpr ((ltype_eq_iff h i i').mp heq)).mono (by omega)
      · exact wle_one.mpr (Or.inr ((ltype_adj_iff h i i').mp hadj))
  | succ j ih =>
    intro ℓ t t' h i i' d ra hd hra hraR hw
    by_cases hdj : d ≤ 2 ^ j
    · exact ih (ltype_mono h) i i' d ra hdj hra hraR hw
    · replace hdj : 2 ^ j < d := Nat.lt_of_not_le hdj
      -- split the walk at distance 2^j
      have hdsum : d = 2 ^ j + (d - 2 ^ j) := by omega
      obtain ⟨z, hz₁, hz₂⟩ := wle_split (2 ^ j) (hdsum ▸ hw)
      have hd₂ : d - 2 ^ j ≤ 2 ^ j := by
        have : (2 : ℕ) ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; omega
        omega
      -- z lies in the ball around c
      have hzball : z ∈ ballFinset H c R :=
        mem_ballFinset.mpr ((hra.trans hz₁).mono (by omega))
      obtain ⟨z', hz'ball, hzeq⟩ := ltype_ext h hzball
      -- transfer the first half on the extended tuples
      have h₁ : WLE H (t' i) z' (2 ^ j) := by
        have := ih hzeq i.castSucc (Fin.last ℓ) (2 ^ j) ra (le_refl _)
          (by rwa [Fin.snoc_castSucc]) (by omega)
        simpa [Fin.snoc_castSucc, Fin.snoc_last] using
          this (by simpa [Fin.snoc_castSucc, Fin.snoc_last] using hz₁)
      -- transfer the second half on the extended tuples
      have h₂ : WLE H z' (t' i') (d - 2 ^ j) := by
        have := ih hzeq (Fin.last ℓ) i'.castSucc (d - 2 ^ j) (ra + 2 ^ j) hd₂
          (by simpa [Fin.snoc_last] using hra.trans hz₁) (by omega)
        simpa [Fin.snoc_castSucc, Fin.snoc_last] using
          this (by simpa [Fin.snoc_castSucc, Fin.snoc_last] using hz₂)
      have := h₁.trans h₂
      rwa [← hdsum] at this

end Transfer

end Lax5Proofs.LocalTypes
