import Lax5.GraphTransductions
import Lax5Proofs.Subdivision
import Lax5Proofs.Sparsification
import Lax5Proofs.TransductionCalculus

/-!
The star-crossing transduction (Mählmann §2 hardness picture, star
case): a class containing, for a fixed `ℓ ≥ 1`, induced exact
`ℓ`-subdivided bicliques of every order transduces the class of all
graphs.

Two-step, thesis-faithful: the fixed `subdivisionTransduction ℓ` marks
the principals of a copy (the domain color) and the internal vertices
of *kept* subdivision paths (the blue color), and joins two domain
vertices when a walk of length `ℓ + 1` with all `ℓ` interior vertices
blue connects them — since the copy is induced and blue vertices are
confined to kept paths, such a walk is forced along a single
subdivision path, so the transduction produces every bipartite graph.
The fixed `incidenceTransduction` then joins two vertex-side vertices
of an incidence graph when they have a common edge-side neighbor,
producing every graph from its (bipartite) incidence graph. The two
steps compose by `Transduces.trans`.

The interior-forcing argument is carried out on the abstract graph
`subdividedBiclique m ℓ` and transported through the induced-copy
embedding: interior vertices of distinct subdivision paths are never
adjacent and principals are never blue, so a walk with blue interior
starting at an interior vertex of a kept path stays on that path
(`blueWalk_inr`), and a blue walk between two distinct principals
identifies a kept path having them as its endpoints
(`kept_of_blueWalk_principal`). Walks, not paths: repetitions are
harmless because the endpoint principals are distinct.
-/

namespace Lax5Proofs.CrossingTransduction

open FirstOrder Lax5.Transductions Lax5.GraphClasses
open Lax5Proofs.Subdivision

/-! ## Blue walks -/

/-- A walk of length `ℓ + 1` from `x` to `y` whose `ℓ` interior
vertices all lie in `blue`. The endpoints are unconstrained. -/
def BlueWalk {V : Type*} (G : SimpleGraph V) (blue : Set V) :
    ℕ → V → V → Prop
  | 0, x, y => G.Adj x y
  | ℓ + 1, x, y => ∃ z ∈ blue, G.Adj x z ∧ BlueWalk G blue ℓ z y

theorem BlueWalk.snoc {V : Type*} {G : SimpleGraph V} {blue : Set V} :
    ∀ {ℓ : ℕ} {x w y : V}, BlueWalk G blue ℓ x w → w ∈ blue →
      G.Adj w y → BlueWalk G blue (ℓ + 1) x y
  | 0, _, w, _, hxw, hw, hwy => ⟨w, hw, hxw, hwy⟩
  | _ + 1, _, _, _, ⟨z, hz, hxz, hzw⟩, hw, hwy =>
      ⟨z, hz, hxz, hzw.snoc hw hwy⟩

theorem BlueWalk.symm {V : Type*} {G : SimpleGraph V} {blue : Set V}
    {ℓ : ℕ} : ∀ {x y : V}, BlueWalk G blue ℓ x y →
      BlueWalk G blue ℓ y x := by
  induction ℓ with
  | zero => exact fun h => G.symm h
  | succ ℓ ih =>
    rintro x y ⟨z, hz, hxz, hzy⟩
    exact (ih hzy).snoc hz hxz.symm

/-- Blue walks transport through a graph embedding whose image carries
the blue set. -/
theorem blueWalk_map {V W : Type*} {H : SimpleGraph V}
    {G : SimpleGraph W} (φ : H ↪g G) (blue : Set V) :
    ∀ (ℓ : ℕ) (x y : V),
      BlueWalk G (φ '' blue) ℓ (φ x) (φ y) ↔ BlueWalk H blue ℓ x y
  | 0, _, _ => φ.map_adj_iff
  | ℓ + 1, x, y => by
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, hxz, hzy⟩
      exact ⟨z, hz, φ.map_adj_iff.1 hxz, (blueWalk_map φ blue ℓ z y).1 hzy⟩
    · rintro ⟨z, hz, hxz, hzy⟩
      exact ⟨φ z, ⟨z, hz, rfl⟩, φ.map_adj_iff.2 hxz,
        (blueWalk_map φ blue ℓ z y).2 hzy⟩

/-! ## The walk formula -/

/-- The formula asserting a blue walk of length `ℓ + 1` between its two
free variables: `ℓ` existentially quantified interior vertices, each of
color `blue`, chained by adjacency. Built by recursion on `ℓ`; the tail
is relabeled so that its start becomes the fresh quantified vertex. -/
noncomputable def walkFormula (c : ℕ) (blue : Fin c) :
    ℕ → (withColors Language.graph c).Formula (Fin 2)
  | 0 => adjAtom (Language.Term.var (Sum.inl 0))
      (Language.Term.var (Sum.inl 1))
  | ℓ + 1 =>
      (colorAtom blue (&0) ⊓
        adjAtom (Language.Term.var (Sum.inl 0)) (&0) ⊓
        Language.BoundedFormula.relabel
          (![Sum.inr 0, Sum.inl 1] : Fin 2 → Fin 2 ⊕ Fin 1)
          (walkFormula c blue ℓ)).ex

theorem realizeIn_walkFormula {c n : ℕ} (blue : Fin c)
    (G : SimpleGraph (Fin n)) (colors : Fin c → Set (Fin n)) :
    ∀ (ℓ : ℕ) (x y : Fin n),
      RealizeIn G.structure colors (walkFormula c blue ℓ) ![x, y] ↔
        BlueWalk G (colors blue) ℓ x y := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro x y
    letI := G.structure
    letI := colorStructure colors
    have hadj (v : Fin 2 → Fin n) :
        @Language.Structure.RelMap (withColors Language.graph c)
          _ _ 2 (Sum.inl Language.adj) v ↔ G.Adj (v 0) (v 1) := Iff.rfl
    simp [walkFormula, RealizeIn, Language.Formula.Realize,
      Language.BoundedFormula.Realize, adjAtom,
      Language.Relations.boundedFormula₂,
      Language.Relations.boundedFormula, hadj, BlueWalk]
  | succ ℓ ih =>
    intro x y
    letI := G.structure
    letI := colorStructure colors
    have hcolor (i : Fin c) (v : Fin 1 → Fin n) :
        @Language.Structure.RelMap (withColors Language.graph c)
          _ _ 1 (Sum.inr (ColorRel.color i)) v ↔ v 0 ∈ colors i := Iff.rfl
    have hadj (v : Fin 2 → Fin n) :
        @Language.Structure.RelMap (withColors Language.graph c)
          _ _ 2 (Sum.inl Language.adj) v ↔ G.Adj (v 0) (v 1) := Iff.rfl
    have htail (z : Fin n) :
        Language.BoundedFormula.Realize
            (L := withColors Language.graph c) (M := Fin n)
            (Language.BoundedFormula.relabel
              (![Sum.inr 0, Sum.inl 1] : Fin 2 → Fin 2 ⊕ Fin 1)
              (walkFormula c blue ℓ)) ![x, y] ![z] ↔
          BlueWalk G (colors blue) ℓ z y := by
      rw [Language.BoundedFormula.realize_relabel]
      have hv : (Sum.elim (![x, y] : Fin 2 → Fin n)
            ((![z] : Fin 1 → Fin n) ∘ Fin.castAdd 0) ∘
          (![Sum.inr 0, Sum.inl 1] : Fin 2 → Fin 2 ⊕ Fin 1)) = ![z, y] := by
        funext i
        fin_cases i <;> rfl
      rw [hv, Language.Formula.boundedFormula_realize_eq_realize]
      exact ih z y
    calc RealizeIn G.structure colors (walkFormula c blue (ℓ + 1)) ![x, y]
        ↔ ∃ z : Fin n, z ∈ colors blue ∧ G.Adj x z ∧
            Language.BoundedFormula.Realize
              (L := withColors Language.graph c) (M := Fin n)
              (Language.BoundedFormula.relabel
                (![Sum.inr 0, Sum.inl 1] : Fin 2 → Fin 2 ⊕ Fin 1)
                (walkFormula c blue ℓ)) ![x, y] ![z] := by
          simp only [walkFormula, RealizeIn, Language.Formula.Realize,
            Language.BoundedFormula.realize_ex,
            Language.BoundedFormula.realize_inf]
          constructor
          · rintro ⟨z, ⟨hc, ha⟩, ht⟩
            refine ⟨z, ?_, ?_, ?_⟩
            · simpa [colorAtom, Language.Relations.boundedFormula₁,
                Language.Relations.boundedFormula,
                Language.BoundedFormula.Realize, hcolor, Fin.snoc] using hc
            · simpa [adjAtom, Language.Relations.boundedFormula₂,
                Language.Relations.boundedFormula,
                Language.BoundedFormula.Realize, hadj, Fin.snoc] using ha
            · have hz : (Fin.snoc (default : Fin 0 → Fin n) z :
                  Fin 1 → Fin n) = ![z] := by
                funext i
                fin_cases i
                simp [Fin.snoc]
              rwa [hz] at ht
          · rintro ⟨z, hc, ha, ht⟩
            have hz : (Fin.snoc (default : Fin 0 → Fin n) z :
                Fin 1 → Fin n) = ![z] := by
              funext i
              fin_cases i
              simp [Fin.snoc]
            refine ⟨z, ⟨?_, ?_⟩, ?_⟩
            · rw [hz]
              simpa [colorAtom, Language.Relations.boundedFormula₁,
                Language.Relations.boundedFormula,
                Language.BoundedFormula.Realize, hcolor, Fin.snoc] using hc
            · rw [hz]
              simpa [adjAtom, Language.Relations.boundedFormula₂,
                Language.Relations.boundedFormula,
                Language.BoundedFormula.Realize, hadj, Fin.snoc] using ha
            · rwa [hz]
      _ ↔ BlueWalk G (colors blue) (ℓ + 1) x y := by
          simp only [BlueWalk]
          exact exists_congr fun z => by rw [htail z]

/-! ## Forcing on the abstract subdivided biclique -/

/-- The interior vertices of the kept subdivision paths. -/
def keptInterior {m : ℕ} (K : Set (Fin m × Fin m)) (ℓ : ℕ) :
    Set (SubdividedBicliqueVert m ℓ) :=
  {v | ∃ e ∈ K, ∃ j : Fin ℓ, v = Sum.inr (e, j)}

/-- Neighbors of an interior vertex of the subdivided biclique: the two
principals of its path, or another interior vertex of the same path. -/
theorem adj_inr {m ℓ : ℕ} {e : Fin m × Fin m} {j : Fin ℓ}
    {w : SubdividedBicliqueVert m ℓ}
    (h : (subdividedBiclique m ℓ).Adj (Sum.inr (e, j)) w) :
    w = Sum.inl (Sum.inl e.1) ∨ w = Sum.inl (Sum.inr e.2) ∨
      ∃ j' : Fin ℓ, w = Sum.inr (e, j') := by
  rw [subdividedBiclique, SimpleGraph.fromRel_adj] at h
  obtain ⟨-, h | h⟩ := h
  · rcases w with (i | i) | ⟨e', j'⟩
    · exact absurd h not_false
    · exact absurd h not_false
    · obtain ⟨rfl, -⟩ := h
      exact Or.inr (Or.inr ⟨j', rfl⟩)
  · rcases w with (i | i) | ⟨e', j'⟩
    · obtain ⟨rfl, -⟩ := h
      exact Or.inl rfl
    · obtain ⟨rfl, -⟩ := h
      exact Or.inr (Or.inl rfl)
    · obtain ⟨rfl, -⟩ := h
      exact Or.inr (Or.inr ⟨j', rfl⟩)

/-- A walk with blue interior starting at an interior vertex of a kept
path ends on that path or at one of its principals. -/
theorem blueWalk_inr {m ℓ : ℕ} {K : Set (Fin m × Fin m)}
    {e : Fin m × Fin m} :
    ∀ {ℓ' : ℕ} {j : Fin ℓ} {Q : SubdividedBicliqueVert m ℓ},
      BlueWalk (subdividedBiclique m ℓ) (keptInterior K ℓ) ℓ'
        (Sum.inr (e, j)) Q →
      Q = Sum.inl (Sum.inl e.1) ∨ Q = Sum.inl (Sum.inr e.2) ∨
        ∃ j' : Fin ℓ, Q = Sum.inr (e, j') := by
  intro ℓ'
  induction ℓ' with
  | zero => exact fun h => adj_inr h
  | succ ℓ' ih =>
    rintro j Q ⟨z, ⟨e'', -, j'', rfl⟩, hadj, hwalk⟩
    rcases adj_inr hadj with h | h | ⟨j', h⟩
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Sum.inr_injective h)
      exact ih hwalk

/-- Forcing: a blue walk of full length `ℓ ≥ 1` between two *distinct*
principals identifies a kept path having them as its two endpoints. -/
theorem kept_of_blueWalk_principal {m ℓ : ℕ} {K : Set (Fin m × Fin m)}
    (hℓ : 1 ≤ ℓ) {p q : Fin m ⊕ Fin m} (hne : p ≠ q)
    (h : BlueWalk (subdividedBiclique m ℓ) (keptInterior K ℓ) ℓ
      (Sum.inl p) (Sum.inl q)) :
    ∃ e ∈ K, (p = Sum.inl e.1 ∧ q = Sum.inr e.2) ∨
      (p = Sum.inr e.2 ∧ q = Sum.inl e.1) := by
  obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 :=
    ⟨ℓ - 1, by omega⟩
  obtain ⟨z, ⟨e, he, j, rfl⟩, hadj, hwalk⟩ := h
  have hp : p = Sum.inl e.1 ∨ p = Sum.inr e.2 := by
    rcases adj_inr hadj.symm with h | h | ⟨j', h⟩
    · exact Or.inl (Sum.inl_injective h)
    · exact Or.inr (Sum.inl_injective h)
    · exact absurd h (by simp)
  have hq : q = Sum.inl e.1 ∨ q = Sum.inr e.2 := by
    rcases blueWalk_inr hwalk with h | h | ⟨j', h⟩
    · exact Or.inl (Sum.inl_injective h)
    · exact Or.inr (Sum.inl_injective h)
    · exact absurd h (by simp)
  refine ⟨e, he, ?_⟩
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact absurd (hp.trans hq.symm) hne
  · exact Or.inl ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hq⟩
  · exact absurd (hp.trans hq.symm) hne

/-- The straight walk down a kept path, from an interior vertex to the
`b`-side principal. -/
theorem blueWalk_inr_to_b {m ℓ : ℕ} {K : Set (Fin m × Fin m)}
    {e : Fin m × Fin m} (he : e ∈ K) :
    ∀ (t : ℕ) (j : Fin ℓ), j.val + t + 1 = ℓ →
      BlueWalk (subdividedBiclique m ℓ) (keptInterior K ℓ) t
        (Sum.inr (e, j)) (Sum.inl (Sum.inr e.2)) := by
  intro t
  induction t with
  | zero =>
    intro j hj
    show (subdividedBiclique m ℓ).Adj _ _
    rw [subdividedBiclique, SimpleGraph.fromRel_adj]
    exact ⟨by simp, Or.inr ⟨rfl, by omega⟩⟩
  | succ t ih =>
    intro j hj
    refine ⟨Sum.inr (e, ⟨j.val + 1, by omega⟩), ⟨e, he, _, rfl⟩, ?_, ?_⟩
    · show (subdividedBiclique m ℓ).Adj _ _
      rw [subdividedBiclique, SimpleGraph.fromRel_adj]
      refine ⟨by simp [Fin.ext_iff], Or.inl ⟨rfl, rfl⟩⟩
    · exact ih ⟨j.val + 1, by omega⟩ (by simp; omega)

/-- A kept path carries a blue walk of full length between its two
principals. -/
theorem blueWalk_of_kept {m ℓ : ℕ} {K : Set (Fin m × Fin m)}
    {e : Fin m × Fin m} (he : e ∈ K) (hℓ : 1 ≤ ℓ) :
    BlueWalk (subdividedBiclique m ℓ) (keptInterior K ℓ) ℓ
      (Sum.inl (Sum.inl e.1)) (Sum.inl (Sum.inr e.2)) := by
  obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
  refine ⟨Sum.inr (e, ⟨0, by omega⟩), ⟨e, he, _, rfl⟩, ?_, ?_⟩
  · show (subdividedBiclique _ _).Adj _ _
    rw [subdividedBiclique, SimpleGraph.fromRel_adj]
    exact ⟨by simp, Or.inl ⟨rfl, rfl⟩⟩
  · exact blueWalk_inr_to_b he ℓ' ⟨0, by omega⟩ (by simp)

/-! ## Step 1: subdivided bicliques transduce all bipartite graphs -/

/-- The class of all finite bipartite graphs: some `2`-coloring has no
monochromatic edge. -/
def bipartiteGraphs : GraphClass := fun p B =>
  ∃ c : Fin p → Bool, ∀ u v, B.Adj u v → c u ≠ c v

/-- Adjacency formula of `subdivisionTransduction`: distinct vertices
joined by a walk of length `ℓ + 1` whose interior is blue (color 1). -/
noncomputable def subdivisionAdjFormula (ℓ : ℕ) :
    (withColors Language.graph 2).Formula (Fin 2) :=
  ∼((Language.Term.var (Sum.inl (0 : Fin 2))).bdEqual
      (Language.Term.var (Sum.inl 1))) ⊓ walkFormula 2 1 ℓ

theorem realizeIn_subdivisionAdjFormula {n : ℕ} (ℓ : ℕ)
    (G : SimpleGraph (Fin n)) (colors : Fin 2 → Set (Fin n))
    (x y : Fin n) :
    RealizeIn G.structure colors (subdivisionAdjFormula ℓ) ![x, y] ↔
      x ≠ y ∧ BlueWalk G (colors 1) ℓ x y := by
  letI := G.structure
  letI := colorStructure colors
  have hwalk := realizeIn_walkFormula (n := n) (1 : Fin 2) G colors ℓ x y
  unfold RealizeIn at hwalk ⊢
  simp only [subdivisionAdjFormula, Language.Formula.realize_inf,
    Language.Formula.realize_not, hwalk]
  simp [Language.Term.bdEqual, Language.Formula.Realize,
    Language.BoundedFormula.Realize]

/-- The fixed transduction from induced `ℓ`-subdivided bicliques to
bipartite graphs: color 0 marks the copies of the target vertices among
the principals, color 1 the interior vertices of the kept subdivision
paths. -/
noncomputable def subdivisionTransduction (ℓ : ℕ) :
    Transduction Language.graph Language.graph where
  colors := 2
  domain := colorAtom (0 : Fin 2) (Language.Term.var (Sum.inl 0))
  rel := fun R => match R with
    | .adj => subdivisionAdjFormula ℓ

/-- Step 1: a class containing induced exact `ℓ`-subdivided bicliques
of every order transduces the class of all bipartite graphs. -/
theorem transduces_bipartiteGraphs {C : GraphClass} {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (h : ∀ m : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧
      (subdividedBiclique m ℓ).IsIndContained G) :
    Lax5.GraphTransductions.Transduces C bipartiteGraphs := by
  classical
  refine ⟨subdivisionTransduction ℓ, ?_⟩
  intro p N hN
  obtain ⟨B, ⟨c, hc⟩, rfl⟩ := hN
  obtain ⟨n, G, hG, ⟨φ⟩⟩ := h p
  -- the side of a target vertex, and its principal in the copy
  set side : Fin p → Fin p ⊕ Fin p := fun u =>
    if c u then Sum.inl u else Sum.inr u with hside
  have hside_inl : ∀ u i, side u = Sum.inl i → c u = true ∧ u = i := by
    intro u i hh
    by_cases hu : c u
    · rw [hside] at hh
      simp only [hu, if_true] at hh
      exact ⟨hu, Sum.inl_injective hh⟩
    · rw [hside] at hh
      simp only [hu] at hh
      exact absurd hh (by simp)
  have hside_inr : ∀ u i, side u = Sum.inr i → c u = false ∧ u = i := by
    intro u i hh
    by_cases hu : c u
    · rw [hside] at hh
      simp only [hu, if_true] at hh
      exact absurd hh (by simp)
    · rw [hside] at hh
      simp only [hu] at hh
      exact ⟨by simp [hu], Sum.inr_injective hh⟩
  have hsideinj : Function.Injective side := by
    intro u w huw
    by_cases hu : c u
    · have h1 : side u = Sum.inl u := by simp [hside, hu]
      obtain ⟨-, rfl⟩ := hside_inl w u (huw.symm.trans h1)
      rfl
    · have h1 : side u = Sum.inr u := by simp [hside, hu]
      obtain ⟨-, rfl⟩ := hside_inr w u (huw.symm.trans h1)
      rfl
  set f : Fin p ↪ Fin n :=
    ⟨fun u => φ (Sum.inl (side u)),
      fun u w hh =>
        hsideinj (Sum.inl_injective (φ.injective hh))⟩ with hf
  -- kept paths: the edges of `B`, oriented from the true side
  set K : Set (Fin p × Fin p) :=
    {q | B.Adj q.1 q.2 ∧ c q.1 = true ∧ c q.2 = false} with hK
  set colors : Fin 2 → Set (Fin n) :=
    ![Set.range ⇑f, ⇑φ '' keptInterior K ℓ] with hcolors
  refine ⟨n, G.structure, ⟨G, hG, rfl⟩, colors, f, ?_, ?_⟩
  · intro x
    letI := G.structure
    letI := colorStructure colors
    change x ∈ Set.range ⇑f ↔ x ∈ colors 0
    rw [hcolors]
    simp
  · intro r R v
    cases R with
    | adj =>
      change B.Adj (v 0) (v 1) ↔
        RealizeIn G.structure colors (subdivisionAdjFormula ℓ) (⇑f ∘ v)
      have hfv : ⇑f ∘ v = ![f (v 0), f (v 1)] := by
        funext i
        fin_cases i <;> rfl
      rw [hfv, realizeIn_subdivisionAdjFormula]
      have hcol1 : colors 1 = ⇑φ '' keptInterior K ℓ := by
        rw [hcolors]
        simp
      have hfφ : ∀ u, f u = φ (Sum.inl (side u)) := fun u => rfl
      rw [hcol1, hfφ, hfφ,
        blueWalk_map φ (keptInterior K ℓ) ℓ (Sum.inl (side (v 0)))
          (Sum.inl (side (v 1)))]
      constructor
      · intro hadj
        have hcc : c (v 0) ≠ c (v 1) := hc _ _ hadj
        refine ⟨fun hh => hadj.ne
          (hsideinj (Sum.inl_injective (φ.injective hh))), ?_⟩
        by_cases h0 : c (v 0)
        · have h1 : c (v 1) = false := by
            cases hcv1 : c (v 1)
            · rfl
            · exact absurd (h0.trans hcv1.symm) hcc
          have he : ((v 0), (v 1)) ∈ K := ⟨hadj, h0, h1⟩
          have hw := blueWalk_of_kept he hℓ
          simpa [hside, h0, h1] using hw
        · have h0' : c (v 0) = false := by simpa using h0
          have h1 : c (v 1) = true := by
            cases hcv1 : c (v 1)
            · exact absurd (h0'.trans hcv1.symm) hcc
            · rfl
          have he : ((v 1), (v 0)) ∈ K := ⟨hadj.symm, h1, h0'⟩
          have hw := (blueWalk_of_kept he hℓ).symm
          simpa [hside, h0', h1] using hw
      · rintro ⟨hne, hwalk⟩
        have hne' : side (v 0) ≠ side (v 1) := fun hh =>
          hne (congrArg (fun z => φ (Sum.inl z)) hh)
        obtain ⟨e, he, hcase⟩ :=
          kept_of_blueWalk_principal hℓ hne' hwalk
        rcases hcase with ⟨hp, hq⟩ | ⟨hp, hq⟩
        · obtain ⟨-, h1⟩ := hside_inl _ _ hp
          obtain ⟨-, h2⟩ := hside_inr _ _ hq
          rw [h1, h2]
          exact he.1
        · obtain ⟨-, h1⟩ := hside_inr _ _ hp
          obtain ⟨-, h2⟩ := hside_inl _ _ hq
          rw [h1, h2]
          exact he.1.symm

/-! ## Step 2: bipartite graphs transduce all graphs -/

/-- Adjacency formula of `incidenceTransduction`: distinct vertices
with a common neighbor of color 1 (the edge side of an incidence
graph). -/
noncomputable def incidenceAdjFormula :
    (withColors Language.graph 2).Formula (Fin 2) :=
  ∼((Language.Term.var (Sum.inl (0 : Fin 2))).bdEqual
      (Language.Term.var (Sum.inl 1))) ⊓
    (colorAtom (1 : Fin 2) (&0) ⊓
      adjAtom (&0) (Language.Term.var (Sum.inl 0)) ⊓
      adjAtom (&0) (Language.Term.var (Sum.inl 1))).ex

theorem realizeIn_incidenceAdjFormula {n : ℕ} (G : SimpleGraph (Fin n))
    (colors : Fin 2 → Set (Fin n)) (x y : Fin n) :
    RealizeIn G.structure colors incidenceAdjFormula ![x, y] ↔
      x ≠ y ∧ ∃ z, z ∈ colors 1 ∧ G.Adj z x ∧ G.Adj z y := by
  letI := G.structure
  letI := colorStructure colors
  have hcolor (i : Fin 2) (v : Fin 1 → Fin n) :
      @Language.Structure.RelMap (withColors Language.graph 2)
        _ _ 1 (Sum.inr (ColorRel.color i)) v ↔ v 0 ∈ colors i := Iff.rfl
  have hadj (v : Fin 2 → Fin n) :
      @Language.Structure.RelMap (withColors Language.graph 2)
        _ _ 2 (Sum.inl Language.adj) v ↔ G.Adj (v 0) (v 1) := Iff.rfl
  simp [incidenceAdjFormula, RealizeIn, Language.Formula.Realize,
    Language.BoundedFormula.Realize, colorAtom, adjAtom,
    Language.Relations.boundedFormula₁, Language.Relations.boundedFormula₂,
    Language.Relations.boundedFormula, Language.Term.bdEqual,
    hcolor, hadj, Fin.snoc]

/-- The fixed transduction from incidence graphs to their underlying
graphs: color 0 marks the vertex side (the domain), color 1 the edge
side; adjacency is a common edge-side neighbor. -/
noncomputable def incidenceTransduction :
    Transduction Language.graph Language.graph where
  colors := 2
  domain := colorAtom (0 : Fin 2) (Language.Term.var (Sum.inl 0))
  rel := fun R => match R with
    | .adj => incidenceAdjFormula

/-- Step 2: the class of all bipartite graphs transduces the class of
all graphs, via incidence graphs. -/
theorem bipartiteGraphs_transduces_allGraphs :
    Lax5.GraphTransductions.Transduces bipartiteGraphs allGraphs := by
  classical
  refine ⟨incidenceTransduction, ?_⟩
  intro q N hN
  obtain ⟨H, -, rfl⟩ := hN
  -- the incidence graph of `H`, on vertex side plus edge side
  set ec := H.edgeFinset.card with hec
  set σ : Fin ec → Sym2 (Fin q) :=
    fun e => (H.edgeFinset.equivFin.symm e : Sym2 (Fin q)) with hσ
  have hσmem : ∀ e, σ e ∈ H.edgeFinset := fun e =>
    (H.edgeFinset.equivFin.symm e).property
  set IncAux : SimpleGraph (Fin q ⊕ Fin ec) :=
    SimpleGraph.fromRel (fun a b =>
      ∃ u e, a = Sum.inl u ∧ b = Sum.inr e ∧ u ∈ σ e) with hIncAux
  have hIncAdj : ∀ a b, IncAux.Adj a b ↔
      (∃ u e, a = Sum.inl u ∧ b = Sum.inr e ∧ u ∈ σ e) ∨
      (∃ u e, b = Sum.inl u ∧ a = Sum.inr e ∧ u ∈ σ e) := by
    intro a b
    rw [hIncAux, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · rintro (⟨u, e, rfl, rfl, hm⟩ | ⟨u, e, rfl, rfl, hm⟩)
      · exact ⟨by simp, Or.inl ⟨u, e, rfl, rfl, hm⟩⟩
      · exact ⟨by simp, Or.inr ⟨u, e, rfl, rfl, hm⟩⟩
  set Inc : SimpleGraph (Fin (q + ec)) :=
    IncAux.comap ⇑finSumFinEquiv.symm with hInc
  have hIncAdj' : ∀ a b : Fin (q + ec), Inc.Adj a b ↔
      IncAux.Adj (finSumFinEquiv.symm a) (finSumFinEquiv.symm b) :=
    fun a b => Iff.rfl
  have hmem : bipartiteGraphs (q + ec) Inc := by
    refine ⟨fun i => (finSumFinEquiv.symm i).isLeft, ?_⟩
    intro u v huv
    rcases (hIncAdj _ _).1 ((hIncAdj' u v).1 huv) with
      ⟨u', e', h1, h2, -⟩ | ⟨u', e', h1, h2, -⟩
    · simp [h1, h2]
    · simp [h1, h2]
  set f : Fin q ↪ Fin (q + ec) :=
    ⟨fun u => finSumFinEquiv (Sum.inl u),
      fun u w hh =>
        Sum.inl_injective (finSumFinEquiv.injective hh)⟩ with hf
  set colors : Fin 2 → Set (Fin (q + ec)) :=
    ![Set.range ⇑f,
      Set.range fun e : Fin ec => finSumFinEquiv (Sum.inr e)] with hcolors
  refine ⟨q + ec, Inc.structure, ⟨Inc, hmem, rfl⟩, colors, f, ?_, ?_⟩
  · intro x
    letI := Inc.structure
    letI := colorStructure colors
    change x ∈ Set.range ⇑f ↔ x ∈ colors 0
    rw [hcolors]
    simp
  · intro r R v
    cases R with
    | adj =>
      change H.Adj (v 0) (v 1) ↔
        RealizeIn Inc.structure colors incidenceAdjFormula (⇑f ∘ v)
      have hfv : ⇑f ∘ v = ![f (v 0), f (v 1)] := by
        funext i
        fin_cases i <;> rfl
      rw [hfv, realizeIn_incidenceAdjFormula]
      have hsymm_f : ∀ u : Fin q,
          finSumFinEquiv.symm (f u) = Sum.inl u := fun u =>
        Equiv.symm_apply_apply _ _
      have hsymm_e : ∀ e : Fin ec,
          finSumFinEquiv.symm
              (finSumFinEquiv (Sum.inr e : Fin q ⊕ Fin ec)) =
            Sum.inr e := fun e => Equiv.symm_apply_apply _ _
      have hcol1 : ∀ z : Fin (q + ec), z ∈ colors 1 ↔
          ∃ e : Fin ec, finSumFinEquiv (Sum.inr e) = z := by
        intro z
        rw [hcolors]
        simp
      constructor
      · intro hadj
        have hedge : s(v 0, v 1) ∈ H.edgeFinset :=
          SimpleGraph.mem_edgeFinset.2 hadj
        set e₀ : Fin ec := H.edgeFinset.equivFin ⟨_, hedge⟩ with he₀
        have hσe₀ : σ e₀ = s(v 0, v 1) := by
          rw [hσ, he₀]
          simp
        refine ⟨fun hh => hadj.ne (f.injective hh),
          finSumFinEquiv (Sum.inr e₀), (hcol1 _).2 ⟨e₀, rfl⟩, ?_, ?_⟩
        · rw [hIncAdj', hsymm_e, hsymm_f, hIncAdj]
          exact Or.inr ⟨v 0, e₀, rfl, rfl,
            hσe₀ ▸ Sym2.mem_mk_left (v 0) (v 1)⟩
        · rw [hIncAdj', hsymm_e, hsymm_f, hIncAdj]
          exact Or.inr ⟨v 1, e₀, rfl, rfl,
            hσe₀ ▸ Sym2.mem_mk_right (v 0) (v 1)⟩
      · rintro ⟨hne, z, hz1, hadj0, hadj1⟩
        obtain ⟨e, rfl⟩ := (hcol1 z).1 hz1
        have hm0 : v 0 ∈ σ e := by
          rcases (hIncAdj _ _).1 ((hIncAdj' _ _).1 hadj0) with
            ⟨u', e', h1, -, -⟩ | ⟨u', e', h1, h2, hm⟩
          · rw [hsymm_e] at h1
            exact absurd h1 (by simp)
          · rw [hsymm_f] at h1
            rw [hsymm_e] at h2
            obtain rfl := Sum.inl_injective h1
            obtain rfl := Sum.inr_injective h2
            exact hm
        have hm1 : v 1 ∈ σ e := by
          rcases (hIncAdj _ _).1 ((hIncAdj' _ _).1 hadj1) with
            ⟨u', e', h1, -, -⟩ | ⟨u', e', h1, h2, hm⟩
          · rw [hsymm_e] at h1
            exact absurd h1 (by simp)
          · rw [hsymm_f] at h1
            rw [hsymm_e] at h2
            obtain rfl := Sum.inl_injective h1
            obtain rfl := Sum.inr_injective h2
            exact hm
        have hne' : v 0 ≠ v 1 := fun hh => hne (congrArg ⇑f hh)
        have hs : σ e = s(v 0, v 1) :=
          (Sym2.mem_and_mem_iff hne').1 ⟨hm0, hm1⟩
        have := hσmem e
        rw [hs, SimpleGraph.mem_edgeFinset] at this
        exact this

/-! ## The star-crossing transduction -/

/-- The star-crossing transduction (Mählmann §2, star case): a graph
class containing, for a fixed `ℓ ≥ 1`, induced exact `ℓ`-subdivided
bicliques of every order transduces the class of all graphs. -/
theorem transduces_allGraphs_of_isIndContained_subdividedBiclique
    {C : GraphClass} {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (h : ∀ m : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧
      (subdividedBiclique m ℓ).IsIndContained G) :
    Lax5.GraphTransductions.Transduces C allGraphs :=
  TransductionCalculus.Transduces.trans (transduces_bipartiteGraphs hℓ h)
    bipartiteGraphs_transduces_allGraphs

end Lax5Proofs.CrossingTransduction
