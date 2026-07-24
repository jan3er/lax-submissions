import Lax5.Transductions

/-!
The slice of transduction calculus the Appendix-A machinery needs: the
image class of a fixed transduction, monotonicity of the transduces
relation in both arguments, and composition (transitivity). Composition
carries the main content: formula substitution through a transduction,
with quantifiers relativized to the intermediate domain.
-/

namespace Lax5Proofs.TransductionCalculus

open FirstOrder Lax5.Transductions

universe u v u' v' u'' v''

variable {L : Language.{u, v}} {L' : Language.{u', v'}}
  {L'' : Language.{u'', v''}}

/-- The class of all structures produced by the transduction `T` from
colored members of `C` — the inner condition of `Transduces`, packaged
as a class. -/
def transductionImage [L'.IsRelational] (T : Transduction L L')
    (C : StructureClass L) : StructureClass L' :=
  fun m N => ∃ (n : ℕ) (M : L.Structure (Fin n)), C n M ∧
    ∃ (colors : Fin T.colors → Set (Fin n)) (g : Fin m ↪ Fin n),
      (∀ x : Fin n,
        x ∈ Set.range g ↔ RealizeIn M colors T.domain ![x]) ∧
      ∀ {r : ℕ} (R : L'.Relations r) (v : Fin r → Fin m),
        N.RelMap R v ↔ RealizeIn M colors (T.rel R) (g ∘ v)

/-- A class transduces the image class of any fixed transduction. -/
theorem transduces_transductionImage [L'.IsRelational]
    (T : Transduction L L') (C : StructureClass L) :
    Transduces C (transductionImage T C) :=
  ⟨T, fun _ _ hN => hN⟩

/-- Shrinking the target class preserves the transduces relation. -/
theorem Transduces.mono_target [L'.IsRelational] {C : StructureClass L}
    {D D' : StructureClass L'} (h : Transduces C D)
    (hsub : ∀ m N, D' m N → D m N) : Transduces C D' :=
  let ⟨T, hT⟩ := h
  ⟨T, fun m N hN => hT m N (hsub m N hN)⟩

/-- Growing the source class preserves the transduces relation. -/
theorem Transduces.mono_source [L'.IsRelational] {C C' : StructureClass L}
    {D : StructureClass L'} (h : Transduces C D)
    (hsub : ∀ n M, C n M → C' n M) : Transduces C' D := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun m N hN => ?_⟩
  obtain ⟨n, M, hM, rest⟩ := hT m N hN
  exact ⟨n, M, hsub n M hM, rest⟩

/-! ## Formula composition -/

/-- Include the first block of colors into a sum of two color blocks. -/
private def firstColorHom (c₁ c₂ : ℕ) :
    colorLanguage c₁ →ᴸ colorLanguage (c₁ + c₂) where
  onFunction := fun {m} (f : (colorLanguage c₁).Functions m) => f.elim
  onRelation := fun {m} (R : ColorRel c₁ m) => match R with
    | .color i => .color (i.castAdd c₂)

/-- Regard a formula using the first transduction's colors as a formula
using both blocks of colors. -/
private def liftFirstColors {c₁ : ℕ} (c₂ : ℕ) {α : Type*}
    (φ : (withColors L c₁).Formula α) :
    (withColors L (c₁ + c₂)).Formula α :=
  (Language.LHom.sumMap (Language.LHom.id L) (firstColorHom c₁ c₂)).onFormula φ

/-- Every term of a relational language is a variable. -/
private def relationalTermVar (K : Language) [K.IsRelational] {α : Type*} :
    K.Term α → α
  | .var x => x
  | .func f _ => isEmptyElim f

/-- Translate a formula of the second transduction back through the first.
Universal quantifiers are relativized to the first transduction's domain;
the second block of colors is kept as a fresh block after the first. -/
private noncomputable def composeBounded [L'.IsRelational]
    (T₁ : Transduction L L') (c₂ : ℕ) :
    ∀ {α : Type*} {q : ℕ},
      (withColors L' c₂).BoundedFormula α q →
        (withColors L (T₁.colors + c₂)).BoundedFormula α q
  | _, _, .falsum => .falsum
  | _, _, .equal t₁ t₂ =>
      .equal (.var (relationalTermVar _ t₁)) (.var (relationalTermVar _ t₂))
  | _, _, .rel (Sum.inl R) ts =>
      Language.BoundedFormula.relabel (β := _) (n := _)
        (fun i => relationalTermVar _ (ts i))
        (liftFirstColors c₂ (T₁.rel R))
  | _, _, .rel (Sum.inr (.color i)) ts =>
      .rel (Sum.inr (.color (i.natAdd T₁.colors))) fun j =>
        .var (relationalTermVar _ (ts j))
  | _, _, .imp φ ψ =>
      .imp (composeBounded T₁ c₂ φ) (composeBounded T₁ c₂ ψ)
  | α, q, .all φ =>
      .all (.imp
        (Language.BoundedFormula.relabel (β := α) (n := q + 1)
          (fun _ => Sum.inr (Fin.last q))
          (liftFirstColors c₂ T₁.domain))
        (composeBounded T₁ c₂ φ))

/-- The syntactic composite of two non-copying transductions. -/
private noncomputable def Transduction.comp [L'.IsRelational]
    (T₁ : Transduction L L')
    (T₂ : Transduction L' L'') : Transduction L L'' where
  colors := T₁.colors + T₂.colors
  domain := (liftFirstColors T₂.colors T₁.domain) ⊓
    composeBounded T₁ T₂.colors T₂.domain
  rel R := composeBounded T₁ T₂.colors (T₂.rel R)

private theorem realize_liftFirstColors {c₁ c₂ n : ℕ}
    (M : L.Structure (Fin n))
    (colors₁ : Fin c₁ → Set (Fin n)) (colors₂ : Fin c₂ → Set (Fin n))
    {α : Type*} (φ : (withColors L c₁).Formula α) (v : α → Fin n) :
    RealizeIn M (Fin.append colors₁ colors₂) (liftFirstColors c₂ φ) v ↔
      RealizeIn M colors₁ φ v := by
  letI := M
  letI := colorStructure (Fin.append colors₁ colors₂)
  letI := colorStructure colors₁
  haveI : (firstColorHom c₁ c₂).IsExpansionOn (Fin n) :=
    ⟨fun f => f.elim, fun R x => by
      cases R with
      | color i =>
        simpa only [firstColorHom, colorStructure] using
          congrFun (Fin.append_left colors₁ colors₂ i) (x 0)⟩
  exact Language.LHom.realize_onFormula
    (Language.LHom.sumMap (Language.LHom.id L) (firstColorHom c₁ c₂)) φ

private def RealizeBoundedIn {K : Language} {n c q : ℕ}
    (M : K.Structure (Fin n)) (colors : Fin c → Set (Fin n))
    {α : Type*} (φ : (withColors K c).BoundedFormula α q)
    (v : α → Fin n) (xs : Fin q → Fin n) : Prop :=
  letI := M
  letI := colorStructure colors
  φ.Realize v xs

private theorem realize_relabel_formula_in {K : Language} {n c q : ℕ}
    (M : K.Structure (Fin n)) (colors : Fin c → Set (Fin n))
    {α β : Type*} (φ : (withColors K c).Formula α)
    (r : α → β ⊕ Fin q) (v : β → Fin n) (xs : Fin q → Fin n) :
    RealizeBoundedIn M colors
        (Language.BoundedFormula.relabel r φ) v xs ↔
      RealizeIn M colors φ (Sum.elim v xs ∘ r) := by
  letI := M
  letI := colorStructure colors
  unfold RealizeBoundedIn RealizeIn
  rw [Language.BoundedFormula.realize_relabel,
    Language.Formula.boundedFormula_realize_eq_realize]
  simp

private theorem realize_imp_in {K : Language} {n c q : ℕ}
    (M : K.Structure (Fin n)) (colors : Fin c → Set (Fin n))
    {α : Type*} (φ ψ : (withColors K c).BoundedFormula α q)
    (v : α → Fin n) (xs : Fin q → Fin n) :
    RealizeBoundedIn M colors (.imp φ ψ) v xs ↔
      (RealizeBoundedIn M colors φ v xs →
        RealizeBoundedIn M colors ψ v xs) := by
  unfold RealizeBoundedIn
  rfl

private theorem realize_all_in {K : Language} {n c q : ℕ}
    (M : K.Structure (Fin n)) (colors : Fin c → Set (Fin n))
    {α : Type*} (φ : (withColors K c).BoundedFormula α (q + 1))
    (v : α → Fin n) (xs : Fin q → Fin n) :
    RealizeBoundedIn M colors (.all φ) v xs ↔
      ∀ x : Fin n, RealizeBoundedIn M colors φ v (Fin.snoc xs x) := by
  unfold RealizeBoundedIn
  rfl

private theorem realize_inf_formula_in {K : Language} {n c : ℕ}
    (M : K.Structure (Fin n)) (colors : Fin c → Set (Fin n))
    {α : Type*} (φ ψ : (withColors K c).Formula α) (v : α → Fin n) :
    RealizeIn M colors (φ ⊓ ψ) v ↔
      RealizeIn M colors φ v ∧ RealizeIn M colors ψ v := by
  letI := M
  letI := colorStructure colors
  unfold RealizeIn
  exact Language.Formula.realize_inf

private theorem relationalTermVar_realize (K : Language) [K.IsRelational]
    {X α : Type*} [K.Structure X] (t : K.Term α) (v : α → X) :
    t.realize v = v (relationalTermVar K t) := by
  cases t with
  | var x => rfl
  | func f _ => exact isEmptyElim f

private theorem realize_color_in {K : Language} {n c q : ℕ}
    (M : K.Structure (Fin n)) (colors : Fin c → Set (Fin n))
    [K.IsRelational] {α : Type*} (i : Fin c)
    (ts : Fin 1 → (withColors K c).Term (α ⊕ Fin q))
    (v : α → Fin n) (xs : Fin q → Fin n) :
    RealizeBoundedIn M colors (.rel (Sum.inr (.color i)) ts) v xs ↔
      Sum.elim v xs (relationalTermVar _ (ts 0)) ∈ colors i := by
  letI := M
  letI := colorStructure colors
  unfold RealizeBoundedIn
  change (ts 0).realize (Sum.elim v xs) ∈ colors i ↔ _
  rw [relationalTermVar_realize]

private theorem realize_color_var_in {K : Language} {n c q : ℕ}
    (M : K.Structure (Fin n)) (colors : Fin c → Set (Fin n))
    {α : Type*} (i : Fin c) (a : Fin 1 → α ⊕ Fin q)
    (v : α → Fin n) (xs : Fin q → Fin n) :
    RealizeBoundedIn M colors
        (.rel (Sum.inr (.color i)) fun j => .var (a j)) v xs ↔
      Sum.elim v xs (a 0) ∈ colors i := by
  letI := M
  letI := colorStructure colors
  unfold RealizeBoundedIn
  rfl

private theorem realize_composeBounded [L'.IsRelational]
    (T₁ : Transduction L L') {n m : ℕ}
    (M : L.Structure (Fin n)) (N : L'.Structure (Fin m))
    (colors₁ : Fin T₁.colors → Set (Fin n)) {c₂ : ℕ}
    (colors₂ : Fin c₂ → Set (Fin m)) (g : Fin m ↪ Fin n)
    (hdom : ∀ x : Fin n,
      x ∈ Set.range g ↔ RealizeIn M colors₁ T₁.domain ![x])
    (hrel : ∀ {r : ℕ} (R : L'.Relations r) (v : Fin r → Fin m),
      N.RelMap R v ↔ RealizeIn M colors₁ (T₁.rel R) (g ∘ v)) :
    ∀ {α : Type*} {q : ℕ}
      (φ : (withColors L' c₂).BoundedFormula α q)
      (v : α → Fin m) (xs : Fin q → Fin m),
      RealizeBoundedIn M
          (Fin.append colors₁ (fun i => g '' colors₂ i))
          (composeBounded T₁ c₂ φ) (g ∘ v) (g ∘ xs) ↔
        RealizeBoundedIn N colors₂ φ v xs := by
  intro α q φ
  induction φ with
  | falsum =>
      intro v xs
      simp only [composeBounded, RealizeBoundedIn,
        Language.BoundedFormula.Realize]
  | equal t₁ t₂ =>
      intro v xs
      letI := N
      letI := colorStructure colors₂
      simp only [composeBounded, RealizeBoundedIn,
        Language.BoundedFormula.Realize]
      have hcomp : Sum.elim (g ∘ v) (g ∘ xs) =
          g ∘ Sum.elim v xs := by
        funext z
        cases z <;> rfl
      rw [hcomp]
      simp only [Language.Term.realize, Function.comp_apply]
      change g ((Sum.elim v xs) (relationalTermVar _ t₁)) =
          g ((Sum.elim v xs) (relationalTermVar _ t₂)) ↔
        t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
      rw [relationalTermVar_realize _ t₁ (Sum.elim v xs),
        relationalTermVar_realize _ t₂ (Sum.elim v xs)]
      exact g.injective.eq_iff
  | rel R ts =>
      rcases R with R | R
      · intro v xs
        simp only [composeBounded]
        let args : Fin _ → Fin m := fun i =>
          Sum.elim v xs (relationalTermVar _ (ts i))
        calc
          _ ↔ RealizeIn M
                (Fin.append colors₁ (fun i => g '' colors₂ i))
                (liftFirstColors c₂ (T₁.rel R)) (g ∘ args) := by
              rw [realize_relabel_formula_in]
              have hv :
                  Sum.elim (g ∘ v) (g ∘ xs) ∘
                      (fun i => relationalTermVar _ (ts i)) =
                    g ∘ args := by
                funext i
                change Sum.elim (g ∘ v) (g ∘ xs)
                    (relationalTermVar _ (ts i)) = g (args i)
                unfold args
                cases relationalTermVar _ (ts i) <;> rfl
              rw [hv]
          _ ↔ RealizeIn M colors₁ (T₁.rel R) (g ∘ args) :=
            realize_liftFirstColors M colors₁
              (fun i => g '' colors₂ i) (T₁.rel R) (g ∘ args)
          _ ↔ N.RelMap R args := (hrel R args).symm
          _ ↔ RealizeBoundedIn N colors₂
                (.rel (Sum.inl R) ts) v xs := by
              letI := N
              letI := colorStructure colors₂
              unfold RealizeBoundedIn
              change N.RelMap R args ↔
                N.RelMap R (fun i => (ts i).realize (Sum.elim v xs))
              apply iff_of_eq
              congr 1
              funext i
              exact (relationalTermVar_realize _ (ts i)
                (Sum.elim v xs)).symm
      · cases R with
        | color i =>
          intro v xs
          simp only [composeBounded]
          rw [realize_color_var_in, realize_color_in]
          simp only [relationalTermVar, Fin.append_right]
          let a := relationalTermVar (withColors L' c₂) (ts 0)
          have heq : Sum.elim (g ∘ v) (g ∘ xs) a =
              g (Sum.elim v xs a) := by
            cases a <;> rfl
          change Sum.elim (g ∘ v) (g ∘ xs) a ∈ g '' colors₂ i ↔
            Sum.elim v xs a ∈ colors₂ i
          rw [heq]
          constructor
          · rintro ⟨z, hz, hgz⟩
            exact (g.injective hgz) ▸ hz
          · exact fun hz => ⟨_, hz, rfl⟩
  | imp φ ψ ihφ ihψ =>
      intro v xs
      simp only [composeBounded, RealizeBoundedIn,
        Language.BoundedFormula.Realize]
      change (RealizeBoundedIn M _ (composeBounded T₁ c₂ φ)
          (g ∘ v) (g ∘ xs) →
        RealizeBoundedIn M _ (composeBounded T₁ c₂ ψ)
          (g ∘ v) (g ∘ xs)) ↔
        (RealizeBoundedIn N colors₂ φ v xs →
          RealizeBoundedIn N colors₂ ψ v xs)
      rw [ihφ v xs, ihψ v xs]
  | @all q' φ ih =>
      intro v xs
      let combined := Fin.append colors₁ (fun i => g '' colors₂ i)
      let guard := Language.BoundedFormula.relabel (β := α) (n := q' + 1)
        (fun _ => Sum.inr (Fin.last q'))
        (liftFirstColors c₂ T₁.domain)
      simp only [composeBounded]
      rw [realize_all_in, realize_all_in]
      simp only [realize_imp_in]
      have hguard (x : Fin n) :
          RealizeBoundedIn M combined guard (g ∘ v)
              (Fin.snoc (g ∘ xs) x) ↔
            RealizeIn M colors₁ T₁.domain ![x] := by
        unfold guard combined
        rw [realize_relabel_formula_in]
        have hv :
            Sum.elim (g ∘ v) (Fin.snoc (g ∘ xs) x) ∘
                (fun _ : Fin 1 => Sum.inr (Fin.last q')) = ![x] := by
          funext i
          have hi : i = 0 := Fin.eq_zero i
          subst i
          simp
        rw [hv]
        exact realize_liftFirstColors M colors₁
          (fun i => g '' colors₂ i) T₁.domain ![x]
      have hsnoc (y : Fin m) :
          Fin.snoc (g ∘ xs) (g y) = g ∘ Fin.snoc xs y := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp
      constructor
      · intro hall y
        have hgy : RealizeBoundedIn M combined guard (g ∘ v)
            (Fin.snoc (g ∘ xs) (g y)) :=
          (hguard (g y)).2 ((hdom (g y)).1 ⟨y, rfl⟩)
        have hout := hall (g y) hgy
        rw [hsnoc y] at hout
        exact (ih v (Fin.snoc xs y)).1 hout
      · intro hall x hx
        have hxrange : x ∈ Set.range g :=
          (hdom x).2 ((hguard x).1 hx)
        obtain ⟨y, rfl⟩ := hxrange
        rw [hsnoc y]
        exact (ih v (Fin.snoc xs y)).2 (hall y)

private theorem realize_composeFormula [L'.IsRelational]
    (T₁ : Transduction L L') {n m : ℕ}
    (M : L.Structure (Fin n)) (N : L'.Structure (Fin m))
    (colors₁ : Fin T₁.colors → Set (Fin n)) {c₂ : ℕ}
    (colors₂ : Fin c₂ → Set (Fin m)) (g : Fin m ↪ Fin n)
    (hdom : ∀ x : Fin n,
      x ∈ Set.range g ↔ RealizeIn M colors₁ T₁.domain ![x])
    (hrel : ∀ {r : ℕ} (R : L'.Relations r) (v : Fin r → Fin m),
      N.RelMap R v ↔ RealizeIn M colors₁ (T₁.rel R) (g ∘ v))
    {α : Type*} (φ : (withColors L' c₂).Formula α) (v : α → Fin m) :
    RealizeIn M (Fin.append colors₁ (fun i => g '' colors₂ i))
        (composeBounded T₁ c₂ φ) (g ∘ v) ↔
      RealizeIn N colors₂ φ v := by
  have h := realize_composeBounded T₁ M N colors₁ colors₂ g hdom hrel
    φ v (default : Fin 0 → Fin m)
  unfold RealizeBoundedIn at h
  unfold RealizeIn
  simpa only [Language.Formula.Realize,
    Subsingleton.elim (g ∘ (default : Fin 0 → Fin m))
      (default : Fin 0 → Fin n)] using h

/-- Transitivity of the transduces relation: composition of
transductions. Substituting the interpreting formulas of the first
transduction through the formulas of the second, with the second's
colors carried as guessed unary predicates on the source. The workhorse
of the calculus. -/
theorem Transduces.trans [L'.IsRelational] [L''.IsRelational]
    {C : StructureClass L} {D : StructureClass L'} {E : StructureClass L''}
    (h₁ : Transduces C D) (h₂ : Transduces D E) : Transduces C E := by
  obtain ⟨T₁, hT₁⟩ := h₁
  obtain ⟨T₂, hT₂⟩ := h₂
  refine ⟨Lax5Proofs.TransductionCalculus.Transduction.comp T₁ T₂,
    fun p P hP => ?_⟩
  obtain ⟨m, N, hN, colors₂, g₂, hdom₂, hrel₂⟩ := hT₂ p P hP
  obtain ⟨n, M, hM, colors₁, g₁, hdom₁, hrel₁⟩ := hT₁ m N hN
  let combined : Fin (T₁.colors + T₂.colors) → Set (Fin n) :=
    Fin.append colors₁ (fun i => g₁ '' colors₂ i)
  let g : Fin p ↪ Fin n := g₂.trans g₁
  refine ⟨n, M, hM, combined, g, ?_, ?_⟩
  · intro x
    have hfirst :
        RealizeIn M combined (liftFirstColors T₂.colors T₁.domain) ![x] ↔
          RealizeIn M colors₁ T₁.domain ![x] := by
      unfold combined
      exact realize_liftFirstColors M colors₁
        (fun i => g₁ '' colors₂ i) T₁.domain ![x]
    have hand :
        RealizeIn M combined
            ((liftFirstColors T₂.colors T₁.domain) ⊓
              composeBounded T₁ T₂.colors T₂.domain) ![x] ↔
          RealizeIn M combined (liftFirstColors T₂.colors T₁.domain) ![x] ∧
            RealizeIn M combined (composeBounded T₁ T₂.colors T₂.domain)
              ![x] := by
      exact realize_inf_formula_in M combined _ _ ![x]
    change x ∈ Set.range g ↔
      RealizeIn M combined
        ((liftFirstColors T₂.colors T₁.domain) ⊓
          composeBounded T₁ T₂.colors T₂.domain) ![x]
    rw [hand, hfirst]
    constructor
    · rintro ⟨z, rfl⟩
      have h₁range : g₁ (g₂ z) ∈ Set.range g₁ := ⟨g₂ z, rfl⟩
      refine ⟨(hdom₁ _).1 h₁range, ?_⟩
      have hcomp := (realize_composeFormula T₁ M N colors₁ colors₂ g₁
        hdom₁ hrel₁ T₂.domain ![g₂ z]).2
          ((hdom₂ (g₂ z)).1 ⟨z, rfl⟩)
      have hv : g₁ ∘ ![g₂ z] = ![g₁ (g₂ z)] := by
        funext i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        rfl
      unfold combined
      rw [hv] at hcomp
      exact hcomp
    · rintro ⟨hx₁, hx₂⟩
      obtain ⟨y, hy⟩ := (hdom₁ x).2 hx₁
      have hv : g₁ ∘ ![y] = ![x] := by
        funext i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simpa using hy
      have hcomp := (realize_composeFormula T₁ M N colors₁ colors₂ g₁
        hdom₁ hrel₁ T₂.domain ![y]).1
      unfold combined at hx₂
      rw [hv] at hcomp
      have hy₂ := hcomp hx₂
      obtain ⟨z, hz⟩ := (hdom₂ y).2 hy₂
      refine ⟨z, ?_⟩
      change g₁ (g₂ z) = x
      rw [hz, hy]
  · intro r R v
    change P.RelMap R v ↔
      RealizeIn M combined (composeBounded T₁ T₂.colors (T₂.rel R))
        (g ∘ v)
    calc
      P.RelMap R v ↔ RealizeIn N colors₂ (T₂.rel R) (g₂ ∘ v) :=
        hrel₂ R v
      _ ↔ RealizeIn M
          (Fin.append colors₁ (fun i => g₁ '' colors₂ i))
          (composeBounded T₁ T₂.colors (T₂.rel R))
          (g₁ ∘ (g₂ ∘ v)) :=
        (realize_composeFormula T₁ M N colors₁ colors₂ g₁
          hdom₁ hrel₁ (T₂.rel R) (g₂ ∘ v)).symm
      _ ↔ RealizeIn M combined
          (composeBounded T₁ T₂.colors (T₂.rel R)) (g ∘ v) := by
        unfold combined g
        have hv : g₁ ∘ (g₂ ∘ v) = (g₂.trans g₁ : Fin p → Fin n) ∘ v := by
          funext i
          rfl
        rw [hv]

end Lax5Proofs.TransductionCalculus
