import Lax13Proofs.Refine.Iicf.Intf.Set
import Lax13Proofs.Refine.NREST.Foreach

/-!
# Matrix interface and finite pointwise implementations

Source-faithful semantic leaf for `IICF/Intf/IICF_Matrix.thy` at
`isabelle_llvm_time` commit `42dd7f5`.

## Source accounting

| Active source item | Lean disposition |
|---|---|
| `mtx_rel`, `mtx_rel_id`, `i_mtx`, inference | `mtxRel`, `mtxRel_diagonal`, `MatrixI`, `mtxRel_intf` |
| five operations `new/copy/get/set/nonzero` | exactly five cost-silent `sepref_decl_op`s below |
| `IS_ID A` on `nonzero` | its fref is intentionally diagonal-only; no stronger arbitrary relation theorem is registered |
| get/set patterns | explicit operation definitions plus `fold_op_mtx_get/set` |
| initializer frame-match rule | the Isabelle rule changes `hn_val` through `the_pure (pure A)`; those wrappers have no Lean SL counterpart, so the diagonal initializer fref is the exact usable boundary |
| `pointwise_op` and `pointwise_fun_fold` | `pointwise_upd_fold`, `pointwise_fun_fold` |
| product/divmod and fold/nfold conversions | `matrixGrid_divmod`, `foldGrid_divmod`, `nfoldGrid_divmod` |
| nonzero cases/bounds | `mtxNonzero_cases`, `mtxNonzeroD_left/right` |
| unary pointwise locale | semantic definition, locality hypotheses, finite fold equality and NRest refinement |
| binary pointwise locale | semantic definition, locality hypothesis, finite fold equality and NRest refinement |
| comparison pointwise locale | semantic definition, zero bounds, finite-grid implementation and NRest refinement |
| three `*_gen_impl` locales and generated concrete definitions | their portable conclusions are the three NRest refinements here; Isabelle's polymorphic `Heap`, `rdomp`, `nbn_assn`, `concrete_definition`, and `prepare_code_thms` have no directly supported generic analogue in the current Lean refinement/SL layer, so no fake concrete declarations are emitted |

The source pattern and generic-locale registrations are therefore accounted
for without cloning Isabelle-only term-pattern or code-generator machinery.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

variable {α β σ : Type}

/-! ## Relation and interface -/

abbrev Matrix (α : Type) := ℕ × ℕ → α

/-- Source `⟨A⟩mtx_rel = nat_rel × nat_rel → A`. -/
def mtxRel (A : Set (α × β)) : Set (Matrix α × Matrix β) :=
  (Set.diagonal ℕ ×ᵣ Set.diagonal ℕ) →ᵣ A

@[simp] theorem mtxRel_diagonal :
    mtxRel (Set.diagonal α) = Set.diagonal (Matrix α) := by
  apply Set.Subset.antisymm
  · rintro ⟨m, n⟩ h
    change m = n
    funext p
    exact h p p ⟨rfl, rfl⟩
  · rintro ⟨m, n⟩ h
    change m = n at h
    subst n
    intro p q hpq
    rcases p with ⟨i, j⟩
    rcases q with ⟨k, l⟩
    obtain ⟨hik, hjl⟩ := hpq
    change i = k at hik
    change j = l at hjl
    subst k
    subst l
    rfl

sepref_decl_intf (α) MatrixI is Matrix α

@[intf_of_rel] theorem mtxRel_intf (A : Set (α × β)) :
    intfOfRel (mtxRel A) (MatrixI β) := trivial

#guard_rel_interface (mtxRel (Set.diagonal ℕ)) is MatrixI ℕ

/-! ## Five source operations -/

sepref_decl_op mtx_new (α : Type) : Matrix α → NRest (Matrix α) ECost :=
    fun m => NRest.returnT m
  interface := ∀ α : Type, (ℕ × ℕ → α) → NRest (MatrixI α) ECost
  precondition := fun _ : Matrix α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_mtx_new α, op_mtx_new β) ∈
        fref (fun _ : Matrix β => True)
          ((Set.diagonal ℕ ×ᵣ Set.diagonal ℕ) →ᵣ A)
          (fun _ => NRest.nrestRel (mtxRel A))) := by
    intro β A m n _ h
    exact NRest.param_returnT h

sepref_decl_op mtx_copy (α : Type) : Matrix α → NRest (Matrix α) ECost :=
    fun m => NRest.returnT m
  interface := ∀ α : Type, MatrixI α → NRest (MatrixI α) ECost
  precondition := fun _ : Matrix α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_mtx_copy α, op_mtx_copy β) ∈
        fref (fun _ : Matrix β => True) (mtxRel A)
          (fun _ => NRest.nrestRel (mtxRel A))) := by
    intro β A m n _ h
    exact NRest.param_returnT h

sepref_decl_op mtx_get (α : Type) : Matrix α → (ℕ × ℕ) → NRest α ECost :=
    fun m ij => NRest.returnT (m ij)
  interface := ∀ α : Type, MatrixI α → (ℕ × ℕ) → NRest α ECost
  precondition := fun _ : Matrix α => fun _ : ℕ × ℕ => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_mtx_get α, op_mtx_get β) ∈
        fref (fun _ : Matrix β => True) (mtxRel A)
          (fun _ => (Set.diagonal ℕ ×ᵣ Set.diagonal ℕ) →ᵣ
            NRest.nrestRel A)) := by
    intro β A m n _ h ij kl hidx
    exact NRest.param_returnT (h ij kl hidx)

sepref_decl_op mtx_set (α : Type) :
    Matrix α → (ℕ × ℕ) → α → NRest (Matrix α) ECost :=
    fun m ij x => NRest.returnT (Function.update m ij x)
  interface := ∀ α : Type,
    MatrixI α → (ℕ × ℕ) → α → NRest (MatrixI α) ECost
  precondition := fun _ : Matrix α => fun _ : ℕ × ℕ => fun _ : α => True
  parametricity : ∀ {β : Type} (A : Set (α × β)),
      ((op_mtx_set α, op_mtx_set β) ∈
        fref (fun _ : Matrix β => True) (mtxRel A)
          (fun _ => (Set.diagonal ℕ ×ᵣ Set.diagonal ℕ) →ᵣ
            A →ᵣ NRest.nrestRel (mtxRel A))) := by
    intro β A m n _ h ij kl hidx x y hxy
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨k, l⟩
    obtain ⟨hik, hjl⟩ := hidx
    change i = k at hik
    change j = l at hjl
    subst k
    subst l
    apply NRest.param_returnT
    intro p q hpq
    rcases p with ⟨a, b⟩
    rcases q with ⟨c, d⟩
    obtain ⟨hac, hbd⟩ := hpq
    change a = c at hac
    change b = d at hbd
    subst c
    subst d
    by_cases he : (a, b) = (i, j)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      simpa using hxy
    · simp only [Function.update_apply, if_neg he]
      exact h (a, b) (a, b) ⟨rfl, rfl⟩

/-- Source support set of entries unequal to zero. -/
def mtxNonzero [Zero α] (m : Matrix α) : Set (ℕ × ℕ) :=
  {ij | m ij ≠ 0}

sepref_decl_op mtx_nonzero (α : Type) [Zero α] :
    Matrix α → NRest (Set (ℕ × ℕ)) ECost :=
    fun m => NRest.returnT (mtxNonzero m)
  interface := ∀ α : Type, [Zero α] →
    MatrixI α → NRest (SetI (ℕ × ℕ)) ECost
  precondition := fun _ : Matrix α => True
  parametricity :
      ((op_mtx_nonzero α, op_mtx_nonzero α) ∈
        fref (fun _ : Matrix α => True) (mtxRel (Set.diagonal α))
          (fun _ => NRest.nrestRel
            (setRel (Set.diagonal ℕ ×ᵣ Set.diagonal ℕ)))) := by
    intro m n _ h
    have heq : m = n := by simpa using h
    clear h
    subst n
    apply NRest.param_returnT
    constructor <;> intro p hp
    · exact ⟨p, hp, ⟨rfl, rfl⟩⟩
    · exact ⟨p, hp, ⟨rfl, rfl⟩⟩

/-! The source get/set pattern rules are definitional folds in Lean. -/

theorem fold_op_mtx_get (m : Matrix α) (ij : ℕ × ℕ) :
    op_mtx_get α m ij = NRest.returnT (m ij) := rfl

theorem fold_op_mtx_set (m : Matrix α) (ij : ℕ × ℕ) (x : α) :
    op_mtx_set α m ij x = NRest.returnT (Function.update m ij x) := rfl

/-! ## Finite grids and pointwise fold support -/

def matrixGrid (N M : ℕ) : List (ℕ × ℕ) :=
  List.product (List.range N) (List.range M)

@[simp] theorem mem_matrixGrid {N M : ℕ} {p : ℕ × ℕ} :
    p ∈ matrixGrid N M ↔ p.1 < N ∧ p.2 < M := by
  rcases p with ⟨i, j⟩
  simp [matrixGrid]

theorem matrixGrid_nodup (N M : ℕ) : (matrixGrid N M).Nodup := by
  exact List.Nodup.product List.nodup_range List.nodup_range

private theorem product_append_left (xs ys : List α) (zs : List β) :
    List.product (xs ++ ys) zs =
      List.product xs zs ++ List.product ys zs := by
  simp [List.product]

/-- Row-major product enumeration is the source's single div/mod range. -/
theorem matrixGrid_divmod (N M : ℕ) :
    matrixGrid N M =
      (List.range (M * N)).map (fun k => (k / M, k % M)) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [Nat.mul_succ, List.range_add, List.map_append]
      unfold matrixGrid
      rw [List.range_succ, product_append_left]
      change matrixGrid N M ++ List.product [N] (List.range M) = _
      rw [ih]
      congr 1
      rw [List.map_map]
      unfold List.product
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      change (List.range M).map (fun j => (N, j)) = _
      apply List.map_congr_left
      intro j hj
      have hjlt : j < M := List.mem_range.mp hj
      have hM : 0 < M := Nat.zero_lt_of_lt hjlt
      simp [Nat.mul_add_div hM, Nat.div_eq_of_lt hjlt,
        Nat.mod_eq_of_lt hjlt]

/-- Pure fold form of the source product/divmod conversion. -/
theorem foldGrid_divmod (N M : ℕ) (f : ℕ → ℕ → σ → σ) (s : σ) :
    (matrixGrid N M).foldl (fun s p => f p.1 p.2 s) s =
      (List.range (M * N)).foldl (fun s k => f (k / M) (k % M) s) s := by
  rw [matrixGrid_divmod]
  exact List.foldl_map

/-- `nfoldli` commutes with mapping the traversed list. -/
theorem nfoldli_map (c : σ → Bool) (f : α → σ → NRest σ ECost)
    (g : β → α) (xs : List β) (s : σ) :
    NRest.nfoldli c f (xs.map g) s =
      NRest.nfoldli c (fun x s => f (g x) s) xs s := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, NRest.nfoldli_cons]
      split
      · congr 1
        funext s'
        exact ih s'
      · rfl

/-- Monadic fold form of the source `nfoldli_prod_divmod_conv`. -/
theorem nfoldGrid_divmod (N M : ℕ) (c : σ → Bool)
    (f : ℕ → ℕ → σ → NRest σ ECost) (s : σ) :
    NRest.nfoldli c (fun p s => f p.1 p.2 s) (matrixGrid N M) s =
      NRest.nfoldli c (fun k s => f (k / M) (k % M) s)
        (List.range (M * N)) s := by
  rw [matrixGrid_divmod]
  exact nfoldli_map c (fun p s => f p.1 p.2 s)
    (fun k => (k / M, k % M)) _ s

/-- Pure nested-loop form of the product/divmod fold conversion. -/
theorem foldNested_divmod (N M : ℕ) (f : ℕ → ℕ → σ → σ) (s : σ) :
    (List.range N).foldl
        (fun s i => (List.range M).foldl (fun s j => f i j s) s) s =
      (List.range (M * N)).foldl
        (fun s k => f (k / M) (k % M) s) s := by
  rw [← foldGrid_divmod N M f s]
  simp [matrixGrid, List.product, List.foldl_flatMap, List.foldl_map]

/-- Interruptible monadic fold over a `flatMap` is the corresponding nested
interruptible fold. -/
theorem nfoldli_flatMap (c : σ → Bool) (f : β → σ → NRest σ ECost)
    (g : α → List β) (xs : List α) (s : σ) :
    NRest.nfoldli c f (xs.flatMap g) s =
      NRest.nfoldli c (fun x s => NRest.nfoldli c f (g x) s) xs s := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, NRest.nfoldli_append, NRest.nfoldli_cons]
      by_cases hc : c s = true
      · rw [if_pos hc]
        congr 1
        funext s'
        exact ih s'
      · have hcf : c s = false := Bool.eq_false_of_not_eq_true hc
        rw [if_neg hc, NRest.nfoldli_no_continue _ _ _ _ hcf,
          NRest.returnT_bindT,
          NRest.nfoldli_no_continue _ _ _ _ hcf]

/-- Nested monadic-loop form of the source's `nfoldli_prod_divmod_conv`. -/
theorem nfoldNested_divmod (N M : ℕ) (c : σ → Bool)
    (f : ℕ → ℕ → σ → NRest σ ECost) (s : σ) :
    NRest.nfoldli c
        (fun i s => NRest.nfoldli c (fun j s => f i j s)
          (List.range M) s)
        (List.range N) s =
      NRest.nfoldli c (fun k s => f (k / M) (k % M) s)
        (List.range (M * N)) s := by
  rw [← nfoldGrid_divmod N M c f s]
  unfold matrixGrid List.product
  rw [nfoldli_flatMap]
  congr 1
  funext i s'
  symm
  exact nfoldli_map c (fun p s => f p.1 p.2 s)
    (fun j => (i, j)) (List.range M) s'

/-- Generic source `pointwise_upd_fold`. -/
theorem pointwise_upd_fold {ρ τ : Type} [DecidableEq ρ]
    (f : ρ → σ → σ) (q : σ → ρ → τ)
    (h₁ : ∀ p p' s, p ≠ p' → q (f p s) p' = q s p')
    (h₂ : ∀ p p' s, p ≠ p' → q (f p (f p' s)) p = q (f p s) p)
    {ps : List ρ} (hnd : ps.Nodup) (s : σ) (p : ρ) :
    q (ps.foldl (fun s p => f p s) s) p =
      if p ∈ ps then q (f p s) p else q s p := by
  induction ps generalizing s with
  | nil => simp
  | cons a ps ih =>
      have ha : a ∉ ps := (List.nodup_cons.mp hnd).1
      have hps : ps.Nodup := (List.nodup_cons.mp hnd).2
      rw [List.foldl_cons, ih hps]
      by_cases hp : p ∈ ps
      · have hpa : p ≠ a := fun h => ha (h ▸ hp)
        simp [hp, hpa, h₂ p a s hpa]
      · by_cases hpa : p = a
        · subst a
          simp [hp]
        · have hap : a ≠ p := fun h => hpa h.symm
          simp [hp, hpa, h₁ a p s hap]

/-- Function-specialized source `pointwise_fun_fold`. -/
theorem pointwise_fun_fold {ρ τ : Type} [DecidableEq ρ]
    (f : ρ → (ρ → τ) → (ρ → τ))
    (h₁ : ∀ p p' s, p ≠ p' → f p s p' = s p')
    (h₂ : ∀ p p' s, p ≠ p' → f p (f p' s) p = f p s p)
    {ps : List ρ} (hnd : ps.Nodup) (s : ρ → τ) (p : ρ) :
    ps.foldl (fun s p => f p s) s p =
      if p ∈ ps then f p s p else s p :=
  pointwise_upd_fold f (fun s p => s p) h₁ h₂ hnd s p

/-! ## Nonzero support -/

theorem mtxNonzero_cases [Zero α] (m : Matrix α) (p : ℕ × ℕ) :
    p ∈ mtxNonzero m ∨ m p = 0 := by
  by_cases h : m p = 0
  · exact Or.inr h
  · exact Or.inl h

theorem mtxNonzeroD_left [Zero α] {m : Matrix α} {N M i j : ℕ}
    (hi : ¬ i < N) (hs : mtxNonzero m ⊆ {p | p.1 < N ∧ p.2 < M}) :
    m (i, j) = 0 := by
  by_contra h
  exact hi (hs h).1

theorem mtxNonzeroD_right [Zero α] {m : Matrix α} {N M i j : ℕ}
    (hj : ¬ j < M) (hs : mtxNonzero m ⊆ {p | p.1 < N ∧ p.2 < M}) :
    m (i, j) = 0 := by
  by_contra h
  exact hj (hs h).2

theorem mtx_zero_outside [Zero α] {m : Matrix α} {N M : ℕ}
    (hs : mtxNonzero m ⊆ {p | p.1 < N ∧ p.2 < M})
    {p : ℕ × ℕ} (hp : p ∉ matrixGrid N M) : m p = 0 := by
  rcases p with ⟨i, j⟩
  simp only [mem_matrixGrid, not_and_or] at hp
  exact hp.elim (fun hi => mtxNonzeroD_left hi hs)
    (fun hj => mtxNonzeroD_right hj hs)

/-! ## Unary pointwise operation -/

def mtxPointwiseUnop (f : (ℕ × ℕ) → α → α) (m : Matrix α) : Matrix α :=
  fun p => f p (m p)

def mtxUnopUpdate (f : (ℕ × ℕ) → α → α)
    (p : ℕ × ℕ) (m : Matrix α) : Matrix α :=
  Function.update m p (f p (m p))

def mtxUnopFold (N M : ℕ) (f : (ℕ × ℕ) → α → α)
    (m : Matrix α) : Matrix α :=
  (matrixGrid N M).foldl (fun m p => mtxUnopUpdate f p m) m

theorem mtxUnopUpdate_indep₁ (f : (ℕ × ℕ) → α → α)
    {p p' : ℕ × ℕ} (h : p ≠ p') (m : Matrix α) :
    mtxUnopUpdate f p m p' = m p' := by
  simp [mtxUnopUpdate, h.symm]

theorem mtxUnopUpdate_indep₂ (f : (ℕ × ℕ) → α → α)
    {p p' : ℕ × ℕ} (h : p ≠ p') (m : Matrix α) :
    mtxUnopUpdate f p (mtxUnopUpdate f p' m) p =
      mtxUnopUpdate f p m p := by
  simp [mtxUnopUpdate, h]

theorem mtxUnopFold_eq [Zero α] (N M : ℕ)
    (f : (ℕ × ℕ) → α → α)
    (presZero : ∀ i j, N ≤ i ∨ M ≤ j → f (i, j) 0 = 0)
    (m : Matrix α)
    (hs : mtxNonzero m ⊆ {p | p.1 < N ∧ p.2 < M}) :
    mtxPointwiseUnop f m = mtxUnopFold N M f m := by
  funext p
  unfold mtxUnopFold
  rw [pointwise_fun_fold (mtxUnopUpdate f)
    (fun _ _ _ h => mtxUnopUpdate_indep₁ f h _)
    (fun _ _ _ h => mtxUnopUpdate_indep₂ f h _)
    (matrixGrid_nodup N M)]
  by_cases hp : p ∈ matrixGrid N M
  · simp [hp, mtxPointwiseUnop, mtxUnopUpdate]
  · have hm : m p = 0 := mtx_zero_outside hs hp
    have hout : N ≤ p.1 ∨ M ≤ p.2 := by
      have hnot : ¬(p.1 < N ∧ p.2 < M) := by
        simpa only [mem_matrixGrid] using hp
      omega
    rcases p with ⟨i, j⟩
    simp [hp, mtxPointwiseUnop, hm, presZero i j hout]

noncomputable def mtxUnopFoldNRest (N M : ℕ) (f : (ℕ × ℕ) → α → α)
    (m : Matrix α) : NRest (Matrix α) ECost :=
  NRest.returnT (mtxUnopFold N M f m)

theorem mtxUnopFold_refine [Zero α] (N M : ℕ)
    (f : (ℕ × ℕ) → α → α)
    (presZero : ∀ i j, N ≤ i ∨ M ≤ j → f (i, j) 0 = 0) :
    (mtxUnopFoldNRest N M f, fun m => NRest.returnT (mtxPointwiseUnop f m)) ∈
      fref (fun m : Matrix α =>
          mtxNonzero m ⊆ {p | p.1 < N ∧ p.2 < M})
        (Set.diagonal (Matrix α))
        (fun _ => NRest.nrestRel (Set.diagonal (Matrix α))) := by
  intro m n hn hmn
  change m = n at hmn
  subst n
  simp only [mtxUnopFoldNRest]
  rw [← mtxUnopFold_eq N M f presZero m hn]
  exact NRest.param_returnT rfl

/-! ## Binary pointwise operation -/

def mtxPointwiseBinop (f : α → α → α) (m n : Matrix α) : Matrix α :=
  fun p => f (m p) (n p)

def mtxBinopUpdate (f : α → α → α) (n : Matrix α)
    (p : ℕ × ℕ) (m : Matrix α) : Matrix α :=
  Function.update m p (f (m p) (n p))

def mtxBinopFold (N M : ℕ) (f : α → α → α)
    (m n : Matrix α) : Matrix α :=
  (matrixGrid N M).foldl (fun m p => mtxBinopUpdate f n p m) m

theorem mtxBinopUpdate_indep₁ (f : α → α → α) (n : Matrix α)
    {p p' : ℕ × ℕ} (h : p ≠ p') (m : Matrix α) :
    mtxBinopUpdate f n p m p' = m p' := by
  simp [mtxBinopUpdate, h.symm]

theorem mtxBinopUpdate_indep₂ (f : α → α → α) (n : Matrix α)
    {p p' : ℕ × ℕ} (h : p ≠ p') (m : Matrix α) :
    mtxBinopUpdate f n p (mtxBinopUpdate f n p' m) p =
      mtxBinopUpdate f n p m p := by
  simp [mtxBinopUpdate, h]

theorem mtxBinopFold_eq [Zero α] (N M : ℕ) (f : α → α → α)
    (presZero : f 0 0 = 0) (m n : Matrix α)
    (hm : mtxNonzero m ⊆ {p | p.1 < N ∧ p.2 < M})
    (hn : mtxNonzero n ⊆ {p | p.1 < N ∧ p.2 < M}) :
    mtxPointwiseBinop f m n = mtxBinopFold N M f m n := by
  funext p
  unfold mtxBinopFold
  rw [pointwise_fun_fold (mtxBinopUpdate f n)
    (fun _ _ _ h => mtxBinopUpdate_indep₁ f n h _)
    (fun _ _ _ h => mtxBinopUpdate_indep₂ f n h _)
    (matrixGrid_nodup N M)]
  by_cases hp : p ∈ matrixGrid N M
  · simp [hp, mtxPointwiseBinop, mtxBinopUpdate]
  · have hm0 : m p = 0 := mtx_zero_outside hm hp
    have hn0 : n p = 0 := mtx_zero_outside hn hp
    simp [hp, mtxPointwiseBinop, hm0, hn0, presZero]

noncomputable def mtxBinopFoldNRest (N M : ℕ) (f : α → α → α)
    (p : Matrix α × Matrix α) : NRest (Matrix α) ECost :=
  NRest.returnT (mtxBinopFold N M f p.1 p.2)

theorem mtxBinopFold_refine [Zero α] (N M : ℕ) (f : α → α → α)
    (presZero : f 0 0 = 0) :
    (mtxBinopFoldNRest N M f,
      fun p => NRest.returnT (mtxPointwiseBinop f p.1 p.2)) ∈
      fref (fun p : Matrix α × Matrix α =>
          mtxNonzero p.1 ⊆ {q | q.1 < N ∧ q.2 < M} ∧
          mtxNonzero p.2 ⊆ {q | q.1 < N ∧ q.2 < M})
        (Set.diagonal (Matrix α) ×ᵣ Set.diagonal (Matrix α))
        (fun _ => NRest.nrestRel (Set.diagonal (Matrix α))) := by
  rintro ⟨m, n⟩ ⟨m', n'⟩ hp hrel
  obtain ⟨hmm, hnn⟩ := hrel
  change m = m' at hmm
  change n = n' at hnn
  subst m'
  subst n'
  simp only [mtxBinopFoldNRest]
  rw [← mtxBinopFold_eq N M f presZero m n hp.1 hp.2]
  exact NRest.param_returnT rfl

/-! ## Pointwise comparison -/

/-- Source comparison semantics: every entry satisfies `f`, and some entry
satisfies `g`. -/
noncomputable def mtxPointwiseCmp (f g : α → α → Bool)
    (m n : Matrix α) : Bool :=
  propBool ((∀ p, f (m p) (n p) = true) ∧
    ∃ p, g (m p) (n p) = true)

def mtxCmpListBool (N M : ℕ) (f g : α → α → Bool)
    (m n : Matrix α) : Bool :=
  (matrixGrid N M).all (fun p => f (m p) (n p)) &&
    (matrixGrid N M).any (fun p => g (m p) (n p))

/-- The source's three-state comparison loop is represented by the equivalent
pair `(all-f-so-far, any-g-so-far)`.  A false first component interrupts the
fold immediately. -/
def mtxCmpStep (f g : α → α → Bool) (m n : Matrix α)
    (p : ℕ × ℕ) (s : Bool × Bool) : Bool × Bool :=
  if f (m p) (n p) then (s.1, s.2 || g (m p) (n p)) else (false, s.2)

noncomputable def mtxCmpFoldNRest (N M : ℕ) (f g : α → α → Bool)
    (p : Matrix α × Matrix α) : NRest Bool ECost :=
  NRest.bindT
    (NRest.nfoldli (fun s : Bool × Bool => s.1)
      (fun q s => NRest.returnT (mtxCmpStep f g p.1 p.2 q s))
      (matrixGrid N M) (true, false))
    (fun s => NRest.returnT (s.1 && s.2))

private theorem mtxCmpStep_of_false (f g : α → α → Bool)
    (m n : Matrix α) (p : ℕ × ℕ) (s : Bool × Bool)
    (h : f (m p) (n p) = false) :
    mtxCmpStep f g m n p s = (false, s.2) := by
  simp [mtxCmpStep, h]

private theorem mtxCmpStep_of_true (f g : α → α → Bool)
    (m n : Matrix α) (p : ℕ × ℕ) (s : Bool × Bool)
    (h : f (m p) (n p) = true) :
    mtxCmpStep f g m n p s = (s.1, s.2 || g (m p) (n p)) := by
  simp [mtxCmpStep, h]

private theorem cmpFold_correct (f g : α → α → Bool) (m n : Matrix α)
    (xs : List (ℕ × ℕ)) (s : Bool × Bool) :
    NRest.bindT
      (NRest.nfoldli (fun s : Bool × Bool => s.1)
        (fun p s => NRest.returnT (mtxCmpStep f g m n p s)) xs s)
      (fun s => (NRest.returnT (s.1 && s.2) : NRest Bool ECost)) =
    (NRest.returnT
      ((s.1 && xs.all (fun p => f (m p) (n p))) &&
        (s.2 || xs.any (fun p => g (m p) (n p)))) : NRest Bool ECost) := by
  induction xs generalizing s with
  | nil =>
      rcases s with ⟨a, b⟩
      cases a <;> cases b <;> simp
  | cons p xs ih =>
      rcases s with ⟨a, b⟩
      cases a <;> cases b <;>
        cases hf : f (m p) (n p) <;>
        cases hg : g (m p) (n p) <;>
        simp [NRest.nfoldli_cons, mtxCmpStep_of_false,
          mtxCmpStep_of_true, hf, hg, ih]

theorem mtxCmpFoldNRest_eq (N M : ℕ) (f g : α → α → Bool)
    (m n : Matrix α) :
    mtxCmpFoldNRest N M f g (m, n) =
      NRest.returnT (mtxCmpListBool N M f g m n) := by
  unfold mtxCmpFoldNRest mtxCmpListBool
  simpa using cmpFold_correct f g m n (matrixGrid N M) (true, false)

private theorem mtxCmp_grid_prop [Zero α] (N M : ℕ)
    (f g : α → α → Bool) (hf0 : f 0 0 = true) (hg0 : g 0 0 = false)
    (m n : Matrix α)
    (hm : mtxNonzero m ⊆ {p | p.1 < N ∧ p.2 < M})
    (hn : mtxNonzero n ⊆ {p | p.1 < N ∧ p.2 < M}) :
    ((∀ p, f (m p) (n p) = true) ∧
        ∃ p, g (m p) (n p) = true) ↔
      ((∀ p ∈ matrixGrid N M, f (m p) (n p) = true) ∧
        ∃ p ∈ matrixGrid N M, g (m p) (n p) = true) := by
  constructor
  · rintro ⟨hall, ⟨p, hp⟩⟩
    refine ⟨fun q _ => hall q, ?_⟩
    by_cases hpg : p ∈ matrixGrid N M
    · exact ⟨p, hpg, hp⟩
    · have hm0 : m p = 0 := mtx_zero_outside hm hpg
      have hn0 : n p = 0 := mtx_zero_outside hn hpg
      simp [hm0, hn0, hg0] at hp
  · rintro ⟨hall, ⟨p, hpg, hp⟩⟩
    refine ⟨?_, ⟨p, hp⟩⟩
    intro q
    by_cases hqg : q ∈ matrixGrid N M
    · exact hall q hqg
    · have hm0 : m q = 0 := mtx_zero_outside hm hqg
      have hn0 : n q = 0 := mtx_zero_outside hn hqg
      simpa [hm0, hn0] using hf0

theorem mtxCmpListBool_eq [Zero α] (N M : ℕ)
    (f g : α → α → Bool) (hf0 : f 0 0 = true) (hg0 : g 0 0 = false)
    (m n : Matrix α)
    (hm : mtxNonzero m ⊆ {p | p.1 < N ∧ p.2 < M})
    (hn : mtxNonzero n ⊆ {p | p.1 < N ∧ p.2 < M}) :
    mtxCmpListBool N M f g m n = mtxPointwiseCmp f g m n := by
  unfold mtxCmpListBool mtxPointwiseCmp propBool
  rw [show
    ((∀ p, f (m p) (n p) = true) ∧
        ∃ p, g (m p) (n p) = true) =
      ((∀ p ∈ matrixGrid N M, f (m p) (n p) = true) ∧
        ∃ p ∈ matrixGrid N M, g (m p) (n p) = true) from
    propext (mtxCmp_grid_prop N M f g hf0 hg0 m n hm hn)]
  rw [Bool.eq_iff_iff]
  simp

theorem mtxCmpFold_refine [Zero α] (N M : ℕ)
    (f g : α → α → Bool) (hf0 : f 0 0 = true) (hg0 : g 0 0 = false) :
    (mtxCmpFoldNRest N M f g,
      fun p => NRest.returnT (mtxPointwiseCmp f g p.1 p.2)) ∈
      fref (fun p : Matrix α × Matrix α =>
          mtxNonzero p.1 ⊆ {q | q.1 < N ∧ q.2 < M} ∧
          mtxNonzero p.2 ⊆ {q | q.1 < N ∧ q.2 < M})
        (Set.diagonal (Matrix α) ×ᵣ Set.diagonal (Matrix α))
        (fun _ => NRest.nrestRel (Set.diagonal Bool)) := by
  rintro ⟨m, n⟩ ⟨m', n'⟩ hp hrel
  obtain ⟨hmm, hnn⟩ := hrel
  change m = m' at hmm
  change n = n' at hnn
  subst m'
  subst n'
  simp only at hp ⊢
  rw [mtxCmpFoldNRest_eq,
    mtxCmpListBool_eq N M f g hf0 hg0 m n hp.1 hp.2]
  exact NRest.param_returnT rfl

/-! ## Registration and theorem-database gates -/

private example :
    (op_mtx_new ℕ, op_mtx_new ℕ) ∈
      fref (fun _ : Matrix ℕ => True) (mtxRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (mtxRel (Set.diagonal ℕ))) :=
  op_mtx_new_fref ℕ (Set.diagonal ℕ)

private example :
    (op_mtx_copy ℕ, op_mtx_copy ℕ) ∈
      fref (fun _ : Matrix ℕ => True) (mtxRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (mtxRel (Set.diagonal ℕ))) :=
  op_mtx_copy_fref ℕ (Set.diagonal ℕ)

private example :
    (op_mtx_get ℕ, op_mtx_get ℕ) ∈
      fref (fun _ : Matrix ℕ => True) (mtxRel (Set.diagonal ℕ))
        (fun _ => (Set.diagonal ℕ ×ᵣ Set.diagonal ℕ) →ᵣ
          NRest.nrestRel (Set.diagonal ℕ)) :=
  op_mtx_get_fref ℕ (Set.diagonal ℕ)

private example :
    (op_mtx_set ℕ, op_mtx_set ℕ) ∈
      fref (fun _ : Matrix ℕ => True) (mtxRel (Set.diagonal ℕ))
        (fun _ => (Set.diagonal ℕ ×ᵣ Set.diagonal ℕ) →ᵣ
          Set.diagonal ℕ →ᵣ
            NRest.nrestRel (mtxRel (Set.diagonal ℕ))) :=
  op_mtx_set_fref ℕ (Set.diagonal ℕ)

private example :
    (op_mtx_nonzero ℕ, op_mtx_nonzero ℕ) ∈
      fref (fun _ : Matrix ℕ => True) (mtxRel (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel
          (setRel (Set.diagonal ℕ ×ᵣ Set.diagonal ℕ))) :=
  op_mtx_nonzero_fref ℕ

example : op_mtx_new ℕ ::ᵢ
    ((ℕ × ℕ → ℕ) → NRest (MatrixI ℕ) ECost) :=
  op_mtx_new_registration_itype
example : op_mtx_copy ℕ ::ᵢ
    (MatrixI ℕ → NRest (MatrixI ℕ) ECost) :=
  op_mtx_copy_registration_itype
example : op_mtx_get ℕ ::ᵢ
    (MatrixI ℕ → (ℕ × ℕ) → NRest ℕ ECost) :=
  op_mtx_get_registration_itype
example : op_mtx_set ℕ ::ᵢ
    (MatrixI ℕ → (ℕ × ℕ) → ℕ → NRest (MatrixI ℕ) ECost) :=
  op_mtx_set_registration_itype
example : op_mtx_nonzero ℕ ::ᵢ
    (MatrixI ℕ → NRest (SetI (ℕ × ℕ)) ECost) :=
  op_mtx_nonzero_registration_itype

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``op_mtx_new_fref, ``op_mtx_copy_fref, ``op_mtx_get_fref,
      ``op_mtx_set_fref, ``op_mtx_nonzero_fref] do
    unless rules.contains n do
      throwError "matrix interface gate: missing parametricity rule {n}"

/-! ## Kernel-three guards -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.matrixGrid_divmod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms matrixGrid_divmod

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.mtxUnopFold_refine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mtxUnopFold_refine

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.mtxCmpFold_refine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mtxCmpFold_refine

end Lax13Proofs.Refine.Sepref.Iicf
