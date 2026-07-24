import Lax5.Transductions

/-!
The slice of transduction calculus the Appendix-A machinery needs: the
image class of a fixed transduction, monotonicity of the transduces
relation in both arguments, and composition (transitivity). Only
composition carries real content — formula substitution through a
transduction — and it is the single open obligation of this module.
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

/-- Transitivity of the transduces relation: composition of
transductions. Substituting the interpreting formulas of the first
transduction through the formulas of the second, with the second's
colors carried as guessed unary predicates on the source. The workhorse
of the calculus; open obligation. -/
theorem Transduces.trans [L'.IsRelational] [L''.IsRelational]
    {C : StructureClass L} {D : StructureClass L'} {E : StructureClass L''}
    (h₁ : Transduces C D) (h₂ : Transduces D E) : Transduces C E := by
  sorry

end Lax5Proofs.TransductionCalculus
