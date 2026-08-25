module

public import SphereSixComplex.ComplexStructure
import all SphereSixComplex.ComplexStructure

/-!
# Restricting a complex manifold atlas to the real scalars

The underlying real atlas of a complex three-manifold is a smooth real six-manifold atlas.  This
is the standard restriction-of-scalars theorem, stated for the concrete models used by this
project.

The real atlas `underlyingRealChartedSpace c` is the composite of the complex atlas `c` with the
single real-linear chart `complexToRealModel : ℂ³ ≃L[ℝ] ℝ⁶`.  Its transition maps are therefore the
complex transition maps conjugated by that real-linear identification, and a holomorphic (indeed
`C^∞` over `ℂ`) map is `C^∞` over `ℝ` by `ContDiffOn.restrict_scalars`.

This module used to state the theorem as an axiom; it is now proved.
-/

open scoped ContDiff Manifold
open Set

namespace SphereSixComplex.Geometry.EstablishedComplexToRealManifold

/-- Every chart of the real coordinate system on `ℂ³` agrees with the real-linear identification
`complexToRealModel` on its source. -/
public theorem complexModelRealChart_eq_on_source
    (f : OpenPartialHomeomorph ComplexModel RealModel)
    (hf : f ∈ complexModelRealChartedSpace.atlas) {y : ComplexModel} (hy : y ∈ f.source) :
    f y = complexToRealModel y := by
  obtain ⟨q, rfl⟩ := hf
  simp only [chartAt_self_eq, OpenPartialHomeomorph.trans_refl] at hy ⊢
  apply complexToRealModel.symm.injective
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact IsLocalHomeomorph.apply_localInverseAt_of_mem _ hy

/-- The inverse of every chart of the real coordinate system on `ℂ³` is the inverse real-linear
identification, as a function. -/
public theorem complexModelRealChart_symm_eq
    (f : OpenPartialHomeomorph ComplexModel RealModel)
    (hf : f ∈ complexModelRealChartedSpace.atlas) :
    (f.symm : RealModel → ComplexModel) = complexToRealModel.symm := by
  obtain ⟨q, rfl⟩ := hf
  simp only [chartAt_self_eq, OpenPartialHomeomorph.trans_refl,
    IsLocalHomeomorph.localInverseAt_symm]
  rfl

/-- Standard restriction of scalars from a complex three-manifold to its underlying smooth real
six-manifold: the transition maps of the underlying real atlas are the complex transition maps
conjugated by `complexToRealModel`, hence real-smooth. -/
public theorem establishedUnderlyingRealIsManifold
    {M : Type*} [TopologicalSpace M]
    (c : ChartedSpace ComplexModel M)
    (h : @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance (modelWithCornersSelf ℂ ComplexModel) ∞ M inferInstance c) :
    @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
      (modelWithCornersSelf ℝ RealModel) ∞ M inferInstance (underlyingRealChartedSpace c) := by
  let _ := c
  let _ : ChartedSpace RealModel ComplexModel := complexModelRealChartedSpace
  refine @isManifold_of_contDiffOn ℝ _ RealModel _ _ RealModel _ (modelWithCornersSelf ℝ RealModel)
    ∞ M _ (underlyingRealChartedSpace c) ?_
  rintro e e' ⟨e₁, he₁, f₁, hf₁, rfl⟩ ⟨e₂, he₂, f₂, hf₂, rfl⟩
  simp only [mfld_simps]
  set T := e₁.symm ≫ₕ e₂ with hT
  have hmem : T ∈ contDiffGroupoid ∞ (modelWithCornersSelf ℂ ComplexModel) :=
    StructureGroupoid.compatible _ he₁ he₂
  have hC : ContDiffOn ℂ ∞ T T.source := by
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at hmem
    simpa [mfld_simps] using hmem.1
  have hR : ContDiffOn ℝ ∞ T T.source := hC.restrict_scalars ℝ
  have hg : ContDiffOn ℝ ∞
      (⇑complexToRealModel ∘ ⇑T ∘ ⇑complexToRealModel.symm)
      (⇑complexToRealModel.symm ⁻¹' T.source) := by
    have := (hR.comp_continuousLinearMap
      (complexToRealModel.symm : RealModel →L[ℝ] ComplexModel)).continuousLinearMap_comp
      (complexToRealModel : ComplexModel →L[ℝ] RealModel)
    simpa using this
  have hf₁' : (f₁.symm : RealModel → ComplexModel) = complexToRealModel.symm :=
    complexModelRealChart_symm_eq f₁ hf₁
  refine (hg.mono ?_).congr ?_
  · rintro x ⟨⟨_, hx₁⟩, hx₂, _⟩
    simp only [mem_preimage, Function.comp] at hx₁ hx₂ ⊢
    rw [← hf₁']
    exact ⟨hx₁, hx₂⟩
  · rintro x ⟨⟨_, _⟩, _, hx₃⟩
    simp only [mem_preimage, Function.comp] at hx₃ ⊢
    rw [hf₁']
    exact complexModelRealChart_eq_on_source f₂ hf₂ (by simpa [hf₁'] using hx₃)

end SphereSixComplex.Geometry.EstablishedComplexToRealManifold
