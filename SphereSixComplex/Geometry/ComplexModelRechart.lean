module

public import SphereSixComplex.Geometry.AtlasTransport
public import SphereSixComplex.Geometry.GlobalDeckSmoothness

/-!
# Recharting the product model as complex three-space
-/

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry

open ComplexTorus GlobalTorusFamily

noncomputable section

/-- A complex-linear identification of the product coordinates with the canonical `ℂ³` model. -/
public noncomputable def globalDeckComplexModelEquiv :
    (ℂ × ComplexTwoSpace) ≃L[ℂ] ComplexModel :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp [ComplexModel, ComplexTwoSpace])

/-- Remove Mathlib's product-model type tag without changing the atlas. -/
@[instance_reducible]
public def globalDeckProductCharts
    {M : Type*} [TopologicalSpace M] [c : ChartedSpace (ModelProd ℂ ComplexTwoSpace) M] :
    ChartedSpace (ℂ × ComplexTwoSpace) M :=
  c

/-- The canonical `ℂ³` recharting of an atlas expressed in the product coordinates. -/
@[instance_reducible]
public noncomputable def globalDeckComplexCharts
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd ℂ ComplexTwoSpace) M] :
    ChartedSpace ComplexModel M :=
  let _ : ChartedSpace (ℂ × ComplexTwoSpace) M := globalDeckProductCharts
  linearRechart globalDeckComplexModelEquiv

/-- A manifold in the product coordinates is a complex threefold in the canonical model. -/
public theorem globalDeckComplexManifold
    {M : Type*} [TopologicalSpace M] [c : ChartedSpace (ModelProd ℂ ComplexTwoSpace) M]
    {n : ℕ∞ω} [m : IsManifold GlobalDeckTotalModel n M] :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance 𝓘(ℂ, ComplexModel) n M inferInstance globalDeckComplexCharts := by
  let cProduct : ChartedSpace (ℂ × ComplexTwoSpace) M := globalDeckProductCharts
  let _ : ChartedSpace (ℂ × ComplexTwoSpace) M := cProduct
  have hproduct : IsManifold 𝓘(ℂ, ℂ × ComplexTwoSpace) n M := by
    rwa [modelWithCornersSelf_prod]
  let _ : IsManifold 𝓘(ℂ, ℂ × ComplexTwoSpace) n M := hproduct
  exact isManifold_linearRechart globalDeckComplexModelEquiv

/-- A local diffeomorphism in the product coordinates remains a local biholomorphism after both
source and target are recharted as the canonical `ℂ³` model. -/
public theorem globalDeckComplexLocalDiffeomorph
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [cM : ChartedSpace (ModelProd ℂ ComplexTwoSpace) M]
    [cN : ChartedSpace (ModelProd ℂ ComplexTwoSpace) N]
    {f : M → N}
    (hf : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞ f) :
    letI : ChartedSpace ComplexModel M := globalDeckComplexCharts
    letI : ChartedSpace ComplexModel N := globalDeckComplexCharts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ f := by
  letI productM : ChartedSpace (ℂ × ComplexTwoSpace) M := globalDeckProductCharts
  letI productN : ChartedSpace (ℂ × ComplexTwoSpace) N := globalDeckProductCharts
  letI complexM : ChartedSpace ComplexModel M := globalDeckComplexCharts
  letI complexN : ChartedSpace ComplexModel N := globalDeckComplexCharts
  let dM : M ≃ₘ^∞⟮(modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)),
      (modelWithCornersSelf ℂ ComplexModel)⟯ M :=
    { toEquiv := Equiv.refl M
      contMDiff_toFun := contMDiff_id_linearRechart globalDeckComplexModelEquiv
      contMDiff_invFun := contMDiff_id_linearRechart_symm globalDeckComplexModelEquiv }
  let dN : N ≃ₘ^∞⟮(modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)),
      (modelWithCornersSelf ℂ ComplexModel)⟯ N :=
    { toEquiv := Equiv.refl N
      contMDiff_toFun := contMDiff_id_linearRechart globalDeckComplexModelEquiv
      contMDiff_invFun := contMDiff_id_linearRechart_symm globalDeckComplexModelEquiv }
  intro x
  have hsource := dM.symm.isLocalDiffeomorph x
  have hproduct : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace))
      (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞ f x := by
    simpa only [modelWithCornersSelf_prod] using hf x
  have hmiddle := hsource.comp (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) N hproduct
  have htarget := dN.isLocalDiffeomorph (f x)
  exact hmiddle.comp (modelWithCornersSelf ℂ ComplexModel) N htarget

/-- A local biholomorphism whose source already uses the canonical `ℂ³` atlas remains locally
biholomorphic when only its product-model target is recharted as `ComplexModel`. -/
public theorem globalDeckComplexLocalDiffeomorph_target
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [cM : ChartedSpace ComplexModel M]
    [cN : ChartedSpace (ModelProd ℂ ComplexTwoSpace) N]
    {f : M → N}
    (hf : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      GlobalDeckTotalModel ∞ f) :
    letI : ChartedSpace ComplexModel N := globalDeckComplexCharts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ f := by
  letI productN : ChartedSpace (ℂ × ComplexTwoSpace) N := globalDeckProductCharts
  letI complexN : ChartedSpace ComplexModel N := globalDeckComplexCharts
  let dN : N ≃ₘ^∞⟮(modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)),
      (modelWithCornersSelf ℂ ComplexModel)⟯ N :=
    { toEquiv := Equiv.refl N
      contMDiff_toFun := contMDiff_id_linearRechart globalDeckComplexModelEquiv
      contMDiff_invFun := contMDiff_id_linearRechart_symm globalDeckComplexModelEquiv }
  intro x
  have hproduct : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞ f x := by
    simpa only [modelWithCornersSelf_prod] using hf x
  exact hproduct.comp (modelWithCornersSelf ℂ ComplexModel) N
    (dN.isLocalDiffeomorph (f x))

end

end SphereSixComplex.Geometry
