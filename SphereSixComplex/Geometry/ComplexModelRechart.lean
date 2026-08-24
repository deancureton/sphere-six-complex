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
@[expose, instance_reducible]
public def globalDeckProductCharts
    {M : Type*} [TopologicalSpace M] [c : ChartedSpace (ModelProd ℂ ComplexTwoSpace) M] :
    ChartedSpace (ℂ × ComplexTwoSpace) M :=
  c

/-- The canonical `ℂ³` recharting of an atlas expressed in the product coordinates. -/
@[expose, instance_reducible]
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

end

end SphereSixComplex.Geometry
