/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Prerequisites.Geometry.AtlasTransport
public import SphereSixComplex.Prerequisites.Geometry.EstablishedComplexToRealManifold

/-!
# Transporting compatible complex structures

A complex atlas transported along a diffeomorphism has an underlying real atlas compatible
with the target atlas through the identity map. The transport argument is adapted from
`ComplexStructures.Foundation.AtlasTransport` in the companion formalization.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

noncomputable section

/-- Compatibility with a smooth atlas witnessed by a diffeomorphism whose underlying map is the
identity. This compares two smooth structures on the same carrier without changing its points. -/
@[expose]
public def IdentitySmoothlyCompatible {M : Type*} [TopologicalSpace M]
    (standard : ChartedSpace RealModel M) (complex : ChartedSpace ComplexModel M) : Prop :=
  ∃ d :
      @Diffeomorph ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
        inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel)
        𝓘(ℝ, RealModel) M inferInstance (underlyingRealChartedSpace complex) M
        inferInstance standard ∞,
    ∀ x : M, d x = x

/-- A complex atlas compatible with a fixed smooth atlas through the identity map. -/
public structure NormalizedComplexStructure (M : Type*) [TopologicalSpace M]
    [standard : ChartedSpace RealModel M] where
  /-- The complex three-dimensional atlas. -/
  complexCharts : ChartedSpace ComplexModel M
  /-- The complex atlas defines a complex manifold. -/
  complexManifold :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance 𝓘(ℂ, ComplexModel) ∞ M inferInstance complexCharts
  /-- The induced real atlas agrees with the fixed atlas through the identity underlying map. -/
  identityCompatible : IdentitySmoothlyCompatible standard complexCharts

/-- Identity-normalized compatibility implies the compatibility used by the upstream endpoint. -/
public theorem IdentitySmoothlyCompatible.smoothlyCompatible
    {M : Type*} [TopologicalSpace M] {standard : ChartedSpace RealModel M}
    {complex : ChartedSpace ComplexModel M}
    (h : IdentitySmoothlyCompatible standard complex) : SmoothlyCompatible standard complex := by
  obtain ⟨d, -⟩ := h
  exact ⟨d⟩

/-- Forgetting the normalization gives the upstream existence statement. -/
public theorem NormalizedComplexStructure.toAdmitsComplexStructure
    {M : Type*} [TopologicalSpace M] [standard : ChartedSpace RealModel M]
    (c : NormalizedComplexStructure M) : AdmitsComplexStructure M := by
  exact ⟨c.complexCharts, c.complexManifold, c.identityCompatible.smoothlyCompatible⟩

/-- Transport a complex atlas along a diffeomorphism so that the identity compares its induced
real atlas with the target smooth atlas. -/
public theorem normalizedComplexStructure_of_diffeomorph
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [c : ChartedSpace ComplexModel M] [standard : ChartedSpace RealModel N]
    [IsManifold 𝓘(ℂ, ComplexModel) ∞ M]
    (d : letI := underlyingRealChartedSpace c
      Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) M N ∞) :
    Nonempty (NormalizedComplexStructure N) := by
  let hReal := ComplexThreefold.RealAtlas.isManifold c
    (inferInstance : IsManifold 𝓘(ℂ, ComplexModel) ∞ M)
  let cReal : ChartedSpace RealModel M := underlyingRealChartedSpace c
  let h : M ≃ₜ N := d.toHomeomorph
  let cN : ChartedSpace ComplexModel N := transportChartedSpace h
  have complexManifold :
      @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
        inferInstance 𝓘(ℂ, ComplexModel) ∞ N inferInstance cN :=
    @isManifold_transportChartedSpace ℂ inferInstance ComplexModel inferInstance inferInstance
      ComplexModel inferInstance 𝓘(ℂ, ComplexModel) ∞ M N inferInstance
      inferInstance c inferInstance h
  have identityCompatible : IdentitySmoothlyCompatible inferInstance cN := by
    unfold IdentitySmoothlyCompatible
    rw [show underlyingRealChartedSpace cN =
      @transportChartedSpace RealModel inferInstance M N inferInstance
        inferInstance cReal h from underlyingRealChartedSpace_transport c h]
    let : ChartedSpace RealModel M := cReal
    let : IsManifold 𝓘(ℝ, RealModel) ∞ M := hReal
    let t := transportDiffeomorph (I := 𝓘(ℝ, RealModel)) (n := ∞) h
    let tsymm := @Diffeomorph.symm ℝ _ RealModel _ _ RealModel _ _ RealModel _ RealModel _
      𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) M _ cReal N _ (transportChartedSpace h) ∞ t
    let result := @Diffeomorph.trans ℝ _ RealModel _ _ RealModel _ _ RealModel _ _ RealModel _
      RealModel _ RealModel _ 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel)
      N _ (transportChartedSpace h) M _ cReal N _ standard ∞ tsymm d
    refine ⟨result, ?_⟩
    intro x
    change d (h.symm x) = x
    exact d.apply_symm_apply x
  exact ⟨⟨cN, complexManifold, identityCompatible⟩⟩

end

end SphereSixComplex
