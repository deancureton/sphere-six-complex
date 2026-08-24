/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Final

/-!
# An identity-normalized complex structure on the six-sphere

This strengthens `AdmitsComplexStructure` by retaining the complex and underlying real manifold
proofs and requiring the comparison with the standard smooth atlas to have identity underlying
map. The transport argument is adapted from
`ComplexStructures.Foundation.AtlasTransport` in the companion formalization.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

noncomputable section

/-- Compatibility with a smooth atlas witnessed by a diffeomorphism whose underlying map is the
identity. This records that the transported complex atlas lives on the standard smooth sphere,
not merely on a diffeomorphic copy of it. -/
@[expose]
public def IdentitySmoothlyCompatible {M : Type*} [TopologicalSpace M]
    (standard : ChartedSpace RealModel M) (complex : ChartedSpace ComplexModel M) : Prop :=
  ∃ d :
      @Diffeomorph ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
        inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel)
        𝓘(ℝ, RealModel) M inferInstance (underlyingRealChartedSpace complex) M
        inferInstance standard ∞,
    ∀ x : M, d x = x

/-- A complex atlas on a fixed smooth six-manifold, together with both manifold proofs and an
identity-normalized comparison of its underlying real atlas with the fixed smooth atlas. -/
public structure NormalizedComplexStructure (M : Type*) [TopologicalSpace M]
    [standard : ChartedSpace RealModel M] where
  /-- The complex three-dimensional atlas. -/
  complexCharts : ChartedSpace ComplexModel M
  /-- The complex atlas defines a complex manifold. -/
  complexManifold :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance 𝓘(ℂ, ComplexModel) ∞ M inferInstance complexCharts
  /-- The real atlas induced from the complex atlas defines a smooth manifold. -/
  realManifold :
    @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
      𝓘(ℝ, RealModel) ∞ M inferInstance (underlyingRealChartedSpace complexCharts)
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

/-- Transporting the atlas of a complex threefold along a diffeomorphism to `S⁶` produces a
complex structure whose real comparison map is literally the identity. -/
public theorem normalizedComplexStructure_of_diffeomorphicToSixSphere
    (X : ComplexThreefold) (hX : DiffeomorphicToSixSphere X) :
    Nonempty (NormalizedComplexStructure SixSphere) := by
  obtain ⟨d⟩ := hX
  let _ : TopologicalSpace X.Carrier := X.topology
  let _ : ChartedSpace ComplexModel X.Carrier := X.charts
  let cReal : ChartedSpace RealModel X.Carrier := underlyingRealChartedSpace X.charts
  let h : X.Carrier ≃ₜ SixSphere := d.toHomeomorph
  let cSphere : ChartedSpace ComplexModel SixSphere := transportChartedSpace h
  have complexManifold :
      @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
        inferInstance 𝓘(ℂ, ComplexModel) ∞ SixSphere inferInstance cSphere :=
    @isManifold_transportChartedSpace ℂ inferInstance ComplexModel inferInstance inferInstance
      ComplexModel inferInstance 𝓘(ℂ, ComplexModel) ∞ X.Carrier SixSphere X.topology
      inferInstance X.charts X.manifold h
  have realManifoldTransported :
      @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
        𝓘(ℝ, RealModel) ∞ SixSphere inferInstance
          (@transportChartedSpace RealModel inferInstance X.Carrier SixSphere X.topology
            inferInstance cReal h) :=
    @isManifold_transportChartedSpace ℝ inferInstance RealModel inferInstance inferInstance
      RealModel inferInstance 𝓘(ℝ, RealModel) ∞ X.Carrier SixSphere X.topology
      inferInstance cReal X.realManifold h
  have realManifold :
      @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
        𝓘(ℝ, RealModel) ∞ SixSphere inferInstance
          (underlyingRealChartedSpace cSphere) := by
    rw [show underlyingRealChartedSpace cSphere =
      @transportChartedSpace RealModel inferInstance X.Carrier SixSphere X.topology
        inferInstance cReal h from underlyingRealChartedSpace_transport X.charts h]
    exact realManifoldTransported
  have identityCompatible : IdentitySmoothlyCompatible inferInstance cSphere := by
    unfold IdentitySmoothlyCompatible
    rw [show underlyingRealChartedSpace cSphere =
      @transportChartedSpace RealModel inferInstance X.Carrier SixSphere X.topology
        inferInstance cReal h from underlyingRealChartedSpace_transport X.charts h]
    let t := @transportDiffeomorph ℝ inferInstance RealModel inferInstance inferInstance
      RealModel inferInstance 𝓘(ℝ, RealModel) ∞ X.Carrier SixSphere X.topology
      inferInstance cReal X.realManifold h
    let tsymm := @Diffeomorph.symm ℝ inferInstance RealModel inferInstance inferInstance
      RealModel inferInstance inferInstance RealModel inferInstance RealModel inferInstance
      𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) X.Carrier X.topology cReal SixSphere
      inferInstance (transportChartedSpace h) ∞ t
    let result := @Diffeomorph.trans ℝ inferInstance RealModel inferInstance inferInstance
      RealModel inferInstance inferInstance RealModel inferInstance inferInstance RealModel
      inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel)
      𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) SixSphere inferInstance
      (transportChartedSpace h) X.Carrier X.topology cReal SixSphere inferInstance inferInstance
      ∞ tsymm d
    refine ⟨result, ?_⟩
    intro x
    change d (h.symm x) = x
    exact d.apply_symm_apply x
  exact ⟨⟨cSphere, complexManifold, realManifold, identityCompatible⟩⟩

/-- The completed construction therefore supplies the standard smooth six-sphere with an
identity-normalized complex atlas. -/
public theorem sixSphere_has_normalizedComplexStructure :
    Nonempty (NormalizedComplexStructure SixSphere) := by
  obtain ⟨X, hX⟩ := exists_complex_threefold_diffeomorphic_sixSphere
  exact normalizedComplexStructure_of_diffeomorphicToSixSphere X hX

end

end SphereSixComplex
