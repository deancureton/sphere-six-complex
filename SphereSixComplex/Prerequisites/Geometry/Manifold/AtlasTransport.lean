module

public import ChallengeDefs
public import ForMathlib.Geometry.Manifold.AtlasTransport

/-!
# Transporting a compatible complex atlas
-/

@[expose] public section

open scoped ContDiff Manifold

namespace SphereSixComplex

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

/-- Passing to the underlying real atlas commutes with transport. -/
public theorem underlyingRealChartedSpace_transport (c : ChartedSpace ComplexModel M)
    (h : M ≃ₜ N) :
    underlyingRealChartedSpace (transportChartedSpace h : ChartedSpace ComplexModel N) =
      @transportChartedSpace RealModel inferInstance M N inferInstance inferInstance
        (underlyingRealChartedSpace c) h := by
  exact comp_transportChartedSpace complexModelRealChartedSpace c h


/-- A complex manifold whose underlying real atlas is diffeomorphic to a specified target atlas
transports to a complex structure compatible with that target atlas. -/
public theorem admitsComplexStructure_of_diffeomorph
    [standardN : ChartedSpace RealModel N] (c : ChartedSpace ComplexModel M)
    (complexManifold :
      @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
        inferInstance 𝓘(ℂ, ComplexModel) ∞ M inferInstance c)
    (realManifold :
      @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
        𝓘(ℝ, RealModel) ∞ M inferInstance (underlyingRealChartedSpace c))
    (d :
      @Diffeomorph ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
        inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel)
        𝓘(ℝ, RealModel) M inferInstance (underlyingRealChartedSpace c) N inferInstance standardN
        ∞) :
    AdmitsComplexStructure N := by
  let h : M ≃ₜ N := @Diffeomorph.toHomeomorph ℝ inferInstance RealModel inferInstance
    inferInstance RealModel inferInstance inferInstance RealModel inferInstance RealModel
    inferInstance 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) M inferInstance
    (underlyingRealChartedSpace c) N inferInstance standardN ∞ d
  let cN : ChartedSpace ComplexModel N := transportChartedSpace h
  refine ⟨cN, ?_, ?_⟩
  · exact @isManifold_transportChartedSpace ℂ inferInstance ComplexModel inferInstance
      inferInstance ComplexModel inferInstance 𝓘(ℂ, ComplexModel) ∞ M N inferInstance
      inferInstance c complexManifold h
  · unfold SmoothlyCompatible
    rw [show underlyingRealChartedSpace cN =
      @transportChartedSpace RealModel inferInstance M N inferInstance inferInstance
        (underlyingRealChartedSpace c) h from underlyingRealChartedSpace_transport c h]
    let cReal : ChartedSpace RealModel M := underlyingRealChartedSpace c
    let t := @transportDiffeomorph ℝ inferInstance RealModel inferInstance inferInstance RealModel
      inferInstance 𝓘(ℝ, RealModel) ∞ M N inferInstance inferInstance cReal realManifold h
    let tsymm := @Diffeomorph.symm ℝ inferInstance RealModel inferInstance inferInstance RealModel
      inferInstance inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel)
      𝓘(ℝ, RealModel) M inferInstance (underlyingRealChartedSpace c) N inferInstance
      (transportChartedSpace h) ∞ t
    let result := @Diffeomorph.trans ℝ inferInstance RealModel inferInstance inferInstance
      RealModel inferInstance inferInstance RealModel inferInstance inferInstance RealModel
      inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel)
      𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) N inferInstance (transportChartedSpace h) M
      inferInstance (underlyingRealChartedSpace c) N inferInstance standardN ∞ tsymm d
    refine ⟨result, ?_⟩
    intro x
    change d (d.symm x) = x
    exact d.apply_symm_apply x

end SphereSixComplex
