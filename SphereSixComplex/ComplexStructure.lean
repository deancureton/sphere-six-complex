module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Complex Structures on the Six-Sphere

The final theorem is stated as the existence of a complex atlas on the standard topological
six-sphere. This is stronger than the existence of an almost-complex tangent endomorphism.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- The standard unit six-sphere in seven-dimensional Euclidean space. -/
public abbrev SixSphere : Type := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1)

/-- The complex vector space used as the local model for a complex threefold. -/
public abbrev ComplexModel : Type := EuclideanSpace ℂ (Fin 3)

/- The real vector space used by the standard smooth structure on the six-sphere. -/
public abbrev RealModel : Type := EuclideanSpace ℝ (Fin 6)

/-- A real-linear identification of the underlying real space of `ℂ³` with `ℝ⁶`. -/
public noncomputable def complexToRealModel : ComplexModel ≃L[ℝ] RealModel :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_real_of_complex]
    norm_num [ComplexModel, RealModel])

/-- The real coordinate system on `ℂ³` obtained from `complexToRealModel`. -/
@[instance_reducible]
public noncomputable def complexModelRealChartedSpace : ChartedSpace RealModel ComplexModel :=
  complexToRealModel.symm.toHomeomorph.chartedSpace

/-- The real atlas underlying a complex atlas. -/
@[instance_reducible]
public noncomputable def underlyingRealChartedSpace {M : Type*} [TopologicalSpace M]
    (c : ChartedSpace ComplexModel M) : ChartedSpace RealModel M :=
  letI : ChartedSpace RealModel ComplexModel := complexModelRealChartedSpace
  letI : ChartedSpace ComplexModel M := c
  ChartedSpace.comp RealModel ComplexModel M

/--
A complex atlas is compatible with a specified smooth six-dimensional atlas when its underlying real
atlas is diffeomorphic to that atlas. This prevents the final statement from forgetting the standard smooth
structure on the sphere.
-/
public def SmoothlyCompatible {M : Type*} [TopologicalSpace M]
    (standard : ChartedSpace RealModel M) (complex : ChartedSpace ComplexModel M) : Prop :=
  Nonempty
    (@Diffeomorph ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
      inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) M
      inferInstance (underlyingRealChartedSpace complex) M inferInstance standard ∞)

/--
A standard smooth six-manifold admits a complex structure when it has a complex-differentiable atlas whose
underlying real smooth structure is diffeomorphic to the specified one.
-/
public def AdmitsComplexStructure (M : Type*) [TopologicalSpace M]
    [standard : ChartedSpace RealModel M] : Prop :=
  ∃ c : ChartedSpace ComplexModel M,
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel inferInstance
      𝓘(ℂ, ComplexModel) ∞ M inferInstance c ∧ SmoothlyCompatible standard c

/-- The standard six-sphere admits an integrable complex structure. -/
public theorem sphere_six_admits_complex_structure : AdmitsComplexStructure SixSphere := by
  sorry

end SphereSixComplex
