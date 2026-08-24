module

public import SphereSixComplex.ComplexStructure

/-!
# Restricting a complex manifold atlas to the real scalars

The underlying real atlas of a complex three-manifold is a smooth real six-manifold atlas.  This
is the standard restriction-of-scalars theorem, stated for the concrete models used by this
project.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.EstablishedComplexToRealManifold

/-- Standard restriction of scalars from a complex three-manifold to its underlying smooth real
six-manifold. -/
public axiom establishedUnderlyingRealIsManifold
    {M : Type*} [TopologicalSpace M]
    (c : ChartedSpace ComplexModel M)
    (h : @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance (modelWithCornersSelf ℂ ComplexModel) ∞ M inferInstance c) :
    @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
      (modelWithCornersSelf ℝ RealModel) ∞ M inferInstance (underlyingRealChartedSpace c)

end SphereSixComplex.Geometry.EstablishedComplexToRealManifold
