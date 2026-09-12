module

public import SphereSixComplex.Paper.Geometry.EllipticFixedPointCriterion
public import SphereSixComplex.Prerequisites.Geometry.CayleyManifold

/-!
# Actual analytic charts near the elliptic fibres

The Cayley coordinate gives the base chart.  The locally biholomorphic period-family quotient
then supplies local analytic parametrizations by the Cayley disc times the vector cover.
-/

open scoped Manifold ComplexConjugate ContDiff

namespace SphereSixComplex.Geometry.EllipticLocalTrivialization

open Complex SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open SphereSixComplex.Geometry SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticFamilySpecialization

noncomputable section

/-- The order-three Cayley coordinate as a biholomorphism. -/
@[expose] public noncomputable def orderThreeCayleyDiffeomorph (n : WithTop ℕ∞) :
    UpperHalfPlane ≃ₘ^n⟮(modelWithCornersSelf ℂ ℂ), (modelWithCornersSelf ℂ ℂ)⟯
      ComplexUnitDisc :=
  UpperHalfPlane.cayleyDiffeomorph fuchsianOneFixedPoint n

/-- The order-four Cayley coordinate as a biholomorphism. -/
@[expose] public noncomputable def orderFourCayleyDiffeomorph (n : WithTop ℕ∞) :
    UpperHalfPlane ≃ₘ^n⟮(modelWithCornersSelf ℂ ℂ), (modelWithCornersSelf ℂ ℂ)⟯
      ComplexUnitDisc :=
  UpperHalfPlane.cayleyDiffeomorph fuchsianTwoFixedPoint n





@[simp]
public theorem orderThreeCayleyHomeomorph_fixedPoint :
    orderThreeCayleyHomeomorph fuchsianOneFixedPoint = ComplexUnitDisc.center := by
  apply Subtype.ext
  exact orderThreeCayley_fixedPoint

@[simp]
public theorem orderFourCayleyHomeomorph_fixedPoint :
    orderFourCayleyHomeomorph fuchsianTwoFixedPoint = ComplexUnitDisc.center := by
  apply Subtype.ext
  exact orderFourCayley_fixedPoint



end

end SphereSixComplex.Geometry.EllipticLocalTrivialization
