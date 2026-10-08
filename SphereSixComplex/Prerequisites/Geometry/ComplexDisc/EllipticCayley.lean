module

public import ForMathlib.Analysis.Complex.UpperHalfPlane.Cayley
public import SphereSixComplex.Prerequisites.Geometry.ComplexDisc.EllipticCoordinates

namespace SphereSixComplex.Geometry.EllipticCayleyHomeomorph

open SphereSixComplex.Geometry.EllipticLocalCoordinates

noncomputable section

/-- The order-three elliptic base chart. -/
@[expose] public noncomputable def orderThreeCayleyHomeomorph :
    UpperHalfPlane ≃ₜ ComplexUnitDisc :=
  UpperHalfPlane.cayleyHomeomorph SphereSixComplex.TriangleGroup.fuchsianOneFixedPoint

/-- The order-four elliptic base chart. -/
@[expose] public noncomputable def orderFourCayleyHomeomorph :
    UpperHalfPlane ≃ₜ ComplexUnitDisc :=
  UpperHalfPlane.cayleyHomeomorph SphereSixComplex.TriangleGroup.fuchsianTwoFixedPoint

public theorem orderThreeCayleyHomeomorph_generator (z : UpperHalfPlane) :
    orderThreeCayleyHomeomorph
        (SphereSixComplex.TriangleGroup.fuchsianSourceAction
          SphereSixComplex.TriangleGroup.g₁ • z) =
      orderThreeDiscRotation (orderThreeCayleyHomeomorph z) := by
  apply Subtype.ext
  exact orderThreeCayley_generator z

public theorem orderFourCayleyHomeomorph_generator (z : UpperHalfPlane) :
    orderFourCayleyHomeomorph
        (SphereSixComplex.TriangleGroup.fuchsianSourceAction
          SphereSixComplex.TriangleGroup.g₂ • z) =
      orderFourDiscRotation (orderFourCayleyHomeomorph z) := by
  apply Subtype.ext
  exact orderFourCayley_generator z

end

end SphereSixComplex.Geometry.EllipticCayleyHomeomorph
