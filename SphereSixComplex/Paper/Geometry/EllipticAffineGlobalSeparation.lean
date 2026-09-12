module

public import SphereSixComplex.Paper.Geometry.EllipticVaryingFamilyQuotient
public import SphereSixComplex.Prerequisites.TriangleGroup.EstablishedFuchsianEllipticStabilizers
public import SphereSixComplex.Paper.TriangleGroup.FuchsianProperFreeness
public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianSmoothAction
import all SphereSixComplex.Paper.TriangleGroup.Representation
import all SphereSixComplex.Paper.Geometry.TorusFamily

/-!
# Separation for the affine global elliptic action

The affine free-product action covers the explicit Fuchsian source action.  Proper discontinuity
therefore lifts from the source.  The final collar separation is reduced to the exact source
stabilizer calculation at the two elliptic points.
-/

namespace SphereSixComplex.Geometry.EllipticAffineGlobalSeparation

open Complex
open Filter Set SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)



















end

end SphereSixComplex.Geometry.EllipticAffineGlobalSeparation
