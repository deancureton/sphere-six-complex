module

public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianArithmeticCore
public import SphereSixComplex.Paper.TriangleGroup.FuchsianProperFreeness

namespace SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

open SphereSixComplex.TriangleGroup

/-- The project-level compact-set criterion follows for any uniformization whose source action is
the explicit Fuchsian action. -/
public theorem sourceActionProperlyDiscontinuous_of_eq
    {U : SphereSixComplex.Periods.TriangleUniformization}
    (hsource : U.sourceAction = fuchsianSourceAction) :
    SphereSixComplex.Geometry.GlobalTorusFamily.SourceActionProperlyDiscontinuous (U := U) := by
  intro K L hK hL
  simpa only [hsource] using finite_fuchsianSourceAction_intersections_of_isCompact hK hL

end SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
