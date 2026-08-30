module

public import SphereSixComplex.Topology.PaperSectionSevenAffineRadialBaseLiftProjection

/-!
# Base-coordinate square for the principal elliptic gauges

The principal logarithmic gauges translate only the torus coordinate.  Passing from a gauged
punctured collar point to the regular family therefore retains the original upper-half-plane
base point.  Together with the radial-lift projection formulas, this identifies the two sides of
the covering-space comparison square.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph

open SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open TorusFamily GlobalTorusFamily AnalyticTorusFamily
open EllipticWholeFiberCompactCover

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- The order-three principal gauge translates only the family fibre. -/
public theorem familyTotalSpaceBase_orderThreePrincipalGauge
    (q : TotalSpace (parameterMap F)) :
    familyTotalSpaceBase F (orderThreePrincipalGaugeEquiv F q) =
      familyTotalSpaceBase F q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    rfl

/-- The order-four principal gauge translates only the family fibre. -/
public theorem familyTotalSpaceBase_orderFourPrincipalGauge
    (q : TotalSpace (parameterMap F)) :
    familyTotalSpaceBase F (orderFourPrincipalGaugeEquiv F q) =
      familyTotalSpaceBase F q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    rfl

end SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph

namespace SphereSixComplex.Geometry

open SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open TorusFamily GlobalTorusFamily AnalyticTorusFamily
open EllipticPuncturedCollarGaugeHomeomorph EllipticVaryingFamilyQuotient
open EllipticLinearCollarGlobalDescent EllipticWholeFiberCompactCover
open PaperAnalyticData

/-- After the order-three principal gauge and collar-to-regular conversion, the regular base is
the original collar representative's base. -/
public theorem orderThreeCollarToRegular_principalGauge_base
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    {r : ℝ} (D : OrderThreeLinearCollarSourceData (U := U) r)
    (q : (orderThreeAffinePuncturedCarrier F hsource r).carrier) :
    (regularTotalSpaceBase F
      (orderThreeCollarToRegular F hproper D
        (orderThreePuncturedCollarGaugeEquiv F r q))).1 =
      familyTotalSpaceBase F q.1 := by
  calc
    _ = familyTotalSpaceBase F
        (orderThreePuncturedCollarGaugeEquiv F r q).1 :=
      orderThreeCollarToRegular_base F hproper hsource D
        (orderThreePuncturedCollarGaugeEquiv F r q)
    _ = familyTotalSpaceBase F q.1 :=
      familyTotalSpaceBase_orderThreePrincipalGauge F q.1

/-- After the order-four principal gauge and collar-to-regular conversion, the regular base is
the original collar representative's base. -/
public theorem orderFourCollarToRegular_principalGauge_base
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    {r : ℝ} (D : OrderFourLinearCollarSourceData (U := U) r)
    (q : (orderFourAffinePuncturedCarrier F hsource r).carrier) :
    (regularTotalSpaceBase F
      (orderFourCollarToRegular F hproper D
        (orderFourPuncturedCollarGaugeEquiv F r q))).1 =
      familyTotalSpaceBase F q.1 := by
  calc
    _ = familyTotalSpaceBase F
        (orderFourPuncturedCollarGaugeEquiv F r q).1 :=
      orderFourCollarToRegular_base F hproper hsource D
        (orderFourPuncturedCollarGaugeEquiv F r q)
    _ = familyTotalSpaceBase F q.1 :=
      familyTotalSpaceBase_orderFourPrincipalGauge F q.1

end SphereSixComplex.Geometry

end
