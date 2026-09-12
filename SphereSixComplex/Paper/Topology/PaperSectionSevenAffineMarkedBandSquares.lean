module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineRegularLiftCompletionAssembly

/-!
# Marked central-band squares for the affine completion

The established affine-band trivialization is unpacked into its actual product homeomorphism and
the resulting fibre-coordinate map.  This makes both canonical finite-cover projections explicit
and isolates the remaining compatibility as two named geometric squares.
-/

@[expose] public section

noncomputable section

open Set
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.EllipticFilling

variable {A : AnalyticData}




/-- The named map from the actual affine band to its selected common torus coordinate. -/
public noncomputable def affineBandFiberCoordinate (A : AnalyticData) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :=
  (A.actualAffineHeightSplit.sidesIntersectionHomeomorph.toHomotopyEquiv.trans
    (A.affineCentralBandHomotopyEquiv
      A.affineCentralSeparation)).toFun


/-- The order-three canonical marked projection, factored through the named band fibre
coordinate and the actual finite quotient map. -/
public noncomputable def affineBandOrderThreeMarkedProjection
    (A : AnalyticData) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      orderThreeReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
      A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩).comp
        (affineBandFiberCoordinate A)

/-- The order-four canonical marked projection, factored through the named band fibre
coordinate and the actual finite quotient map. -/
public noncomputable def affineBandOrderFourMarkedProjection
    (A : AnalyticData) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      orderFourReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
      A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩).comp
        (affineBandFiberCoordinate A)

/-- The named order-three marked projection is exactly the fixed cover map used by the radial
completion. -/
public theorem affineBandOrderThreeMarkedProjection_eq_coverMap
    (A : AnalyticData) :
    affineBandOrderThreeMarkedProjection A =
      affineBandOrderThreeCoverMap A := by
  rfl

/-- The named order-four marked projection is exactly the fixed cover map used by the radial
completion. -/
public theorem affineBandOrderFourMarkedProjection_eq_coverMap
    (A : AnalyticData) :
    affineBandOrderFourMarkedProjection A =
      affineBandOrderFourCoverMap A := by
  rfl


end SphereSixComplex.Geometry.AnalyticData

end
