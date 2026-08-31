module

public import SphereSixComplex.Topology.PaperSectionSevenCuspIndexFourPrismCoefficientProof

/-!
# The index-four cusp coordinate from the boundary basis bridge

The boundary bridge places the fourth raw cusp class in the image of the two side homologies.
This reduces its normalized fibre coordinate to one explicit cokernel-basis identification.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticInteriorMarkedCycleData
open SectionSevenEllipticTwoDiscCoverData
open SectionSevenEllipticTwoDiscHomologyCoordinates

variable {A : PaperAnalyticData} {D : A.SectionSevenEllipticTwoDiscCoverData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- A side-homology lift of the fourth raw cusp class, selected from the boundary bridge. -/
public noncomputable def indexFourSideLift
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    IntegralSingularHomology 2 D.orderThreeSide ×
      IntegralSingularHomology 2 D.orderFourSide :=
  ((SectionSevenCuspPulledBackBoundaryBasisBridge.toMayerVietorisBasisBridge D N G
      |>.lowerBasis_factors (4 : Fin 5))).choose

/-- The selected side lift includes to the fourth raw cusp class. -/
public theorem inclusion_indexFourSideLift
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    (presentationTwo (D := D)).inclusion (D.indexFourSideLift N G) =
      cuspToEllipticUnionHomology D 2
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) :=
  ((SectionSevenCuspPulledBackBoundaryBasisBridge.toMayerVietorisBasisBridge D N G
      |>.lowerBasis_factors (4 : Fin 5))).choose_spec

/-- The normalized fibre coordinate of a class included from the two sides is its cokernel
coordinate. -/
public theorem normalizedUnionHomologyTwoEquiv_inclusion_zero
    (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (y : IntegralSingularHomology 2 D.orderThreeSide ×
      IntegralSingularHomology 2 D.orderFourSide) :
    B.normalizedUnionHomologyTwoEquiv S ((presentationTwo (D := D)).inclusion y) 0 =
      B.degreeTwoCoinvariantEquiv (Submodule.Quotient.mk y) := by
  let c : (presentationTwo (D := D)).Coinvariants := Submodule.Quotient.mk y
  have h := congrFun (B.normalizedUnionHomologyTwoEquiv_add S c 0) (0 : Fin 2)
  simp only [map_zero, add_zero] at h
  rw [show (presentationTwo (D := D)).inclusion y =
      (presentationTwo (D := D)).coinvariantsToTotal c by rfl]
  exact h

/-- For the fourth raw cusp class, the normalized fibre coordinate is exactly the cokernel
coordinate of the side lift supplied by the boundary bridge. -/
public theorem indexFourFiberCoordinate_eq_sideLiftCoinvariantCoordinate
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
        (D.cuspNormalizedDegreeTwoSplitting N G)
        (cuspToEllipticUnionHomology D 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) 0 =
      N.actualHomologyCoordinates.degreeTwoCoinvariantEquiv
        (Submodule.Quotient.mk (D.indexFourSideLift N G)) := by
  rw [← D.inclusion_indexFourSideLift N G]
  exact D.normalizedUnionHomologyTwoEquiv_inclusion_zero
    N.actualHomologyCoordinates (D.cuspNormalizedDegreeTwoSplitting N G)
      (D.indexFourSideLift N G)

/-- The same reduction in the exact actual-interior form required by the marked-coordinate
package. -/
public theorem ellipticInteriorDegreeTwoFiberCoordinateHom_indexFour_eq_sideLift
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    D.ellipticInteriorDegreeTwoFiberCoordinateHom N G
        (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) =
      N.actualHomologyCoordinates.degreeTwoCoinvariantEquiv
        (Submodule.Quotient.mk (D.indexFourSideLift N G)) := by
  rw [D.ellipticInteriorDegreeTwoFiberCoordinateHom_cuspToEllipticInteriorMap]
  exact D.indexFourFiberCoordinate_eq_sideLiftCoinvariantCoordinate N G

/-- Thus the missing scalar is equivalent to saying that the bridge's fourth side lift is the
positive normalized coinvariant generator. -/
public theorem ellipticInteriorDegreeTwoFiberCoordinateHom_indexFour_eq_one_iff
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    D.ellipticInteriorDegreeTwoFiberCoordinateHom N G
          (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 1 ↔
      Submodule.Quotient.mk (D.indexFourSideLift N G) =
        N.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.symm 1 := by
  rw [D.ellipticInteriorDegreeTwoFiberCoordinateHom_indexFour_eq_sideLift N G]
  constructor
  · intro h
    apply N.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.injective
    rw [h, LinearEquiv.apply_symm_apply]
  · intro h
    rw [h, LinearEquiv.apply_symm_apply]

/-- For every prism package over the bridge, its remaining coefficient calculation is exactly
the single assertion that the fourth side lift is the positive coinvariant generator. -/
public theorem normalizedIndexFourPrismCoefficientCalculation_iff_sideLiftGenerator
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N)
    (C : D.CuspEllipticMappingTorusPrismGeometricData N G) :
    D.NormalizedIndexFourPrismCoefficientCalculation C ↔
      Submodule.Quotient.mk (D.indexFourSideLift N G) =
        N.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.symm 1 := by
  have hCoordinate := D.indexFourFiberCoordinate_eq_sideLiftCoinvariantCoordinate N G
  have hPrism := indexFourPrismCoefficient_eq_cuspFiberCoordinate C
  constructor
  · intro I
    apply N.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    exact hCoordinate.symm.trans (hPrism.symm.trans I.coefficient)
  · intro h
    constructor
    calc
      _ = N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
          (D.cuspNormalizedDegreeTwoSplitting N G)
          (cuspToEllipticUnionHomology D 2
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) 0 := hPrism
      _ = N.actualHomologyCoordinates.degreeTwoCoinvariantEquiv
          (Submodule.Quotient.mk (D.indexFourSideLift N G)) := hCoordinate
      _ = N.actualHomologyCoordinates.degreeTwoCoinvariantEquiv
          (N.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.symm 1) := congrArg _ h
      _ = 1 := LinearEquiv.apply_symm_apply _ _

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end
