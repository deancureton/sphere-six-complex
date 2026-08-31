module

public import SphereSixComplex.Topology.PaperSectionSevenCuspIndexFourGeneratorCompletion

/-!
# The canonical positive side lift of the first cusp suspension

The finite-cover coordinates select a unique side-homology class with coordinates
`(0, -1, 1, 0)`.  The remaining index-four scalar is exactly the geometric assertion that the
inclusion of this class is the first invariant-suspension cusp class.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticInteriorMarkedCycleData
open SectionSevenEllipticTwoDiscCoverData
open SectionSevenEllipticTwoDiscHomologyCoordinates

variable {A : PaperAnalyticData}

namespace EstablishedSectionSevenCuspTopology

/-- The unique side-homology class with the primitive positive index-four coordinates. -/
public noncomputable def actualCuspIndexFourPositiveSideLift
    (R : A.SectionSevenAffineRadialCompletionInput) :
    IntegralSingularHomology 2 R.twoDiscCover.orderThreeSide ×
      IntegralSingularHomology 2 R.twoDiscCover.orderFourSide :=
  R.homologyAlignment.actualHomologyCoordinates.sidesTwo.symm
    positiveIndexFourSideCoordinate

/-- The canonical side lift has coordinates `(0, -1, 1, 0)`. -/
public theorem actualCuspIndexFourPositiveSideLift_coordinate
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.homologyAlignment.actualHomologyCoordinates.sidesTwo
        (actualCuspIndexFourPositiveSideLift R) =
      positiveIndexFourSideCoordinate :=
  R.homologyAlignment.actualHomologyCoordinates.sidesTwo.apply_symm_apply _

/-- The canonical side lift represents the positive generator of the degree-two
coinvariants. -/
public theorem actualCuspIndexFourPositiveSideLift_quotient_generator
    (R : A.SectionSevenAffineRadialCompletionInput) :
    (Submodule.Quotient.mk (actualCuspIndexFourPositiveSideLift R) :
        (presentationTwo (D := R.twoDiscCover)).Coinvariants) =
      R.homologyAlignment.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.symm 1 := by
  apply R.homologyAlignment.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  change alphaTwoFunctional
    (R.homologyAlignment.actualHomologyCoordinates.sidesTwo
      (actualCuspIndexFourPositiveSideLift R)) = 1
  rw [actualCuspIndexFourPositiveSideLift_coordinate]
  exact alphaTwoFunctional_positiveIndexFourSideCoordinate

/-- The index-four coordinate is one exactly when the canonical positive side lift includes to
the first invariant-suspension cusp class.  Thus the right-hand equality is the smallest exact
geometric realization statement still required by the current chain-level API. -/
public theorem actualCuspDegreeTwoIndexFour_iff_positiveSideLift_inclusion
    (R : A.SectionSevenAffineRadialCompletionInput)
    (G : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment) :
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
          G
          (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 1 ↔
      (presentationTwo (D := R.twoDiscCover)).inclusion
          (actualCuspIndexFourPositiveSideLift R) =
        cuspToEllipticUnionHomology R.twoDiscCover 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) := by
  rw [R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom_indexFour_eq_one_iff
    R.homologyAlignment G,
    R.twoDiscCover.indexFourSideLift_quotient_eq_generator_iff_total_orientation
      R.homologyAlignment G]
  let y := actualCuspIndexFourPositiveSideLift R
  have hyq : (Submodule.Quotient.mk y :
        (presentationTwo (D := R.twoDiscCover)).Coinvariants) =
      R.homologyAlignment.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.symm 1 :=
    actualCuspIndexFourPositiveSideLift_quotient_generator R
  constructor
  · intro h
    calc
      (presentationTwo (D := R.twoDiscCover)).inclusion y =
          (presentationTwo (D := R.twoDiscCover)).coinvariantsToTotal
            (Submodule.Quotient.mk y) := rfl
      _ = (presentationTwo (D := R.twoDiscCover)).coinvariantsToTotal
          (R.homologyAlignment.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.symm 1) :=
        congrArg _ hyq
      _ = cuspToEllipticUnionHomology R.twoDiscCover 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) := h.symm
  · intro h
    calc
      cuspToEllipticUnionHomology R.twoDiscCover 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) =
          (presentationTwo (D := R.twoDiscCover)).inclusion y := h.symm
      _ = (presentationTwo (D := R.twoDiscCover)).coinvariantsToTotal
          (Submodule.Quotient.mk y) := rfl
      _ = (presentationTwo (D := R.twoDiscCover)).coinvariantsToTotal
          (R.homologyAlignment.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.symm 1) :=
        congrArg _ hyq

end EstablishedSectionSevenCuspTopology

end SphereSixComplex.Geometry.PaperAnalyticData

end
