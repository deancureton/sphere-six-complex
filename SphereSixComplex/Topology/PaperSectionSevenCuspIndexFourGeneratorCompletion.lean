module

public import SphereSixComplex.Topology.PaperSectionSevenCuspIndexFourFromBasisBridgeCompletion
public import SphereSixComplex.Topology.PaperSectionSevenCuspEllipticMarkedCoordinateFullCompletion

/-!
# The index-four cusp coinvariant class

The pulled-back boundary bridge determines the quotient class of its selected side lift
independently of every existential choice.  Its identification with the positive normalized
generator is equivalent to one orientation identity in the Mayer--Vietoris total homology.
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

/-- Any side lift of the fourth raw cusp class has the same class in the degree-two
coinvariants as the lift selected by `indexFourSideLift`. -/
public theorem quotient_mk_eq_indexFourSideLift_of_inclusion
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N)
    (y : IntegralSingularHomology 2 D.orderThreeSide ×
      IntegralSingularHomology 2 D.orderFourSide)
    (hy : (presentationTwo (D := D)).inclusion y =
      cuspToEllipticUnionHomology D 2
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) :
    (Submodule.Quotient.mk y : (presentationTwo (D := D)).Coinvariants) =
      (Submodule.Quotient.mk (D.indexFourSideLift N G) :
        (presentationTwo (D := D)).Coinvariants) := by
  apply (presentationTwo (D := D)).coinvariantsToTotal_injective
  calc
    (presentationTwo (D := D)).coinvariantsToTotal (Submodule.Quotient.mk y) =
        (presentationTwo (D := D)).inclusion y := rfl
    _ = cuspToEllipticUnionHomology D 2
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) := hy
    _ = (presentationTwo (D := D)).inclusion (D.indexFourSideLift N G) :=
      (D.inclusion_indexFourSideLift N G).symm
    _ = (presentationTwo (D := D)).coinvariantsToTotal
        (Submodule.Quotient.mk (D.indexFourSideLift N G)) := rfl

/-- The quotient class selected at index four is independent of the proof of the pulled-back
boundary basis bridge. -/
public theorem indexFourSideLift_quotient_independent_of_bridge
    (N : A.EllipticBandHomologyAlignment D)
    (G H : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    (Submodule.Quotient.mk (D.indexFourSideLift N G) :
        (presentationTwo (D := D)).Coinvariants) =
      (Submodule.Quotient.mk (D.indexFourSideLift N H) :
        (presentationTwo (D := D)).Coinvariants) :=
  (D.quotient_mk_eq_indexFourSideLift_of_inclusion N H
    (D.indexFourSideLift N G) (D.inclusion_indexFourSideLift N G))

/-- Basis-independent uniqueness: a coinvariant is the class of the selected fourth side lift
exactly when its canonical image in total homology is the fourth raw cusp class. -/
public theorem indexFourSideLift_quotient_eq_iff_coinvariantsToTotal
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N)
    (c : (presentationTwo (D := D)).Coinvariants) :
    Submodule.Quotient.mk (D.indexFourSideLift N G) = c ↔
      cuspToEllipticUnionHomology D 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) =
        (presentationTwo (D := D)).coinvariantsToTotal c := by
  constructor
  · intro h
    calc
      cuspToEllipticUnionHomology D 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) =
          (presentationTwo (D := D)).inclusion (D.indexFourSideLift N G) :=
        (D.inclusion_indexFourSideLift N G).symm
      _ = (presentationTwo (D := D)).coinvariantsToTotal
          (Submodule.Quotient.mk (D.indexFourSideLift N G)) := rfl
      _ = (presentationTwo (D := D)).coinvariantsToTotal c := congrArg _ h
  · intro h
    apply (presentationTwo (D := D)).coinvariantsToTotal_injective
    calc
      (presentationTwo (D := D)).coinvariantsToTotal
          (Submodule.Quotient.mk (D.indexFourSideLift N G)) =
          (presentationTwo (D := D)).inclusion (D.indexFourSideLift N G) := rfl
      _ = cuspToEllipticUnionHomology D 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) :=
        D.inclusion_indexFourSideLift N G
      _ = (presentationTwo (D := D)).coinvariantsToTotal c := h

/-- The requested positive-generator identity is exactly the orientation of the fourth raw cusp
class relative to the normalized degree-two coinvariant generator. -/
public theorem indexFourSideLift_quotient_eq_generator_iff_total_orientation
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    Submodule.Quotient.mk (D.indexFourSideLift N G) =
        N.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.symm 1 ↔
      cuspToEllipticUnionHomology D 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) =
        (presentationTwo (D := D)).coinvariantsToTotal
          (N.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.symm 1) :=
  D.indexFourSideLift_quotient_eq_iff_coinvariantsToTotal N G _

/-- For any prism geometry, the normalized index-four coefficient is equivalent to the same
single total-homology orientation identity. -/
public theorem normalizedIndexFourPrismCoefficientCalculation_iff_total_orientation
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N)
    (C : D.CuspEllipticMappingTorusPrismGeometricData N G) :
    D.NormalizedIndexFourPrismCoefficientCalculation C ↔
      cuspToEllipticUnionHomology D 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) =
        (presentationTwo (D := D)).coinvariantsToTotal
          (N.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.symm 1) := by
  rw [D.normalizedIndexFourPrismCoefficientCalculation_iff_sideLiftGenerator N G C]
  exact D.indexFourSideLift_quotient_eq_generator_iff_total_orientation N G

end SectionSevenEllipticTwoDiscCoverData

namespace EstablishedSectionSevenCuspTopology

/-- Specializing the uniqueness theorem to the prism geometry constructed from the topological
cusp--band square and meridian projection leaves exactly the total-homology orientation of the
fourth raw cusp class. -/
public theorem normalizedIndexFourPrismCoefficientCalculation_existingGeometry_iff_orientation
    (R : A.SectionSevenAffineRadialCompletionInput)
    (G : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge R.homologyAlignment)
    (hTop : R.twoDiscCover.CanonicalCuspFiberBandTopologicalCompatibility)
    (M : R.twoDiscCover.CuspEllipticMappingTorusMeridianProjectionComparison
      R.homologyAlignment) :
    R.twoDiscCover.NormalizedIndexFourPrismCoefficientCalculation
          (cuspPrismGeometryOfExistingFiberValues R G hTop M) ↔
      cuspToEllipticUnionHomology R.twoDiscCover 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) =
        (presentationTwo (D := R.twoDiscCover)).coinvariantsToTotal
          (R.homologyAlignment.actualHomologyCoordinates.degreeTwoCoinvariantEquiv.symm 1) :=
  R.twoDiscCover.normalizedIndexFourPrismCoefficientCalculation_iff_total_orientation
    R.homologyAlignment G _

end EstablishedSectionSevenCuspTopology

end SphereSixComplex.Geometry.PaperAnalyticData

end
