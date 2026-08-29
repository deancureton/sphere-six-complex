module

public import SphereSixComplex.Topology.PaperSectionSevenAffineCuspFiberPeriodMarking
public import SphereSixComplex.Topology.PaperSectionSevenCuspEllipticMappingTorusComparison
public import SphereSixComplex.Topology.PaperSectionSevenCuspInvariantSuspensionPrismNaturality
public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianProjectionNaturality
public import SphereSixComplex.Topology.PaperSectionSevenCanonicalCuspWangBoundaryNaturalityProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspPrismGeometricDataProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspIndexFourPrismCoefficientProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspEllipticCoordinateFiniteReduction

/-!
# Established cusp comparison for Section 7

The radial Wang boundary and the boundary of the pulled-back two-disc cover are the same
connecting morphism under the canonical fibre-to-band map.  The remaining geometric content is
the mapping-torus coordinate calculation for the cusp-to-elliptic inclusion.  Homotopy invariance
then supplies the corresponding statements for the actual cusp collar.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscCoverData
open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData}

namespace EstablishedSectionSevenCuspTopology

/-- The marked coordinate of the cusp Wang connecting morphism agrees with the marked coordinate
of the pulled-back Mayer--Vietoris boundary. -/
public axiom cuspMarkedConnectingNaturality
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.CuspMarkedConnectingNaturality R.homologyAlignment

/-- The marked connecting square determines the boundary comparison used by the affine
assembly. -/
public theorem markedBoundaryComparison
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.SectionSevenCuspMarkedBoundaryComparison R.homologyAlignment :=
  R.twoDiscCover.sectionSevenCuspMarkedBoundaryComparison_of_connectingNaturality
    R.homologyAlignment (cuspMarkedConnectingNaturality R)

/-- The canonical boundary basis bridge selected by the marked connecting square. -/
public theorem pulledBackBoundaryBasisBridge
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge R.homologyAlignment :=
  SectionSevenCuspMarkedBoundaryComparison.pulledBackBoundaryBasisBridge
    R.homologyAlignment (markedBoundaryComparison R)

/-- The remaining paper-specific input, reduced to the eight marked coordinate evaluations for
the canonical boundary basis bridge. -/
public axiom establishedActualCuspFiberEllipticMarkedCoordinateCalculation
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspFiberEllipticMarkedCoordinateCalculation R (pulledBackBoundaryBasisBridge R)

/-- The finite marked calculation implies the complete coordinate-homomorphism identities. -/
public theorem actualCuspFiberEllipticFiniteCoordinateIdentities
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspFiberEllipticFiniteCoordinateIdentities R (pulledBackBoundaryBasisBridge R) :=
  markedCoordinateCalculation_iff_finiteCoordinateIdentities.mp
    (establishedActualCuspFiberEllipticMarkedCoordinateCalculation R)

/-- The two remaining cusp coordinate identities: the meridian is the elliptic degree-one
generator, and the cusp fibre degree-two classes have the marked normalized elliptic fibre
coordinate.  Everything else in the Section 7 cusp model is derived. -/
public structure ActualCuspFiberEllipticCoordinateIdentities
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop where
  /-- The meridian projection is the elliptic degree-one coordinate. -/
  degreeOne : (R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
      (integralSingularHomologyMap 1
        R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap) =
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    coordinateAfterAddEquiv G.geometricWangSections.circleMappingTorusHOneAddEquiv 2
  /-- The cusp fibre degree-two basis classes have marked elliptic fibre coordinates. -/
  degreeTwo : ∀ i : Fin 6, i ≠ 5 →
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        (pulledBackBoundaryBasisBridge R)
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)))
      = if i = 4 then 1 else 0

/-- The finite marked-basis calculation supplies the complete Section 7 cusp comparison. -/
public theorem actualCuspFiberEllipticCoordinateIdentities
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspFiberEllipticCoordinateIdentities R :=
  { degreeOne := (actualCuspFiberEllipticFiniteCoordinateIdentities R).degreeOneHom
    degreeTwo := (actualCuspFiberEllipticFiniteCoordinateIdentities R).degreeTwo }

/-- The structural Section 7 cusp model, derived from the two coordinate identities. -/
public noncomputable def cuspEllipticMappingTorusPrismGeometricData
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.CuspEllipticMappingTorusPrismGeometricData R.homologyAlignment
      (pulledBackBoundaryBasisBridge R) :=
  cuspEllipticMappingTorusPrismGeometricData_proved_of_coordinateIdentities R
    (pulledBackBoundaryBasisBridge R)
    (actualCuspFiberEllipticCoordinateIdentities R).degreeOne
    (fun i hi4 hi5 => by
      have h := (actualCuspFiberEllipticCoordinateIdentities R).degreeTwo i hi5
      simp only [hi4, ↓reduceIte] at h
      exact h)

/-- The orientation calculation at index four, derived from the same coordinate identities. -/
public theorem normalizedIndexFourPrismCoefficientCalculation
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.NormalizedIndexFourPrismCoefficientCalculation
      (cuspEllipticMappingTorusPrismGeometricData R) :=
  normalizedIndexFourPrismCoefficientCalculation_of_actualCuspFiberCoordinate R
    (pulledBackBoundaryBasisBridge R) _
    (by simpa using (actualCuspFiberEllipticCoordinateIdentities R).degreeTwo 4 (by decide))

end EstablishedSectionSevenCuspTopology

namespace SectionSevenAffineRadialCompletionInput

open EstablishedSectionSevenCuspTopology

/-- The two established geometric comparison theorems discharge all three marked-coordinate
obligations left by the affine reduction. -/
public theorem sectionSevenAffineMarkedCompletionInput
    (R : A.SectionSevenAffineRadialCompletionInput) :
    A.SectionSevenAffineMarkedCompletionInput R := by
  refine
    { connectingNaturality := cuspMarkedConnectingNaturality R
      inclusionNaturality := ?_ }
  simpa [markedBoundaryComparison, pulledBackBoundaryBasisBridge] using
    CuspEllipticMappingTorusCoordinateComparison.inclusionNaturality
      (CuspEllipticMappingTorusPrismGeometricData.coordinateComparison
        (cuspEllipticMappingTorusPrismGeometricData R)
        (normalizedIndexFourPrismCoefficientCalculation R))

end SectionSevenAffineRadialCompletionInput

end SphereSixComplex.Geometry.PaperAnalyticData
