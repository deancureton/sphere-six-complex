module

public import SphereSixComplex.Topology.PaperSectionSevenAffineCuspFiberPeriodMarking
public import SphereSixComplex.Topology.PaperSectionSevenCuspEllipticMappingTorusComparison
public import SphereSixComplex.Topology.PaperSectionSevenCuspInvariantSuspensionPrismNaturality
public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianProjectionNaturality
public import SphereSixComplex.Topology.PaperSectionSevenCuspWangOpenCoverChainRealization
public import SphereSixComplex.Topology.PaperSectionSevenCuspPrismGeometricDataProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspIndexFourPrismCoefficientProof

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

/-- Naturality of the connecting morphism for the canonical map from the radial cusp cover to
the affine two-disc cover. -/
public theorem canonicalWangBoundaryNaturality
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.CanonicalCuspWangBoundaryNaturality :=
  ActualCuspWangOpenCoverChainRealization.canonicalWangBoundaryNaturality
    R.twoDiscCover
    (EstablishedActualCuspWangOpenCoverChainRealization.realization R.twoDiscCover)

/-- The two remaining cusp coordinate identities: the meridian is the elliptic degree-one
generator, and the cusp fibre degree-two classes have the marked normalized elliptic fibre
coordinate.  Everything else in the Section 7 cusp model is derived. -/
public structure ActualCuspFiberEllipticCoordinateIdentities
    (R : A.SectionSevenAffineRadialCompletionInput)
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment) : Prop where
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
        W.pulledBackBoundaryBasisBridge
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)))
      = if i = 4 then 1 else 0

/-- The remaining geometric input for the Section 7 cusp comparison. -/
public axiom actualCuspFiberEllipticCoordinateIdentities
    (R : A.SectionSevenAffineRadialCompletionInput)
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment) :
    ActualCuspFiberEllipticCoordinateIdentities R W

/-- The structural Section 7 cusp model, derived from the two coordinate identities. -/
public noncomputable def cuspEllipticMappingTorusPrismGeometricData
    (R : A.SectionSevenAffineRadialCompletionInput)
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment) :
    R.twoDiscCover.CuspEllipticMappingTorusPrismGeometricData R.homologyAlignment
      W.pulledBackBoundaryBasisBridge :=
  cuspEllipticMappingTorusPrismGeometricData_proved_of_coordinateIdentities R W
    (actualCuspFiberEllipticCoordinateIdentities R W).degreeOne
    (fun i hi4 hi5 => by
      have h := (actualCuspFiberEllipticCoordinateIdentities R W).degreeTwo i hi5
      simp only [hi4, ↓reduceIte] at h
      exact h)

/-- The orientation calculation at index four, derived from the same coordinate identities. -/
public theorem normalizedIndexFourPrismCoefficientCalculation
    (R : A.SectionSevenAffineRadialCompletionInput)
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment) :
    R.twoDiscCover.NormalizedIndexFourPrismCoefficientCalculation
      (cuspEllipticMappingTorusPrismGeometricData R W) :=
  normalizedIndexFourPrismCoefficientCalculation_of_actualCuspFiberCoordinate R W _
    (by simpa using (actualCuspFiberEllipticCoordinateIdentities R W).degreeTwo 4 (by decide))

end EstablishedSectionSevenCuspTopology

namespace SectionSevenAffineRadialCompletionInput

open EstablishedSectionSevenCuspTopology

/-- The established Section 7 cusp comparison supplies the complete unmarked clutching package
for the actual affine radial cover. -/
public noncomputable def sectionSevenCuspClutchingCompatibility
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.SectionSevenCuspClutchingCompatibility R.homologyAlignment := by
  let hOrderThree := R.canonicalCuspFiberOrderThreePeriodMarking
    A.actualCuspFiberPeriodMarkingCompatibility
  let hMarking := R.twoDiscCover.canonicalCuspFiberBandPeriodMarking_of_orderThree
    R.homologyAlignment hOrderThree
  let wang := R.twoDiscCover.sectionSevenCuspWangBandCompatibility_of_canonicalMap
    R.homologyAlignment
    (EstablishedSectionSevenCuspTopology.canonicalWangBoundaryNaturality R)
    hMarking
  exact
    { wangBand := wang
      cycleDecomposition :=
        SectionSevenCuspEllipticInclusionNaturality.cycleDecomposition
          (CuspEllipticMappingTorusCoordinateComparison.inclusionNaturality
            (CuspEllipticMappingTorusPrismGeometricData.coordinateComparison
              (cuspEllipticMappingTorusPrismGeometricData R wang)
              (normalizedIndexFourPrismCoefficientCalculation R wang))) }

/-- The two established geometric comparison theorems discharge all three marked-coordinate
obligations left by the affine reduction. -/
public theorem sectionSevenAffineMarkedCompletionInput
    (R : A.SectionSevenAffineRadialCompletionInput) :
    A.SectionSevenAffineMarkedCompletionInput R :=
  R.sectionSevenCuspClutchingCompatibility.markedCompletionInput

end SectionSevenAffineRadialCompletionInput

end SphereSixComplex.Geometry.PaperAnalyticData
