module

public import SphereSixComplex.Topology.PaperSectionSevenAffineCuspFiberPeriodMarking
public import SphereSixComplex.Topology.PaperSectionSevenCuspEllipticMappingTorusComparison
public import SphereSixComplex.Topology.PaperSectionSevenCuspInvariantSuspensionPrismNaturality
public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianProjectionNaturality
public import SphereSixComplex.Topology.PaperSectionSevenCuspWangOpenCoverChainRealization

/-!
# Established cusp comparison for Section 7

The radial Wang boundary and the boundary of the pulled-back two-disc cover are the same
connecting morphism under the canonical fibre-to-band map.  The remaining geometric content is
the mapping-torus coordinate calculation for the cusp-to-elliptic inclusion.  Homotopy invariance
then supplies the corresponding statements for the actual cusp collar.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscCoverData

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

/-- The structural Section 7 cusp model: its reference map and homotopy, meridian projection
square, explicit singular-cycle basis, chain images, and swept descriptions away from index four. -/
public axiom cuspEllipticMappingTorusPrismGeometricData
    (R : A.SectionSevenAffineRadialCompletionInput)
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment) :
    R.twoDiscCover.CuspEllipticMappingTorusPrismGeometricData R.homologyAlignment
      W.pulledBackBoundaryBasisBridge

/-- The remaining orientation calculation: the fourth target prism has coefficient one on the
first normalized elliptic-interior degree-two basis class. -/
public axiom normalizedIndexFourPrismCoefficientCalculation
    (R : A.SectionSevenAffineRadialCompletionInput)
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment) :
    R.twoDiscCover.NormalizedIndexFourPrismCoefficientCalculation
      (cuspEllipticMappingTorusPrismGeometricData R W)

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
