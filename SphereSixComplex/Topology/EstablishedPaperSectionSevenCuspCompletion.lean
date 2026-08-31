module

public import SphereSixComplex.Topology.PaperSectionSevenAffineCuspFiberPeriodMarking
public import SphereSixComplex.Topology.PaperSectionSevenCuspEllipticMappingTorusComparison
public import SphereSixComplex.Topology.PaperSectionSevenCuspInvariantSuspensionPrismNaturality
public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianProjectionNaturality
public import SphereSixComplex.Topology.PaperSectionSevenCanonicalCuspWangBoundaryNaturalityProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspMarkedConnectingNaturalityProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspPrismGeometricDataProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspIndexFourPrismCoefficientProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspEllipticCoordinateFiniteReduction
public import SphereSixComplex.Topology.PaperSectionSevenCuspDegreeOneIndexTwoProof

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

/-- The remaining two pulled-back Mayer--Vietoris boundary evaluations on the invariant raw
degree-two basis.  The explicit cover calculation proves the other four basis cases, while the
Wang presentation identifies its marked composite with the last raw coordinate. -/
public axiom establishedCuspPulledBackMarkedInvariantBasisData
    (R : A.SectionSevenAffineRadialCompletionInput) :
    CuspPulledBackMarkedInvariantBasisData R

/-- The marked coordinate of the cusp Wang connecting morphism agrees with the marked coordinate
of the pulled-back Mayer--Vietoris boundary. -/
public theorem cuspMarkedConnectingNaturality
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.CuspMarkedConnectingNaturality R.homologyAlignment :=
  cuspMarkedConnectingNaturality_of_invariantBasisData R
    (establishedCuspPulledBackMarkedInvariantBasisData R)

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

/-- The two geometric statements not supplied by the canonical cusp--band compatibility: the
finite-meridian full-iterate relation and the orientation of the first invariant-suspension
class. -/
public structure ActualCuspFiberEllipticMarkedCoordinateResidual
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop where
  degreeOneFullIterateRelation : ActualCuspDegreeOneIndexTwoFullIterateRelation R
  degreeTwoIndexFour :
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        (pulledBackBoundaryBasisBridge R)
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 1

/-- The remaining paper-specific input after the six fibre-coordinate evaluations supplied by
the canonical cusp--band compatibility. -/
public axiom establishedActualCuspFiberEllipticMarkedCoordinateResidual
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspFiberEllipticMarkedCoordinateResidual R

/-- The two residual geometric statements and the proved canonical cusp--band compatibility give
the complete marked-coordinate calculation for the canonical boundary basis bridge. -/
public theorem actualCuspFiberEllipticMarkedCoordinateCalculation_of_residual
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspFiberEllipticMarkedCoordinateResidual R) :
    ActualCuspFiberEllipticMarkedCoordinateCalculation R (pulledBackBoundaryBasisBridge R) := by
  let hTop := canonicalCuspFiberBandTopologicalCompatibility R
  let S := R.twoDiscCover.cuspNormalizedDegreeTwoSplitting R.homologyAlignment
    (pulledBackBoundaryBasisBridge R)
  refine ⟨?_, ?_, C.degreeTwoIndexFour⟩
  · intro i
    fin_cases i
    · simpa [SectionSevenEllipticTwoDiscCoverData.ellipticInteriorDegreeOneCoordinateHom,
        coordinateAfterAddEquiv_apply, actualCuspEllipticDegreeOneRawCoordinate] using congrFun
        (affineActualCuspDegreeOneFiberBasis_scalarValues R hTop) 0
    · simpa [SectionSevenEllipticTwoDiscCoverData.ellipticInteriorDegreeOneCoordinateHom,
        coordinateAfterAddEquiv_apply, actualCuspEllipticDegreeOneRawCoordinate] using congrFun
        (affineActualCuspDegreeOneFiberBasis_scalarValues R hTop) 1
    · have h := (actualCuspDegreeOneIndexTwo_iff_fullIterateRelation R).mpr
          C.degreeOneFullIterateRelation
      simpa [actualCuspEllipticDegreeOneRawCoordinate] using h
  · intro i hi4 hi5
    fin_cases i
    · rw [← cuspMappingTorusToEllipticInteriorMap_basis]
      simpa [SectionSevenEllipticTwoDiscCoverData.ellipticInteriorDegreeTwoFiberCoordinateHom,
        coordinateAfterAddEquiv_apply, actualCuspEllipticDegreeTwoFiberRawCoordinate] using
        congrFun (affineActualCuspDegreeTwoFiberBasis_scalarValues R S hTop) 0
    · rw [← cuspMappingTorusToEllipticInteriorMap_basis]
      simpa [SectionSevenEllipticTwoDiscCoverData.ellipticInteriorDegreeTwoFiberCoordinateHom,
        coordinateAfterAddEquiv_apply, actualCuspEllipticDegreeTwoFiberRawCoordinate] using
        congrFun (affineActualCuspDegreeTwoFiberBasis_scalarValues R S hTop) 1
    · rw [← cuspMappingTorusToEllipticInteriorMap_basis]
      simpa [SectionSevenEllipticTwoDiscCoverData.ellipticInteriorDegreeTwoFiberCoordinateHom,
        coordinateAfterAddEquiv_apply, actualCuspEllipticDegreeTwoFiberRawCoordinate] using
        congrFun (affineActualCuspDegreeTwoFiberBasis_scalarValues R S hTop) 2
    · rw [← cuspMappingTorusToEllipticInteriorMap_basis]
      simpa [SectionSevenEllipticTwoDiscCoverData.ellipticInteriorDegreeTwoFiberCoordinateHom,
        coordinateAfterAddEquiv_apply, actualCuspEllipticDegreeTwoFiberRawCoordinate] using
        congrFun (affineActualCuspDegreeTwoFiberBasis_scalarValues R S hTop) 3
    · exact (hi4 rfl).elim
    · exact (hi5 rfl).elim

/-- The two-statement residual is exactly equivalent to the former eight-value package because
the other six evaluations are now theorems. -/
public theorem actualCuspFiberEllipticMarkedCoordinateCalculation_iff_residual
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspFiberEllipticMarkedCoordinateCalculation R (pulledBackBoundaryBasisBridge R) ↔
      ActualCuspFiberEllipticMarkedCoordinateResidual R := by
  constructor
  · intro C
    refine ⟨?_, C.degreeTwoIndexFour⟩
    apply (actualCuspDegreeOneIndexTwo_iff_fullIterateRelation R).mp
    simpa [actualCuspEllipticDegreeOneRawCoordinate] using C.degreeOne 2
  · exact actualCuspFiberEllipticMarkedCoordinateCalculation_of_residual R

/-- The established two-value residue supplies the complete marked-coordinate calculation. -/
public theorem establishedActualCuspFiberEllipticMarkedCoordinateCalculation
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspFiberEllipticMarkedCoordinateCalculation R (pulledBackBoundaryBasisBridge R) :=
  actualCuspFiberEllipticMarkedCoordinateCalculation_of_residual R
    (establishedActualCuspFiberEllipticMarkedCoordinateResidual R)

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
    actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
      G.geometricWangSections.circleMappingTorusHOneAddEquiv
  /-- The cusp fibre degree-two basis classes have marked elliptic fibre coordinates. -/
  degreeTwo : ∀ i : Fin 6, i ≠ 5 →
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        (pulledBackBoundaryBasisBridge R)
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)))
      = actualCuspEllipticDegreeTwoFiberRawCoordinate (Pi.single i 1)

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
    (fun i _hi4 hi5 ↦ (actualCuspFiberEllipticCoordinateIdentities R).degreeTwo i hi5)

/-- The orientation calculation at index four, derived from the same coordinate identities. -/
public theorem normalizedIndexFourPrismCoefficientCalculation
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.NormalizedIndexFourPrismCoefficientCalculation
      (cuspEllipticMappingTorusPrismGeometricData R) :=
  normalizedIndexFourPrismCoefficientCalculation_of_actualCuspFiberCoordinate R
    (pulledBackBoundaryBasisBridge R) _
    (by
      simpa [actualCuspEllipticDegreeTwoFiberRawCoordinate] using
        (actualCuspFiberEllipticCoordinateIdentities R).degreeTwo 4 (by decide))

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
