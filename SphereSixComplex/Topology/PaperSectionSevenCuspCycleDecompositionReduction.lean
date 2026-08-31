module

public import SphereSixComplex.Topology.PaperSectionSevenCuspClutchingCompatibility

/-!
# Reduction of the cusp cycle decomposition

The swept coordinate in the degree-two cycle decomposition is already forced by the normalized
splitting and its Mayer--Vietoris boundary formula.  Thus the full cycle decomposition is
equivalent to the two marked naturality squares for the actual cusp-to-elliptic inclusion.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscHomologyCoordinates
open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData} {D : A.SectionSevenEllipticTwoDiscCoverData}
variable {N : A.EllipticBandHomologyAlignment D}
variable {G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- The degree-one fibre coordinate and the degree-two fibre coordinate determine the complete
cycle decomposition.  The swept coordinate follows from the boundary formula that defines the
normalized splitting. -/
public theorem SectionSevenEllipticInteriorCycleDecomposition.ofFiberScalarCoordinates
    (hOne : ∀ x : IntegralSingularHomology 1
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
          (cuspToEllipticUnionHomology D 1 x) 0 =
        actualCuspEllipticDegreeOneRawCoordinate (A.actualCuspRawHomologyOneEquiv x))
    (hTwoFiber : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
          (D.cuspNormalizedDegreeTwoSplitting N G)
          (cuspToEllipticUnionHomology D 2 x) 0 =
        actualCuspEllipticDegreeTwoFiberRawCoordinate (A.actualCuspRawHomologyTwoEquiv x)) :
    A.SectionSevenEllipticInteriorCycleDecomposition N.actualHomologyCoordinates
      (D.cuspNormalizedDegreeTwoSplitting N G) := by
  apply SectionSevenEllipticInteriorCycleDecomposition.ofRawScalarCoordinates hOne hTwoFiber
  intro x
  rw [N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv_one]
  exact D.cuspBoundaryCoordinateFormula N G x

/-- The two actual inclusion-naturality squares recover the full cycle decomposition. -/
public theorem SectionSevenCuspEllipticInclusionNaturality.cycleDecomposition
    (C : D.SectionSevenCuspEllipticInclusionNaturality N G) :
    A.SectionSevenEllipticInteriorCycleDecomposition N.actualHomologyCoordinates
      (D.cuspNormalizedDegreeTwoSplitting N G) := by
  apply SectionSevenEllipticInteriorCycleDecomposition.ofFiberScalarCoordinates
  · intro x
    have hx := DFunLike.congr_fun C.degreeOne x
    change D.ellipticInteriorDegreeOneCoordinateHom N
        (integralSingularHomologyMap 1 D.cuspToEllipticInteriorMap.hom x) = _ at hx
    rw [D.ellipticInteriorDegreeOneCoordinateHom_cuspToEllipticInteriorMap] at hx
    simpa [cuspDegreeOneCoordinateHom_apply,
      actualCuspEllipticDegreeOneCoordinateAfterAddEquiv] using hx
  · intro x
    have hx := DFunLike.congr_fun C.degreeTwoFiber x
    change D.ellipticInteriorDegreeTwoFiberCoordinateHom N G
        (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x) = _ at hx
    rw [D.ellipticInteriorDegreeTwoFiberCoordinateHom_cuspToEllipticInteriorMap] at hx
    simpa [cuspDegreeTwoFiberCoordinateHom_apply,
      actualCuspEllipticDegreeTwoFiberCoordinateAfterAddEquiv,
      SectionSevenEllipticTwoDiscCoverData.cuspNormalizedDegreeTwoSplitting] using hx

/-- For the cusp-normalized splitting, the cycle-level statement is exactly equivalent to the
two marked naturality squares for the actual inclusion map. -/
public theorem sectionSevenEllipticInteriorCycleDecomposition_iff_inclusionNaturality :
    A.SectionSevenEllipticInteriorCycleDecomposition N.actualHomologyCoordinates
        (D.cuspNormalizedDegreeTwoSplitting N G) ↔
      D.SectionSevenCuspEllipticInclusionNaturality N G :=
  ⟨fun C ↦ by
      exact {
        degreeOne := by
          ext x
          change D.ellipticInteriorDegreeOneCoordinateHom N
            (integralSingularHomologyMap 1 D.cuspToEllipticInteriorMap.hom x) = _
          rw [D.ellipticInteriorDegreeOneCoordinateHom_cuspToEllipticInteriorMap]
          have h := C.normalizedDegreeOne_onCuspCollar x
          simpa [cuspDegreeOneCoordinateHom_apply,
            actualCuspEllipticDegreeOneCoordinateAfterAddEquiv,
            sectionSevenFirstBoundaryHom_actualCusp_zero] using congrFun h 0
        degreeTwoFiber := by
          ext x
          change D.ellipticInteriorDegreeTwoFiberCoordinateHom N G
            (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x) = _
          rw [D.ellipticInteriorDegreeTwoFiberCoordinateHom_cuspToEllipticInteriorMap]
          have h := C.normalizedDegreeTwo_onCuspCollar x
          simpa [cuspDegreeTwoFiberCoordinateHom_apply,
            actualCuspEllipticDegreeTwoFiberCoordinateAfterAddEquiv,
            SectionSevenEllipticTwoDiscCoverData.cuspNormalizedDegreeTwoSplitting,
            sectionSevenMayerVietorisFinalTwoHom_actualCusp_zero] using congrFun h 0 },
    SectionSevenCuspEllipticInclusionNaturality.cycleDecomposition⟩

/-- The unmarked Wang comparison and the two actual inclusion squares directly supply the final
marked completion input; the intermediate full cycle-decomposition package is unnecessary. -/
public theorem SectionSevenCuspWangBandCompatibility.markedCompletionInput_of_inclusionNaturality
    {R : A.SectionSevenAffineRadialCompletionInput}
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment)
    (I : R.twoDiscCover.SectionSevenCuspEllipticInclusionNaturality R.homologyAlignment
      W.pulledBackBoundaryBasisBridge) :
    A.SectionSevenAffineMarkedCompletionInput R where
  connectingNaturality := W.connectingNaturality
  inclusionNaturality := I

end SphereSixComplex.Geometry.PaperAnalyticData

end
