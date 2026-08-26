module

public import SphereSixComplex.Topology.PaperSectionSevenPositiveDegreeCuspReduction

/-!
# Marked naturality for the cusp-to-elliptic inclusion

The two residual inclusion-coordinate identities can be stated directly for the actual map from
the cusp collar to the cusp-free elliptic interior.  This file proves that formulation equivalent
to the literal-union formulation used by the two-disc Mayer--Vietoris calculation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscHomologyCoordinates
open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

namespace SectionSevenEllipticTwoDiscCoverData

/-- The marked degree-one coordinate on the actual elliptic interior. -/
public noncomputable def ellipticInteriorDegreeOneCoordinateHom
    (N : A.EllipticBandHomologyAlignment D) :
    IntegralSingularHomology 1 A.SectionSevenEllipticInterior →+ ℤ :=
  coordinateAfterAddEquiv
    N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyOneEquiv 0

/-- The boundary formula selected by the marked cusp comparison. -/
public theorem cuspBoundaryCoordinateFormula
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    ∀ x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
          ((presentationTwo (D := D)).totalToInvariants
            (cuspToEllipticUnionHomology D 2 x)) =
        A.actualCuspRawHomologyTwoEquiv x 5 :=
  degreeTwoCuspBoundaryCoordinates_of_basis N
    (fun i ↦
      (SectionSevenCuspPulledBackBoundaryBasisBridge.mayerVietorisBridge N G).boundaryCoordinates
        N i)

/-- The degree-two splitting normalized by the positive cusp suspension class. -/
public noncomputable def cuspNormalizedDegreeTwoSplitting
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)) :=
  N.actualHomologyCoordinates.degreeTwoCuspE5SplittingOfCoordinates
    (D.cuspBoundaryCoordinateFormula N G)

/-- The marked fibre coordinate on degree-two homology of the actual elliptic interior. -/
public noncomputable def ellipticInteriorDegreeTwoFiberCoordinateHom
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    IntegralSingularHomology 2 A.SectionSevenEllipticInterior →+ ℤ :=
  coordinateAfterAddEquiv
    (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
      (D.cuspNormalizedDegreeTwoSplitting N G)) 0

/-- Pulling the actual elliptic degree-one coordinate back along the cusp inclusion gives the
literal-union coordinate already used by the Mayer--Vietoris calculation. -/
public theorem ellipticInteriorDegreeOneCoordinateHom_cuspToEllipticInteriorMap
    (N : A.EllipticBandHomologyAlignment D)
    (x : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0)) :
    D.ellipticInteriorDegreeOneCoordinateHom N
        (integralSingularHomologyMap 1 D.cuspToEllipticInteriorMap.hom x) =
      cuspDegreeOneCoordinateHom N x := by
  rw [D.cuspToEllipticInteriorMap_homology]
  let e := integralSingularHomologyEquiv 1
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  change N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
      (e.symm (e (cuspToEllipticUnionHomology D 1 x))) 0 = _
  rw [e.symm_apply_apply]
  rfl

/-- The analogous equality for the normalized degree-two fibre coordinate. -/
public theorem ellipticInteriorDegreeTwoFiberCoordinateHom_cuspToEllipticInteriorMap
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    D.ellipticInteriorDegreeTwoFiberCoordinateHom N G
        (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x) =
      cuspDegreeTwoFiberCoordinateHom N (D.cuspBoundaryCoordinateFormula N G) x := by
  rw [D.cuspToEllipticInteriorMap_homology]
  let e := integralSingularHomologyEquiv 2
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  change (N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
      (D.cuspNormalizedDegreeTwoSplitting N G))
        (e.symm (e (cuspToEllipticUnionHomology D 2 x))) 0 = _
  rw [e.symm_apply_apply]
  rfl

/-- Naturality of the two marked coordinates for the actual collar-to-elliptic-interior map. -/
public structure SectionSevenCuspEllipticInclusionNaturality
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) : Prop where
  degreeOne :
    (D.ellipticInteriorDegreeOneCoordinateHom N).comp
        (integralSingularHomologyMap 1 D.cuspToEllipticInteriorMap.hom) =
      coordinateAfterAddEquiv A.actualCuspRawHomologyOneEquiv 2
  degreeTwoFiber :
    (D.ellipticInteriorDegreeTwoFiberCoordinateHom N G).comp
        (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom) =
      coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 4

namespace SectionSevenCuspEllipticInclusionNaturality

variable {D : A.SectionSevenEllipticTwoDiscCoverData}
  {N : A.EllipticBandHomologyAlignment D}
  {G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- Actual-map naturality supplies the two inclusion identities used by the positive-degree
assembly. -/
public theorem toCoordinateComparison
    (C : D.SectionSevenCuspEllipticInclusionNaturality N G) :
    A.SectionSevenPositiveDegreeCuspCoordinateComparison N G where
  degreeOneCoordinateHom := by
    calc
      cuspDegreeOneCoordinateHom N =
          (D.ellipticInteriorDegreeOneCoordinateHom N).comp
            (integralSingularHomologyMap 1 D.cuspToEllipticInteriorMap.hom) := by
        ext x
        exact (D.ellipticInteriorDegreeOneCoordinateHom_cuspToEllipticInteriorMap N x).symm
      _ = coordinateAfterAddEquiv A.actualCuspRawHomologyOneEquiv 2 := C.degreeOne
  degreeTwoFiberCoordinateHom := by
    calc
      cuspDegreeTwoFiberCoordinateHom N (D.cuspBoundaryCoordinateFormula N G) =
          (D.ellipticInteriorDegreeTwoFiberCoordinateHom N G).comp
            (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom) := by
        ext x
        exact
          (D.ellipticInteriorDegreeTwoFiberCoordinateHom_cuspToEllipticInteriorMap N G x).symm
      _ = coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 4 := C.degreeTwoFiber

end SectionSevenCuspEllipticInclusionNaturality

namespace SectionSevenPositiveDegreeCuspCoordinateComparison

variable {D : A.SectionSevenEllipticTwoDiscCoverData}
  {N : A.EllipticBandHomologyAlignment D}
  {G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- The literal-union coordinate identities imply naturality for the actual inclusion map. -/
public theorem toCuspEllipticInclusionNaturality
    (C : A.SectionSevenPositiveDegreeCuspCoordinateComparison N G) :
    D.SectionSevenCuspEllipticInclusionNaturality N G where
  degreeOne := by
    calc
      (D.ellipticInteriorDegreeOneCoordinateHom N).comp
          (integralSingularHomologyMap 1 D.cuspToEllipticInteriorMap.hom) =
        cuspDegreeOneCoordinateHom N := by
          ext x
          exact D.ellipticInteriorDegreeOneCoordinateHom_cuspToEllipticInteriorMap N x
      _ = coordinateAfterAddEquiv A.actualCuspRawHomologyOneEquiv 2 :=
        C.degreeOneCoordinateHom
  degreeTwoFiber := by
    calc
      (D.ellipticInteriorDegreeTwoFiberCoordinateHom N G).comp
          (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom) =
        cuspDegreeTwoFiberCoordinateHom N (D.cuspBoundaryCoordinateFormula N G) := by
          ext x
          exact D.ellipticInteriorDegreeTwoFiberCoordinateHom_cuspToEllipticInteriorMap N G x
      _ = coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 4 :=
        C.degreeTwoFiberCoordinateHom

end SectionSevenPositiveDegreeCuspCoordinateComparison

/-- The two residual coordinate identities are exactly the marked naturality squares for the
actual cusp-to-elliptic-interior inclusion. -/
public theorem sectionSevenPositiveDegreeCuspCoordinateComparison_iff_inclusionNaturality
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) :
    A.SectionSevenPositiveDegreeCuspCoordinateComparison N G ↔
      D.SectionSevenCuspEllipticInclusionNaturality N G :=
  ⟨SectionSevenPositiveDegreeCuspCoordinateComparison.toCuspEllipticInclusionNaturality,
    SectionSevenCuspEllipticInclusionNaturality.toCoordinateComparison⟩

/-- The remaining positive-degree input stated entirely for actual maps: the marked Wang
boundary square and the two marked squares for the cusp-to-elliptic-interior inclusion. -/
public structure SectionSevenPositiveDegreeActualMapInput
    (N : A.EllipticBandHomologyAlignment D) : Prop where
  boundary : D.SectionSevenCuspMarkedBoundaryComparison N
  inclusion : D.SectionSevenCuspEllipticInclusionNaturality N
    (SectionSevenCuspMarkedBoundaryComparison.pulledBackBoundaryBasisBridge N boundary)

namespace SectionSevenPositiveDegreeActualMapInput

variable {D : A.SectionSevenEllipticTwoDiscCoverData}
  {N : A.EllipticBandHomologyAlignment D}

/-- The three actual-map naturality squares supply the production positive-degree assembly. -/
public noncomputable def positiveDegreeHomologyAssembly
    (C : D.SectionSevenPositiveDegreeActualMapInput N) :
    A.SectionSevenPositiveDegreeHomologyAssembly :=
  C.inclusion.toCoordinateComparison.toCuspBasisInput.positiveDegreeHomologyAssembly

end SectionSevenPositiveDegreeActualMapInput

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
