module
public import SphereSixComplex.Topology.CuspFourthSweepToricLift
public import SphereSixComplex.Topology.CuspFourthSweepFiberParity

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology CuspPuncturedCollarBridge
open SectionSevenEllipticTwoDiscCoverData

public theorem actualCuspFourthSweepClass_raw_fiber_zero_of_projection
    (A : PaperAnalyticData)
    (r : IntegralSingularHomology 2 (A.openEmbeddingStarData.filling 0) →+ (Fin 4 → ℤ))
    (hproj : ∀ x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      r (integralSingularHomologyMap 2 (A.openEmbeddingStarData.toFilling 0).hom x) =
        fun i : Fin 4 ↦ A.actualCuspRawHomologyTwoEquiv x (Fin.castAdd 2 i))
    (i : Fin 4) :
    A.actualCuspRawHomologyTwoEquiv (actualCuspFourthSweepClass A) (Fin.castAdd 2 i) = 0 := by
  have h := hproj (actualCuspFourthSweepClass A)
  have hz := actualCuspFourthSweep_filling_homology_zero A
    PositiveCircleCross.positiveCircleProductGenerator
  change integralSingularHomologyMap 2 (A.openEmbeddingStarData.toFilling 0).hom
    (actualCuspFourthSweepClass A) = 0 at hz
  rw [hz, map_zero] at h
  exact (congrFun h i).symm

public theorem actualCuspFourthSweepClass_eq_rawFive_of_projection
    (A : PaperAnalyticData)
    (r : IntegralSingularHomology 2 (A.openEmbeddingStarData.filling 0) →+ (Fin 4 → ℤ))
    (hproj : ∀ x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      r (integralSingularHomologyMap 2 (A.openEmbeddingStarData.toFilling 0).hom x) =
        fun i : Fin 4 ↦ A.actualCuspRawHomologyTwoEquiv x (Fin.castAdd 2 i)) :
    actualCuspFourthSweepClass A =
      A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1) := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  apply A.actualCuspRawHomologyTwoEquiv.injective
  rw [A.actualCuspRawHomologyTwoEquiv.apply_symm_apply]
  have hw := actualCuspWangBoundaryHom_rawCoordinates A (actualCuspFourthSweepClass A)
  have hs := actualCuspFourthSweep_wang A
  dsimp only at hw
  change A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne
    (actualCuspWangBoundaryHom A (actualCuspFourthSweepClass A)) = Pi.single (3 : Fin 4) 1 at hs
  rw [hs] at hw
  ext i
  fin_cases i
  · exact actualCuspFourthSweepClass_raw_fiber_zero_of_projection A r hproj 0
  · exact actualCuspFourthSweepClass_raw_fiber_zero_of_projection A r hproj 1
  · exact actualCuspFourthSweepClass_raw_fiber_zero_of_projection A r hproj 2
  · exact actualCuspFourthSweepClass_raw_fiber_zero_of_projection A r hproj 3
  · exact (congrFun hw (2 : Fin 4)).symm
  · exact (congrFun hw (3 : Fin 4)).symm

end SphereSixComplex.Geometry.PaperAnalyticData
