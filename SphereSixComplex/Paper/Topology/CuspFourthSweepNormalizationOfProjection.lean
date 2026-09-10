module
public import SphereSixComplex.Paper.Topology.CuspFourthSweepToricLift
public import SphereSixComplex.Paper.Topology.CuspFourthSweepFiberParity

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology CuspPuncturedCollarBridge
open SectionSevenEllipticTwoDiscCoverData

public theorem cuspFourthSweepClass_raw_fiber_zero_of_projection
    (A : PaperAnalyticData)
    (r : IntegralSingularHomology 2 (A.openEmbeddingStarData.filling 0) →+ (Fin 4 → ℤ))
    (hproj : ∀ x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      r (integralSingularHomologyMap 2 (A.openEmbeddingStarData.toFilling 0).hom x) =
        fun i : Fin 4 ↦ A.cuspRawHomologyTwoEquiv x (Fin.castAdd 2 i))
    (i : Fin 4) :
    A.cuspRawHomologyTwoEquiv (cuspFourthSweepClass A) (Fin.castAdd 2 i) = 0 := by
  have h := hproj (cuspFourthSweepClass A)
  have hz := cuspFourthSweep_filling_homology_zero A
    PositiveCircleCross.positiveCircleProductGenerator
  change integralSingularHomologyMap 2 (A.openEmbeddingStarData.toFilling 0).hom
    (cuspFourthSweepClass A) = 0 at hz
  rw [hz, map_zero] at h
  exact (congrFun h i).symm

public theorem cuspFourthSweepClass_eq_rawFive_of_projection
    (A : PaperAnalyticData)
    (r : IntegralSingularHomology 2 (A.openEmbeddingStarData.filling 0) →+ (Fin 4 → ℤ))
    (hproj : ∀ x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
      r (integralSingularHomologyMap 2 (A.openEmbeddingStarData.toFilling 0).hom x) =
        fun i : Fin 4 ↦ A.cuspRawHomologyTwoEquiv x (Fin.castAdd 2 i)) :
    cuspFourthSweepClass A =
      A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1) := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  apply A.cuspRawHomologyTwoEquiv.injective
  rw [A.cuspRawHomologyTwoEquiv.apply_symm_apply]
  have hw := actualCuspWangBoundaryHom_rawCoordinates A (cuspFourthSweepClass A)
  have hs := cuspFourthSweep_wang A
  dsimp only at hw
  change A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne
    (actualCuspWangBoundaryHom A (cuspFourthSweepClass A)) = Pi.single (3 : Fin 4) 1 at hs
  rw [hs] at hw
  ext i
  fin_cases i
  · exact cuspFourthSweepClass_raw_fiber_zero_of_projection A r hproj 0
  · exact cuspFourthSweepClass_raw_fiber_zero_of_projection A r hproj 1
  · exact cuspFourthSweepClass_raw_fiber_zero_of_projection A r hproj 2
  · exact cuspFourthSweepClass_raw_fiber_zero_of_projection A r hproj 3
  · exact (congrFun hw (2 : Fin 4)).symm
  · exact (congrFun hw (3 : Fin 4)).symm

end SphereSixComplex.Geometry.PaperAnalyticData
