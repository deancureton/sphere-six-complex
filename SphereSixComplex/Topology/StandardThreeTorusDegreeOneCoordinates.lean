module

public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasisProof

/-!
# Canonical degree-one coordinates on the standard three-torus
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.StandardTorusHomology

public def standardThreeTorusTailInclusionOne : C(StdTorus 3, StdTorus 4) where
  toFun z := Fin.cons 0 z
  continuous_toFun := by fun_prop

public def standardThreeTorusTailRetractionOne : C(StdTorus 4, StdTorus 3) where
  toFun := Fin.tail
  continuous_toFun := by fun_prop

private theorem tailRetraction_comp_inclusionOne :
    standardThreeTorusTailRetractionOne.comp standardThreeTorusTailInclusionOne =
      ContinuousMap.id _ := by
  ext z i
  rfl

private theorem tailInclusion_homologyOne_injective :
    Function.Injective
      (integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne) := by
  intro x y hxy
  have h := congrArg
    (integralSingularHomologyMap 1 standardThreeTorusTailRetractionOne) hxy
  rw [integralSingularHomologyMap_comp_wang, tailRetraction_comp_inclusionOne,
    integralSingularHomologyMap_id_wang] at h
  rw [integralSingularHomologyMap_comp_wang, tailRetraction_comp_inclusionOne,
    integralSingularHomologyMap_id_wang] at h
  exact h

public def standardThreeTorusDegreeOneCoordinateHom :
    IntegralSingularHomology 1 (StdTorus 3) →+ (Fin 3 → ℤ) where
  toFun x i := naturalStdTorusFourHomologyOne
    (integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne x) i.succ
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

private theorem subsingleton_homologyOne_standardPoint :
    Subsingleton (IntegralSingularHomology 1 (StdTorus 0)) := by
  simpa using subsingleton_homology_stdTorusZero 1 one_ne_zero

private def pointProjection : C(StdTorus 3, StdTorus 0) where
  toFun _ := 0
  continuous_toFun := continuous_const

private def pointToCircle : C(StdTorus 0, StdTorus 1) where
  toFun _ := 0
  continuous_toFun := continuous_const

private theorem headProjection_comp_tailInclusion :
    (standardFourTorusCoordinateProjection 0).comp standardThreeTorusTailInclusionOne =
      pointToCircle.comp pointProjection := by
  ext z
  rfl

private theorem headCoordinate_zero (x : IntegralSingularHomology 1 (StdTorus 3)) :
    naturalStdTorusFourHomologyOne
        (integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne x) 0 = 0 := by
  change standardFourTorusCoordinateHom
      (integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne x) 0 = 0
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1
        (StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph :
          C(StdTorus 1, UnitAddCircle))
        (integralSingularHomologyMap 1 (standardFourTorusCoordinateProjection 0)
          (integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne x))) = 0
  have hzProjection :
      integralSingularHomologyMap 1 (standardFourTorusCoordinateProjection 0)
          (integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne x) = 0 := by
    rw [integralSingularHomologyMap_comp_wang, headProjection_comp_tailInclusion,
      ← integralSingularHomologyMap_comp_wang]
    let _ := subsingleton_homologyOne_standardPoint
    have hz : integralSingularHomologyMap 1 pointProjection x = 0 := Subsingleton.elim _ _
    rw [hz, map_zero]
  rw [hzProjection, map_zero]
  exact map_zero _

public def standardThreeTorusCoordinateCircle (i : Fin 3) : C(StdTorus 1, StdTorus 3) :=
  standardThreeTorusTailRetractionOne.comp (standardFourTorusCoordinateCircle i.succ)

public def standardThreeTorusCoordinateHomologyClass (i : Fin 3) :
    IntegralSingularHomology 1 (StdTorus 3) :=
  integralSingularHomologyMap 1 (standardThreeTorusCoordinateCircle i)
    standardCircleHomologyGenerator

private theorem tailInclusion_comp_coordinateCircle (i : Fin 3) :
    standardThreeTorusTailInclusionOne.comp (standardThreeTorusCoordinateCircle i) =
      standardFourTorusCoordinateCircle i.succ := by
  ext z j
  fin_cases i <;> fin_cases j <;> rfl

@[simp]
public theorem standardThreeTorusDegreeOneCoordinateHom_coordinateClass (j : Fin 3) :
    standardThreeTorusDegreeOneCoordinateHom
        (standardThreeTorusCoordinateHomologyClass j) = Pi.single j 1 := by
  funext i
  change naturalStdTorusFourHomologyOne
      (integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne
        (integralSingularHomologyMap 1 (standardThreeTorusCoordinateCircle j)
          standardCircleHomologyGenerator)) i.succ = _
  rw [integralSingularHomologyMap_comp_wang, tailInclusion_comp_coordinateCircle]
  change standardFourTorusCoordinateHom
      (standardFourTorusCoordinateHomologyClass j.succ) i.succ = _
  rw [standardFourTorusCoordinateHom_coordinateHomologyClass]
  fin_cases i <;> fin_cases j <;> simp [Pi.single_apply]

public theorem standardThreeTorusDegreeOneCoordinateHom_surjective :
    Function.Surjective standardThreeTorusDegreeOneCoordinateHom := by
  intro v
  refine ⟨∑ i, v i • standardThreeTorusCoordinateHomologyClass i, ?_⟩
  rw [map_sum]
  simp only [map_zsmul, standardThreeTorusDegreeOneCoordinateHom_coordinateClass]
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

public theorem standardThreeTorusDegreeOneCoordinateHom_injective :
    Function.Injective standardThreeTorusDegreeOneCoordinateHom := by
  intro x y hxy
  apply tailInclusion_homologyOne_injective
  apply naturalStdTorusFourHomologyOne.injective
  funext i
  fin_cases i
  · exact (headCoordinate_zero x).trans (headCoordinate_zero y).symm
  · exact congrFun hxy 0
  · exact congrFun hxy 1
  · exact congrFun hxy 2

public noncomputable def standardThreeTorusHomologyOne :
    IntegralSingularHomology 1 (StdTorus 3) ≃+ (Fin 3 → ℤ) :=
  AddEquiv.ofBijective standardThreeTorusDegreeOneCoordinateHom
    ⟨standardThreeTorusDegreeOneCoordinateHom_injective,
      standardThreeTorusDegreeOneCoordinateHom_surjective⟩

public theorem standardThreeTorusTailInclusion_homologyOne_coordinates (x) :
    naturalStdTorusFourHomologyOne
        (integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne x) =
      ![0, standardThreeTorusHomologyOne x 0,
        standardThreeTorusHomologyOne x 1, standardThreeTorusHomologyOne x 2] := by
  funext i
  fin_cases i
  · exact headCoordinate_zero x
  · rfl
  · rfl
  · rfl

end SphereSixComplex.StandardTorusHomology

end

end
