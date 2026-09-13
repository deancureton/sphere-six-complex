module

public import SphereSixComplex.Prerequisites.Topology.StandardThreeTorusDegreeOneCoordinates
public import SphereSixComplex.Prerequisites.Topology.StandardThreeTorusDegreeTwoCoordinates

/-! # Coordinate generators and projection of the three-torus -/

@[expose] public section
noncomputable section
open AlgebraicTopology

namespace SphereSixComplex.StandardTorusHomology

theorem homologyOne_eq_sum_coordinateClasses (x : IntegralSingularHomology 1 (StdTorus 3)) :
    x = ∑ i, standardThreeTorusDegreeOneCoordinateHom x i •
      standardThreeTorusCoordinateHomologyClass i := by
  apply standardThreeTorusDegreeOneCoordinateHom_injective
  rw [map_sum]
  simp only [map_zsmul, standardThreeTorusDegreeOneCoordinateHom_coordinateClass]
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

theorem homologyTwo_eq_sum_coordinateClasses (x : IntegralSingularHomology 2 (StdTorus 3)) :
    x = ∑ i, standardThreeTorusDegreeTwoCoordinateHom x i •
      standardThreeTorusCoordinateTwoTorusHomologyClass i := by
  apply standardThreeTorusDegreeTwoCoordinateHom_injective
  rw [map_sum]
  simp only [map_zsmul, standardThreeTorusDegreeTwoCoordinateHom_coordinateClass]
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

/-- Forget the first circle, retaining the two phase coordinates. -/
def threeTorusTailProjection : C(StdTorus 3, StdTorus 2) where
  toFun := Fin.tail
  continuous_toFun := by fun_prop

private def projectedPairMatrix (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![0, 1; 0, 0], !![0, 0; 0, 1], 1] i

private theorem tailProjection_comp_coordinateTwoTorus (i : Fin 3) :
    threeTorusTailProjection.comp (standardThreeTorusCoordinateTwoTorus i) =
      standardTwoTorusMatrixMap (projectedPairMatrix i) := by
  fin_cases i <;> ext z k <;> fin_cases k
  · change z 1 = ∑ b : Fin 2, (![0, 1] : Fin 2 → ℤ) b • z b
    simp [Fin.sum_univ_two]
  · change 0 = ∑ b : Fin 2, (![0, 0] : Fin 2 → ℤ) b • z b
    simp [Fin.sum_univ_two]
  · change 0 = ∑ b : Fin 2, (![0, 0] : Fin 2 → ℤ) b • z b
    simp [Fin.sum_univ_two]
  · change z 1 = ∑ b : Fin 2, (![0, 1] : Fin 2 → ℤ) b • z b
    simp [Fin.sum_univ_two]
  · change z 0 = ∑ b : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 b • z b
    simp [Fin.sum_univ_two]
  · change z 1 = ∑ b : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 b • z b
    simp [Fin.sum_univ_two]

@[simp] theorem threeTorusTailProjection_homologyTwo_coordinateClass (i : Fin 3) :
    integralSingularHomologyMap 2 threeTorusTailProjection
      (standardThreeTorusCoordinateTwoTorusHomologyClass i) =
      if i = 2 then standardTwoTorusHomologyGenerator else 0 := by
  change integralSingularHomologyMap 2 threeTorusTailProjection
    (integralSingularHomologyMap 2 (standardThreeTorusCoordinateTwoTorus i)
      standardTwoTorusHomologyGenerator) = _
  rw [integralSingularHomologyMap_comp_wang, tailProjection_comp_coordinateTwoTorus,
    standardTwoTorusMatrixDeterminantDegree]
  fin_cases i <;> simp [projectedPairMatrix, Matrix.det_fin_two]

theorem threeTorusTailProjection_homologyTwo (x : IntegralSingularHomology 2 (StdTorus 3)) :
    integralSingularHomologyMap 2 threeTorusTailProjection x =
      standardThreeTorusDegreeTwoCoordinateHom x 2 • standardTwoTorusHomologyGenerator := by
  conv_lhs => rw [homologyTwo_eq_sum_coordinateClasses x]
  rw [map_sum]
  simp only [map_zsmul, threeTorusTailProjection_homologyTwo_coordinateClass]
  simp


/-- A coordinate circle in the phase two-torus. -/
def twoTorusCoordinateCircle (i : Fin 2) : C(StdTorus 1, StdTorus 2) where
  toFun z j := if j = i then z 0 else 0
  continuous_toFun := by
    apply continuous_pi
    intro j
    split_ifs <;> fun_prop

def twoTorusCoordinateCircleClass (i : Fin 2) : IntegralSingularHomology 1 (StdTorus 2) :=
  integralSingularHomologyMap 1 (twoTorusCoordinateCircle i) standardCircleHomologyGenerator

private def circleToPoint : C(StdTorus 1, StdTorus 0) := ContinuousMap.const _ 0
private def pointToTwoTorus : C(StdTorus 0, StdTorus 2) := ContinuousMap.const _ 0

private theorem tailProjection_comp_coordinateCircle_zero :
    threeTorusTailProjection.comp (standardThreeTorusCoordinateCircle 0) =
      pointToTwoTorus.comp circleToPoint := by
  ext z j
  fin_cases j <;> rfl

private theorem tailProjection_comp_coordinateCircle_succ (i : Fin 2) :
    threeTorusTailProjection.comp (standardThreeTorusCoordinateCircle i.succ) =
      twoTorusCoordinateCircle i := by
  ext z j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem threeTorusTailProjection_homologyOne_coordinateClass_zero :
    integralSingularHomologyMap 1 threeTorusTailProjection
      (standardThreeTorusCoordinateHomologyClass 0) = 0 := by
  change integralSingularHomologyMap 1 threeTorusTailProjection
    (integralSingularHomologyMap 1 (standardThreeTorusCoordinateCircle 0)
      standardCircleHomologyGenerator) = _
  rw [integralSingularHomologyMap_comp_wang, tailProjection_comp_coordinateCircle_zero,
    ← integralSingularHomologyMap_comp_wang]
  let _ := subsingleton_homology_stdTorusZero 1 one_ne_zero
  have h : integralSingularHomologyMap 1 circleToPoint standardCircleHomologyGenerator = 0 :=
    Subsingleton.elim _ _
  rw [h, map_zero]

@[simp] theorem threeTorusTailProjection_homologyOne_coordinateClass_succ (i : Fin 2) :
    integralSingularHomologyMap 1 threeTorusTailProjection
      (standardThreeTorusCoordinateHomologyClass i.succ) = twoTorusCoordinateCircleClass i := by
  change integralSingularHomologyMap 1 threeTorusTailProjection
    (integralSingularHomologyMap 1 (standardThreeTorusCoordinateCircle i.succ)
      standardCircleHomologyGenerator) = _
  rw [integralSingularHomologyMap_comp_wang, tailProjection_comp_coordinateCircle_succ]
  rfl


/-- Insert a zero head circle. -/
def threeTorusTailSection : C(StdTorus 2, StdTorus 3) where
  toFun z := Fin.cons 0 z
  continuous_toFun := by fun_prop

@[simp] theorem threeTorusTailProjection_comp_section :
    threeTorusTailProjection.comp threeTorusTailSection = ContinuousMap.id _ := by
  ext z i
  rfl

theorem threeTorusTailProjection_homology_surjective (n : ℕ) :
    Function.Surjective (integralSingularHomologyMap n threeTorusTailProjection) := by
  intro x
  refine ⟨integralSingularHomologyMap n threeTorusTailSection x, ?_⟩
  rw [integralSingularHomologyMap_comp_wang, threeTorusTailProjection_comp_section,
    integralSingularHomologyMap_id_wang]

private theorem tailSection_comp_coordinateCircle (i : Fin 2) :
    threeTorusTailSection.comp (twoTorusCoordinateCircle i) =
      standardThreeTorusCoordinateCircle i.succ := by
  ext z j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem threeTorusTailSection_homologyOne_coordinateClass (i : Fin 2) :
    integralSingularHomologyMap 1 threeTorusTailSection (twoTorusCoordinateCircleClass i) =
      standardThreeTorusCoordinateHomologyClass i.succ := by
  change integralSingularHomologyMap 1 threeTorusTailSection
    (integralSingularHomologyMap 1 (twoTorusCoordinateCircle i)
      standardCircleHomologyGenerator) = _
  rw [integralSingularHomologyMap_comp_wang, tailSection_comp_coordinateCircle]
  rfl

theorem homologyOne_eq_head_add_tail (x : IntegralSingularHomology 1 (StdTorus 3)) :
    x = standardThreeTorusDegreeOneCoordinateHom x 0 • standardThreeTorusCoordinateHomologyClass 0 +
      integralSingularHomologyMap 1 threeTorusTailSection
        (integralSingularHomologyMap 1 threeTorusTailProjection x) := by
  have h := homologyOne_eq_sum_coordinateClasses x
  conv_rhs =>
    arg 2
    rw [h, map_sum]
  simp only [map_zsmul, Fin.sum_univ_three, map_add,
    threeTorusTailProjection_homologyOne_coordinateClass_zero,
    show (1 : Fin 3) = (0 : Fin 2).succ from rfl,
    show (2 : Fin 3) = (1 : Fin 2).succ from rfl,
    threeTorusTailProjection_homologyOne_coordinateClass_succ,
    threeTorusTailSection_homologyOne_coordinateClass, smul_zero, zero_add]
  simpa only [Fin.sum_univ_three, add_assoc, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using h

theorem threeTorusTailProjection_homologyOne_eq_zero_iff
    (x : IntegralSingularHomology 1 (StdTorus 3)) :
    integralSingularHomologyMap 1 threeTorusTailProjection x = 0 ↔
      x = standardThreeTorusDegreeOneCoordinateHom x 0 •
        standardThreeTorusCoordinateHomologyClass 0 := by
  constructor
  · intro hx
    simpa only [hx, map_zero, add_zero] using homologyOne_eq_head_add_tail x
  · intro hx
    rw [hx, map_zsmul, threeTorusTailProjection_homologyOne_coordinateClass_zero, smul_zero]

end SphereSixComplex.StandardTorusHomology
