module

public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasisProof

/-!
# Canonical degree-two coordinates on the standard three-torus

The last three coordinate two-tori in the standard four-torus identify the second homology of
the coordinate subtorus with `ℤ³`.  This formulation lets the established natural four-torus
calculation control the explicit elliptic three-torus clutching maps.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.StandardTorusHomology

/-- Include the last three coordinates as the head-zero subtorus of the standard four-torus. -/
public def standardThreeTorusTailInclusion : C(StdTorus 3, StdTorus 4) where
  toFun z := Fin.cons 0 z
  continuous_toFun := by fun_prop

/-- Retract the standard four-torus onto its last three coordinates. -/
public def standardThreeTorusTailRetraction : C(StdTorus 4, StdTorus 3) where
  toFun := Fin.tail
  continuous_toFun := by fun_prop

@[simp]
public theorem standardThreeTorusTailRetraction_comp_inclusion :
    standardThreeTorusTailRetraction.comp standardThreeTorusTailInclusion =
      ContinuousMap.id _ := by
  ext z i
  rfl

public theorem standardThreeTorusTailInclusion_homology_injective (k : ℕ) :
    Function.Injective
      (integralSingularHomologyMap k standardThreeTorusTailInclusion) := by
  intro x y hxy
  have h := congrArg
    (integralSingularHomologyMap k standardThreeTorusTailRetraction) hxy
  rw [integralSingularHomologyMap_comp_wang,
    standardThreeTorusTailRetraction_comp_inclusion,
    integralSingularHomologyMap_id_wang] at h
  rw [integralSingularHomologyMap_comp_wang,
    standardThreeTorusTailRetraction_comp_inclusion,
    integralSingularHomologyMap_id_wang] at h
  exact h

/-- The three pair indices `(12,13,23)` inside the four-torus pair ordering. -/
public def tailDegreeTwoIndex : Fin 3 → Fin 6 := ![3, 4, 5]

/-- Restrict the canonical four-torus degree-two coordinates to `(12,13,23)`. -/
public def standardThreeTorusDegreeTwoCoordinateHom :
    IntegralSingularHomology 2 (StdTorus 3) →+ (Fin 3 → ℤ) where
  toFun x i := naturalStdTorusFourHomologyTwo
    (integralSingularHomologyMap 2 standardThreeTorusTailInclusion x)
    (tailDegreeTwoIndex i)
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp

private theorem subsingleton_homologyTwo_standardCircle :
    Subsingleton (IntegralSingularHomology 2 (StdTorus 1)) := by
  constructor
  intro x y
  apply (stdTorusHomologyTwo 1).injective
  funext i
  exact Fin.elim0 i

private theorem homologyMap_standardCircleFactor_degreeTwo_zero
    {X : Type} [TopologicalSpace X]
    (f : C(X, StdTorus 1)) (g : C(StdTorus 1, StdTorus 2))
    (x : IntegralSingularHomology 2 X) :
    integralSingularHomologyMap 2 (g.comp f) x = 0 := by
  rw [← integralSingularHomologyMap_comp_wang]
  let _ := subsingleton_homologyTwo_standardCircle
  have hzero : integralSingularHomologyMap 2 f x = 0 := Subsingleton.elim _ _
  rw [hzero, map_zero]

private def headPairCircleSource (i : Fin 3) : C(StdTorus 3, StdTorus 1) where
  toFun z _ := z i
  continuous_toFun := by fun_prop

private def headPairCircleTarget : C(StdTorus 1, StdTorus 2) where
  toFun z := ![0, z 0]
  continuous_toFun := by fun_prop

private def headDegreeTwoIndex (i : Fin 3) : Fin 6 := ⟨i, by omega⟩

private theorem headPairProjection_comp_tailInclusion (i : Fin 3) :
    (standardFourTorusCoordinateTwoTorusProjection (headDegreeTwoIndex i)).comp
        standardThreeTorusTailInclusion =
      headPairCircleTarget.comp (headPairCircleSource i) := by
  ext z j
  fin_cases i <;> fin_cases j <;>
    rfl

private theorem standardThreeTorusTailInclusion_headCoordinate_zero
    (x : IntegralSingularHomology 2 (StdTorus 3)) (i : Fin 3) :
    naturalStdTorusFourHomologyTwo
        (integralSingularHomologyMap 2 standardThreeTorusTailInclusion x)
        (headDegreeTwoIndex i) = 0 := by
  change standardFourTorusCoordinateTwoTorusHom
      (integralSingularHomologyMap 2 standardThreeTorusTailInclusion x)
        (headDegreeTwoIndex i) = 0
  change stdTorusHomologyTwo 2
      (integralSingularHomologyMap 2
        (standardFourTorusCoordinateTwoTorusProjection (headDegreeTwoIndex i))
        (integralSingularHomologyMap 2 standardThreeTorusTailInclusion x))
        standardTwoTorusDegreeTwoIndex = 0
  rw [integralSingularHomologyMap_comp_wang,
    headPairProjection_comp_tailInclusion]
  rw [homologyMap_standardCircleFactor_degreeTwo_zero]
  simp

public theorem standardThreeTorusDegreeTwoCoordinateHom_injective :
    Function.Injective standardThreeTorusDegreeTwoCoordinateHom := by
  intro x y hxy
  apply standardThreeTorusTailInclusion_homology_injective 2
  apply naturalStdTorusFourHomologyTwo.injective
  funext i
  fin_cases i
  · exact (standardThreeTorusTailInclusion_headCoordinate_zero x 0).trans
      (standardThreeTorusTailInclusion_headCoordinate_zero y 0).symm
  · exact (standardThreeTorusTailInclusion_headCoordinate_zero x 1).trans
      (standardThreeTorusTailInclusion_headCoordinate_zero y 1).symm
  · exact (standardThreeTorusTailInclusion_headCoordinate_zero x 2).trans
      (standardThreeTorusTailInclusion_headCoordinate_zero y 2).symm
  · exact congrFun hxy 0
  · exact congrFun hxy 1
  · exact congrFun hxy 2

/-- Include a coordinate two-torus in the standard three-torus. -/
public def standardThreeTorusCoordinateTwoTorus (i : Fin 3) : C(StdTorus 2, StdTorus 3) :=
  (standardThreeTorusTailRetraction.comp
    (standardFourTorusCoordinateTwoTorus (tailDegreeTwoIndex i)))

/-- The homology class of a coordinate two-torus in the standard three-torus. -/
public def standardThreeTorusCoordinateTwoTorusHomologyClass (i : Fin 3) :
    IntegralSingularHomology 2 (StdTorus 3) :=
  integralSingularHomologyMap 2 (standardThreeTorusCoordinateTwoTorus i)
    standardTwoTorusHomologyGenerator

private theorem tailInclusion_comp_coordinateTwoTorus (i : Fin 3) :
    standardThreeTorusTailInclusion.comp (standardThreeTorusCoordinateTwoTorus i) =
      standardFourTorusCoordinateTwoTorus (tailDegreeTwoIndex i) := by
  ext z j
  fin_cases i <;> fin_cases j <;>
    rfl

@[simp]
public theorem standardThreeTorusDegreeTwoCoordinateHom_coordinateClass (j : Fin 3) :
    standardThreeTorusDegreeTwoCoordinateHom
        (standardThreeTorusCoordinateTwoTorusHomologyClass j) = Pi.single j 1 := by
  funext i
  change naturalStdTorusFourHomologyTwo
      (integralSingularHomologyMap 2 standardThreeTorusTailInclusion
        (integralSingularHomologyMap 2 (standardThreeTorusCoordinateTwoTorus j)
          standardTwoTorusHomologyGenerator)) (tailDegreeTwoIndex i) = _
  rw [integralSingularHomologyMap_comp_wang, tailInclusion_comp_coordinateTwoTorus]
  change standardFourTorusCoordinateTwoTorusHom
      (standardFourTorusCoordinateTwoTorusHomologyClass (tailDegreeTwoIndex j))
      (tailDegreeTwoIndex i) = _
  rw [standardFourTorusCoordinateTwoTorusHom_coordinateHomologyClass]
  fin_cases i <;> fin_cases j <;> simp [tailDegreeTwoIndex]

public theorem standardThreeTorusDegreeTwoCoordinateHom_surjective :
    Function.Surjective standardThreeTorusDegreeTwoCoordinateHom := by
  intro v
  refine ⟨∑ i, v i • standardThreeTorusCoordinateTwoTorusHomologyClass i, ?_⟩
  rw [map_sum]
  simp only [map_zsmul, standardThreeTorusDegreeTwoCoordinateHom_coordinateClass]
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

/-- Canonical integral coordinates `(12,13,23)` on `H₂(T³;ℤ)`. -/
public noncomputable def standardThreeTorusHomologyTwo :
    IntegralSingularHomology 2 (StdTorus 3) ≃+ (Fin 3 → ℤ) :=
  AddEquiv.ofBijective standardThreeTorusDegreeTwoCoordinateHom
    ⟨standardThreeTorusDegreeTwoCoordinateHom_injective,
      standardThreeTorusDegreeTwoCoordinateHom_surjective⟩

public theorem standardThreeTorusTailInclusion_homologyTwo_coordinates
    (x : IntegralSingularHomology 2 (StdTorus 3)) :
    naturalStdTorusFourHomologyTwo
        (integralSingularHomologyMap 2 standardThreeTorusTailInclusion x) =
      ![0, 0, 0, standardThreeTorusHomologyTwo x 0,
        standardThreeTorusHomologyTwo x 1, standardThreeTorusHomologyTwo x 2] := by
  funext i
  fin_cases i
  · exact standardThreeTorusTailInclusion_headCoordinate_zero x 0
  · exact standardThreeTorusTailInclusion_headCoordinate_zero x 1
  · exact standardThreeTorusTailInclusion_headCoordinate_zero x 2
  · rfl
  · rfl
  · rfl

end SphereSixComplex.StandardTorusHomology

end

end
