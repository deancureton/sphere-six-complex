module

public import SphereSixComplex.Prerequisites.Topology.PositiveCircleCross

@[expose] public section
noncomputable section
open AlgebraicTopology Matrix
open scoped ContinuousMap
namespace SphereSixComplex.Topology.PositiveCircleCross
open StandardTorusHomology

public def positiveCircleProductSwap :
    C(UnitAddCircle × StdTorus 1, UnitAddCircle × StdTorus 1) where
  toFun p := (p.2 0, fun _ ↦ p.1)
  continuous_toFun := (continuous_apply 0 |>.comp continuous_snd).prodMk
    (continuous_pi (fun _ ↦ continuous_fst))

public def positiveCircleSwapMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

public theorem positiveCircleProductSwap_conjugate :
    (circleProdStandardCircleHomeomorph : C(_, _)).comp positiveCircleProductSwap =
      (standardTwoTorusMatrixMap positiveCircleSwapMatrix).comp
        (circleProdStandardCircleHomeomorph : C(_, _)) := by
  ext p i
  change (@Fin.cons 1 (fun _ : Fin 2 ↦ UnitAddCircle) (p.2 0) (fun _ ↦ p.1)) i =
    ∑ j, positiveCircleSwapMatrix i j • (@Fin.cons 1 (fun _ : Fin 2 ↦ UnitAddCircle) p.1 p.2) j
  fin_cases i <;> simp [positiveCircleSwapMatrix, Fin.sum_univ_two]

public theorem positiveCircleProductSwap_generator_mapped :
    integralSingularHomologyMap 2 circleProdStandardCircleHomeomorph
      (integralSingularHomologyMap 2 positiveCircleProductSwap positiveCircleProductGenerator) =
      -standardTwoTorusHomologyGenerator := by
  rw [integralSingularHomologyMap_comp_wang, positiveCircleProductSwap_conjugate,
    ← integralSingularHomologyMap_comp_wang]
  rw [show integralSingularHomologyMap 2 circleProdStandardCircleHomeomorph
      positiveCircleProductGenerator = standardTwoTorusHomologyGenerator from
    (integralSingularHomologyEquiv 2 circleProdStandardCircleHomeomorph).apply_symm_apply _]
  rw [standardTwoTorusMatrixDeterminantDegree]
  simp [positiveCircleSwapMatrix, Matrix.det_fin_two]

public theorem positiveCircleProductSwap_generator :
    integralSingularHomologyMap 2 positiveCircleProductSwap positiveCircleProductGenerator =
      -positiveCircleProductGenerator := by
  apply (integralSingularHomologyEquiv 2 circleProdStandardCircleHomeomorph).injective
  rw [map_neg]
  rw [show (integralSingularHomologyEquiv 2 circleProdStandardCircleHomeomorph)
      positiveCircleProductGenerator = standardTwoTorusHomologyGenerator from
    (integralSingularHomologyEquiv 2 circleProdStandardCircleHomeomorph).apply_symm_apply _]
  exact positiveCircleProductSwap_generator_mapped

end SphereSixComplex.Topology.PositiveCircleCross
