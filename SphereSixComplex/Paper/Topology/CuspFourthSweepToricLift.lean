module
public import SphereSixComplex.Paper.Topology.LocalToricCircleSweep
public import SphereSixComplex.Paper.Topology.CuspFourthSweepCentralImage
public import SphereSixComplex.Prerequisites.Topology.UnitCircleExponential

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open CuspPuncturedCollarBridge CuspRadialClutchingConstruction
open CuspLocalPhaseAction InfiniteA2Toric

public def fourthToricCircle : C(UnitAddCircle, DenseTorus) where
  toFun z := ![1, CircleExponential.toUnits z, 1]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

public theorem fourthToricCircle_last (z : UnitAddCircle) : fourthToricCircle z 2 = 1 := rfl

open CuspPeriodExpansion

public def cuspAngularDenseLoop (A : PaperAnalyticData) : C(UnitAddCircle, DenseTorus) where
  toFun z := ![1, 1, (denseCuspExponential 0
    (cuspParameterOfPolar (A.starCuspWitness.localWitness.radius / 2) 0) 2) *
      CircleExponential.toUnits z]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

public theorem cuspAngularDenseLoop_real (A : PaperAnalyticData) (t : ℝ) :
    cuspAngularDenseLoop A (t : UnitAddCircle) =
      denseCuspExponential 0
        (cuspParameterOfPolar (A.starCuspWitness.localWitness.radius / 2) t) := by
  ext i
  fin_cases i
  · simp [cuspAngularDenseLoop, denseCuspExponential,
      NormalizedFuchsianCuspCoordinate.exponentialUnit]
  · simp [cuspAngularDenseLoop, denseCuspExponential,
      NormalizedFuchsianCuspCoordinate.exponentialUnit]
  · change _ * (CircleExponential.toUnits (t : UnitAddCircle) : ℂ) = _
    rw [CircleExponential.toUnits_real]
    change Complex.exp _ * Complex.exp _ = Complex.exp _
    rw [← Complex.exp_add]
    congr 1
    rw [cuspParameterOfPolar_eq, cuspParameterOfPolar_eq]
    push_cast
    ring

public def cuspAngularLocalLoop (A : PaperAnalyticData) :
    C(UnitAddCircle, LocalCarrier A.toricModel A.starCuspWitness.localWitness.radius) where
  toFun z := ⟨A.toricModel.torusEmbedding (cuspAngularDenseLoop A z), by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
    change A.toricModel.t (A.toricModel.torusEmbedding _) ∈ Metric.ball 0 _
    rw [mem_ball_zero_iff]
    rw [cuspAngularDenseLoop_real, A.toricModel.t_torus,
      denseCuspExponential_last,
      norm_cuspQ_cuspParameterOfPolar _ _ (by
        have := A.starCuspWitness.localWitness.radius_pos; linarith)]
    have := A.starCuspWitness.localWitness.radius_pos
    linarith⟩
  continuous_toFun := (A.toricModel.torus_openEmbedding.continuous.comp
    (cuspAngularDenseLoop A).continuous).subtype_mk _

public def fourthSweepToricFactor (A : PaperAnalyticData) :
    C(UnitAddCircle × StdTorus 1,
      UnitAddCircle × LocalCarrier A.toricModel A.starCuspWitness.localWitness.radius) where
  toFun z := (z.2 0, cuspAngularLocalLoop A z.1)
  continuous_toFun := ((continuous_apply 0).comp continuous_snd).prodMk
    ((cuspAngularLocalLoop A).continuous.comp continuous_fst)

public def fourthSweepToricLift (A : PaperAnalyticData) :
    C(UnitAddCircle × StdTorus 1,
      LocalCarrier A.toricModel A.starCuspWitness.localWitness.radius) :=
  (localHeightPreservingCircleAction A.toricModel A.starCuspWitness.localWitness.radius
    fourthToricCircle fourthToricCircle_last).comp (fourthSweepToricFactor A)

public theorem fourthSweepToricLift_homology_zero (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 1)) :
    integralSingularHomologyMap 2 (fourthSweepToricLift A) x = 0 := by
  exact localHeightPreservingCircleSweep_zero _ _ A.starCuspWitness.localWitness.radius_pos
    _ _ _ ⟨fun z ↦ cuspAngularLocalLoop A (z 0),
      (cuspAngularLocalLoop A).continuous.comp (continuous_apply 0)⟩
    ⟨fun z _ ↦ z.1, continuous_pi fun _ ↦ continuous_fst⟩ rfl x

open ComplexTorus SphereSixComplex.Periods
public theorem fourthSweepToricLift_real (A : PaperAnalyticData) (r t : ℝ) :
    fourthSweepToricLift A ((r : UnitAddCircle), fun _ ↦ (t : UnitAddCircle)) =
      additiveCuspFillingLift A.starCuspWitness
        ⟨(t • periodVector (cuspBasePoint A.cuspCoordinate
          (cuspParameterOfPolar (A.starCuspWitness.localWitness.radius / 2) r)).1
          ![0,0,0,1],
          cuspParameterOfPolar (A.starCuspWitness.localWitness.radius / 2) r), by
          change ‖cuspQ (cuspParameterOfPolar (A.starCuspWitness.localWitness.radius / 2) r)‖ < _
          rw [norm_cuspQ_cuspParameterOfPolar _ _ (by
            have := A.starCuspWitness.localWitness.radius_pos; linarith)]
          have := A.starCuspWitness.localWitness.radius_pos; linarith⟩ := by
  change _ = (additiveToPuncturedLocalHomeomorph _ _ (Quotient.mk _ _)).1
  rw [additiveToPuncturedLocalHomeomorph_mk]
  apply Subtype.ext
  change A.toricModel.torusAction (fourthToricCircle (t : UnitAddCircle))
    (A.toricModel.torusEmbedding (cuspAngularDenseLoop A (r : UnitAddCircle))) = _
  rw [A.toricModel.torusAction_torus]
  apply congrArg A.toricModel.torusEmbedding
  rw [cuspAngularDenseLoop_real]
  ext i
  fin_cases i <;>
    simp [fourthToricCircle, denseCuspExponential,
      NormalizedFuchsianCuspCoordinate.exponentialUnit, CircleExponential.toUnits_real,
      periodVector, periodMatrix, Matrix.vecHead, Matrix.vecTail]

public theorem cuspFourthSweep_filling_factor (A : PaperAnalyticData) :
    (⟨puncturedLocalCuspToFilling A.starCuspWitness,
      puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ :
      C(A.openEmbeddingStarData.collarSource 0, actualLocalCuspFilling A.starCuspWitness)).comp
        (cuspFourthSweep A) =
      (actualCuspFillingProjection A.starCuspWitness).comp (fourthSweepToricLift A) := by
  ext1 z
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective z.1
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (z.2 0)
  have hz : z = ((r : UnitAddCircle), fun _ ↦ (t : UnitAddCircle)) := by
    apply Prod.ext hr.symm
    funext i
    fin_cases i
    exact ht.symm
  rw [hz]
  change puncturedLocalCuspToFilling A.starCuspWitness (cuspFourthSweep A _) = _
  rw [cuspFourthSweep_real, cuspFullFibreSlice_fourthCircle_real,
    additiveCuspCoverSquare_commutes]
  change _ = actualCuspFillingProjection A.starCuspWitness (fourthSweepToricLift A _)
  rw [fourthSweepToricLift_real]

public theorem cuspFourthSweep_filling_homology_zero (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 1)) :
    integralSingularHomologyMap 2
      (⟨puncturedLocalCuspToFilling A.starCuspWitness,
        puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩ :
        C(A.openEmbeddingStarData.collarSource 0, actualLocalCuspFilling A.starCuspWitness))
      (integralSingularHomologyMap 2 (cuspFourthSweep A) x) = 0 := by
  rw [integralSingularHomologyMap_comp_wang, cuspFourthSweep_filling_factor,
    ← integralSingularHomologyMap_comp_wang, fourthSweepToricLift_homology_zero, map_zero]

end SphereSixComplex.Geometry.PaperAnalyticData
