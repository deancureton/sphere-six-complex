module

public import SphereSixComplex.Prerequisites.Topology.CellularSquareBoundary
public import SphereSixComplex.Prerequisites.Topology.StandardTorusHomology
public import SphereSixComplex.Prerequisites.Topology.StandardSpherePositiveHomology
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

public instance (n : ℕ) : ContractibleSpace (CWCharacteristicClosedBall n) :=
  (convex_closedBall (0 : Fin n → ℝ) 1).contractibleSpace
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩

public theorem cwCharacteristicBoundary_isIso (n : ℕ) (hn : n ≠ 0) :
    IsIso (cwRelativeIntegralSingularBoundary (cwCharacteristicBoundaryInclusion (n + 1)) n) := by
  have hz (k : ℕ) (hk : k ≠ 0) :
      IsZero ((cwIntegralSingularChainComplexObj
        (TopCat.of (CWCharacteristicClosedBall (n + 1)))).homology k) := by
    let _ : Subsingleton ((cwIntegralSingularChainComplexObj
        (TopCat.of (CWCharacteristicClosedBall (n + 1)))).homology k) :=
      subsingleton_integralSingularHomology_of_contractible
        (X := CWCharacteristicClosedBall (n + 1)) k hk
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact (cwRelativeIntegralSingularShortComplex_shortExact
    (cwCharacteristicBoundaryInclusion (n + 1))).isIso_δ (n + 1) n
      (ComplexShape.down_mk (n + 1) n rfl) (hz (n + 1) (by omega)) (hz n hn)

public def cwSquareBoundaryAddCircleHomeomorph :
    CWCharacteristicBoundarySphere 2 ≃ₜ UnitAddCircle :=
  cwSquareBoundaryCircleHomeomorph.trans (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm

public def cwSquareBoundaryHomologyWinding :
    IntegralSingularHomology 1 (CWCharacteristicBoundarySphere 2) ≃+ ℤ :=
  (integralSingularHomologyEquiv 1 cwSquareBoundaryAddCircleHomeomorph).trans
    (AddEquiv.ofBijective StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      ⟨StandardTorusHomology.unitCircleHomologyWinding_injective,
        StandardCircleHomologyLiftDegree.unitCircleHomologyWinding_surjective⟩)

public def cwSquareBoundaryPositiveLoop :
    Path (cwSquareBoundaryAddCircleHomeomorph.symm 0)
      (cwSquareBoundaryAddCircleHomeomorph.symm 0) :=
  (StandardCircleHomologyLiftDegree.unitCircleIntegerLoop 1).map
    cwSquareBoundaryAddCircleHomeomorph.symm.continuous

public theorem cwSquareBoundaryHomologyWinding_positiveLoop :
    cwSquareBoundaryHomologyWinding
      (StandardCircleHomologyLiftDegree.loopHomologyClass cwSquareBoundaryPositiveLoop) = 1 := by
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1
        (cwSquareBoundaryAddCircleHomeomorph : ContinuousMap _ _)
        (StandardCircleHomologyLiftDegree.loopHomologyClass cwSquareBoundaryPositiveLoop)) = 1
  rw [StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass]
  have h : cwSquareBoundaryPositiveLoop.map cwSquareBoundaryAddCircleHomeomorph.continuous =
      (StandardCircleHomologyLiftDegree.unitCircleIntegerLoop 1).cast
        (cwSquareBoundaryAddCircleHomeomorph.apply_symm_apply 0)
        (cwSquareBoundaryAddCircleHomeomorph.apply_symm_apply 0) := by
    ext t
    exact cwSquareBoundaryAddCircleHomeomorph.apply_symm_apply _
  rw [h]
  exact StandardCircleHomologyLiftDegree.unitCircleHomologyWinding_integerLoop 1

public theorem cwSquareBoundaryHomology_eq_zsmul_positiveLoop
    (x : IntegralSingularHomology 1 (CWCharacteristicBoundarySphere 2)) :
    x = cwSquareBoundaryHomologyWinding x •
      StandardCircleHomologyLiftDegree.loopHomologyClass cwSquareBoundaryPositiveLoop := by
  apply cwSquareBoundaryHomologyWinding.injective
  rw [map_zsmul, cwSquareBoundaryHomologyWinding_positiveLoop]
  simp

public theorem cwSquareBoundaryHomologyMap_eq_zero_of_positiveLoop
    {Y : Type} [TopologicalSpace Y]
    (f : ContinuousMap (CWCharacteristicBoundarySphere 2) Y)
    (h : StandardCircleHomologyLiftDegree.loopHomologyClass
      (cwSquareBoundaryPositiveLoop.map f.continuous) = 0) :
    integralSingularHomologyMap 1 f = 0 := by
  ext x
  rw [cwSquareBoundaryHomology_eq_zsmul_positiveLoop x, map_zsmul,
    StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass, h, smul_zero]
  rfl

public def normalizedSquareDiskOrientation :
    (cwRelativeIntegralSingularChainComplex
      (cwCharacteristicBoundaryInclusion 2)).homology 2 ≃+ ℤ := by
  let _ := cwCharacteristicBoundary_isIso 1 (by omega)
  exact (asIso (cwRelativeIntegralSingularBoundary
    (cwCharacteristicBoundaryInclusion 2) 1)).addCommGroupIsoToAddEquiv.trans
      cwSquareBoundaryHomologyWinding

end SphereSixComplex
