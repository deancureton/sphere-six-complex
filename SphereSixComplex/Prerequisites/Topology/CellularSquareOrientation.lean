module

public import SphereSixComplex.Prerequisites.Topology.CellularSquareBoundary
public import SphereSixComplex.Prerequisites.Topology.StandardTorusHomology
public import SphereSixComplex.Prerequisites.Topology.StandardSpherePositiveHomology
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex



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


end SphereSixComplex
