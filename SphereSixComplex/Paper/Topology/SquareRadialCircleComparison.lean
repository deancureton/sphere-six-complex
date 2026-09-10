module

public import SphereSixComplex.Paper.Topology.ConstructedA2HexagonCircleLoop

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex
open Geometry.StandardInfiniteA2ToricModel.Established
open StandardCircleHomologyLiftDegree

public theorem squareRadialCirclePoint (r : ℝ) (hr : 0 < r) (t : ℝ) :
    cwSquareBoundaryCircleHomeomorph
      (puncturedPlaneToSquareBoundary (planeCirclePuncturedPoint r hr.ne' t)) =
      Circle.exp (2 * Real.pi * t) := by
  let e : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).trans Complex.equivRealProdCLM.symm
  have he : e (planeCirclePoint r t) = r • (Circle.exp (2 * Real.pi * t) : ℂ) := by
    change Complex.mk (r * Real.cos (2 * Real.pi * t))
      (r * Real.sin (2 * Real.pi * t)) = r • (Circle.exp (2 * Real.pi * t) : ℂ)
    apply Complex.ext <;>
      simp [Circle.coe_exp, Complex.exp_re, Complex.exp_im]
  have hn : 0 < ‖planeCirclePoint r t‖ :=
    norm_pos_iff.mpr (planeCirclePoint_ne_zero r hr.ne' t)
  have ha : 0 < ‖planeCirclePoint r t‖⁻¹ * r := mul_pos (inv_pos.mpr hn) hr
  apply Subtype.ext
  change ‖e (‖planeCirclePoint r t‖⁻¹ • planeCirclePoint r t)‖⁻¹ •
    e (‖planeCirclePoint r t‖⁻¹ • planeCirclePoint r t) = _
  have hh : e (‖planeCirclePoint r t‖⁻¹ • planeCirclePoint r t) =
      (‖planeCirclePoint r t‖⁻¹ * r) • (Circle.exp (2 * Real.pi * t) : ℂ) := by
    rw [e.map_smul, he]
    exact smul_smul _ _ _
  calc
    _ = ‖(‖planeCirclePoint r t‖⁻¹ * r) • (Circle.exp (2 * Real.pi * t) : ℂ)‖⁻¹ •
        ((‖planeCirclePoint r t‖⁻¹ * r) • (Circle.exp (2 * Real.pi * t) : ℂ)) :=
      congrArg (fun z : ℂ ↦ ‖z‖⁻¹ • z) hh
    _ = _ := by
      have hnorm : ‖(Circle.exp (2 * Real.pi * t) : ℂ)‖ = 1 := Circle.norm_coe _
      rw [norm_smul, hnorm, mul_one, Real.norm_eq_abs, abs_of_pos ha,
        smul_smul, inv_mul_cancel₀ ha.ne', one_smul]

public theorem squareRadialAddCirclePoint (r : ℝ) (hr : 0 < r) (t : ℝ) :
    cwSquareBoundaryAddCircleHomeomorph
      (puncturedPlaneToSquareBoundary (planeCirclePuncturedPoint r hr.ne' t)) =
      (t : UnitAddCircle) := by
  apply (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).injective
  change (AddCircle.homeomorphCircle _)
    ((AddCircle.homeomorphCircle _).symm
      (cwSquareBoundaryCircleHomeomorph
        (puncturedPlaneToSquareBoundary (planeCirclePuncturedPoint r hr.ne' t)))) = _
  rw [Homeomorph.apply_symm_apply, squareRadialCirclePoint r hr]
  simp [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]

public theorem squareRadialCircleLoop_eq_positive (r : ℝ) (hr : 0 < r) :
    loopHomologyClass ((planeCirclePuncturedLoop r hr.ne').map
      puncturedPlaneToSquareBoundary.continuous) =
      loopHomologyClass cwSquareBoundaryPositiveLoop := by
  have hb : puncturedPlaneToSquareBoundary (planeCirclePuncturedPoint r hr.ne' 0) =
      cwSquareBoundaryAddCircleHomeomorph.symm 0 :=
    cwSquareBoundaryAddCircleHomeomorph.injective (by
      rw [Homeomorph.apply_symm_apply, squareRadialAddCirclePoint r hr]
      simp)
  have hp : (planeCirclePuncturedLoop r hr.ne').map puncturedPlaneToSquareBoundary.continuous =
      cwSquareBoundaryPositiveLoop.cast hb hb := by
    apply Path.ext
    funext t
    apply cwSquareBoundaryAddCircleHomeomorph.injective
    change cwSquareBoundaryAddCircleHomeomorph
      (puncturedPlaneToSquareBoundary (planeCirclePuncturedPoint r hr.ne'
        ((Path.segment (0 : ℝ) 1) t))) =
      cwSquareBoundaryAddCircleHomeomorph
        (cwSquareBoundaryAddCircleHomeomorph.symm (unitCircleIntegerLoop 1 t))
    rw [Homeomorph.apply_symm_apply, squareRadialAddCirclePoint r hr]
    simp [Path.segment_apply, AffineMap.lineMap_apply, unitCircleIntegerLoop,
      vsub_eq_sub, vadd_eq_add]
  rw [hp, loopHomologyClass_cast]

public theorem hexagonBoundaryLoop_square_homology_eq_positive :
    loopHomologyClass (constructedA2HexagonBoundaryLoop.map
      constructedA2SquareBoundaryHexagonHomeomorph.symm.continuous) =
      loopHomologyClass cwSquareBoundaryPositiveLoop := by
  have h := congrArg (integralSingularHomologyMap 1 puncturedPlaneToSquareBoundary)
    constructedA2HexagonBoundaryLoop_homology_eq_circle
  rw [integralSingularHomologyMap_loopHomologyClass,
    integralSingularHomologyMap_loopHomologyClass, squareRadialCircleLoop_eq_positive _ (by norm_num)] at h
  have hp : (constructedA2HexagonBoundaryLoop.map
      constructedA2HexagonBoundaryToPunctured.continuous).map
        puncturedPlaneToSquareBoundary.continuous =
      (constructedA2HexagonBoundaryLoop.map
        constructedA2SquareBoundaryHexagonHomeomorph.symm.continuous).cast
          (constructedA2Hexagon_radial_to_square _)
          (constructedA2Hexagon_radial_to_square _) := by
    apply Path.ext
    funext t
    exact constructedA2Hexagon_radial_to_square _
  rw [hp, loopHomologyClass_cast] at h
  exact h

end SphereSixComplex
