module

public import SphereSixComplex.Topology.CellularHomologyClassicalBoundary
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Basic

@[expose] public section
noncomputable section

namespace SphereSixComplex

public def linearEquivUnitSphereHomeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) :
    ↥(Metric.sphere (0 : E) 1) ≃ₜ ↥(Metric.sphere (0 : F) 1) where
  toFun x := ⟨‖e x‖⁻¹ • e x, by
    have hx : e x ≠ 0 := (e.map_eq_zero_iff).not.mpr (ne_zero_of_mem_unit_sphere x)
    simp [norm_smul, hx]⟩
  invFun y := ⟨‖e.symm y‖⁻¹ • e.symm y, by
    have hy : e.symm y ≠ 0 := (e.symm.map_eq_zero_iff).not.mpr (ne_zero_of_mem_unit_sphere y)
    simp [norm_smul, hy]⟩
  left_inv x := by
    apply Subtype.ext
    have hx : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    have he : ‖e x‖ ≠ 0 := norm_ne_zero_iff.mpr ((e.map_eq_zero_iff).not.mpr (ne_zero_of_mem_unit_sphere x))
    simp [map_smul, norm_smul,
      hx, smul_smul, he]
  right_inv y := by
    apply Subtype.ext
    have hy : ‖(y : F)‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
    have he : ‖e.symm y‖ ≠ 0 := norm_ne_zero_iff.mpr
      ((e.symm.map_eq_zero_iff).not.mpr (ne_zero_of_mem_unit_sphere y))
    simp [map_smul, norm_smul,
      hy, smul_smul, he]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_norm.comp (e.continuous.comp continuous_subtype_val)).inv₀
      (fun x ↦ norm_ne_zero_iff.mpr ((e.map_eq_zero_iff).not.mpr (ne_zero_of_mem_unit_sphere x)))).smul
        (e.continuous.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((continuous_norm.comp (e.symm.continuous.comp continuous_subtype_val)).inv₀
      (fun y ↦ norm_ne_zero_iff.mpr ((e.symm.map_eq_zero_iff).not.mpr (ne_zero_of_mem_unit_sphere y)))).smul
        (e.symm.continuous.comp continuous_subtype_val)

public def cwSquareBoundaryCircleHomeomorph : CWCharacteristicBoundarySphere 2 ≃ₜ Circle :=
  linearEquivUnitSphereHomeomorph
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).trans Complex.equivRealProdCLM.symm)

end SphereSixComplex
