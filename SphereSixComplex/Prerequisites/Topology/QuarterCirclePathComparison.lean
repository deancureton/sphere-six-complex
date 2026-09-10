module

public import SphereSixComplex.Prerequisites.Topology.ConvexRadialPathHomotopy
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex

public def planeCirclePoint (r t : ℝ) : Fin 2 → ℝ :=
  ![r * Real.cos (2 * Real.pi * t), r * Real.sin (2 * Real.pi * t)]

public theorem planeCirclePoint_continuous (r : ℝ) : Continuous (planeCirclePoint r) := by
  unfold planeCirclePoint
  fun_prop

public def quadrantFunctional (i : Fin 4) (x : Fin 2 → ℝ) : ℝ :=
  ![x 0 + x 1, -x 0 + x 1, -x 0 - x 1, x 0 - x 1] i

public theorem quadrantFunctional_linear (i : Fin 4) : IsLinearMap ℝ (quadrantFunctional i) where
  map_add x y := by fin_cases i <;> simp [quadrantFunctional] <;> ring
  map_smul a x := by fin_cases i <;> simp [quadrantFunctional] <;> ring

public theorem quadrantHalfSpace_convex (i : Fin 4) :
    Convex ℝ {x : Fin 2 → ℝ | 0 < quadrantFunctional i x} :=
  convex_halfSpace_gt (quadrantFunctional_linear i) 0

public theorem quadrantHalfSpace_ne_zero (i : Fin 4) {x : Fin 2 → ℝ}
    (hx : 0 < quadrantFunctional i x) : x ≠ 0 := by
  intro h
  rw [h] at hx
  fin_cases i <;> simp [quadrantFunctional] at hx

public theorem sin_add_cos_pos_first_quadrant (a : ℝ) (ha : a ∈ Icc 0 (Real.pi / 2)) :
    0 < Real.cos a + Real.sin a := by
  have hs : 0 ≤ Real.sin a := Real.sin_nonneg_of_mem_Icc ⟨ha.1, by linarith [Real.pi_pos, ha.2]⟩
  have hc : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ha.1], ha.2⟩
  have h := Real.sin_sq_add_cos_sq a
  nlinarith

public theorem planeCirclePoint_quadrant (r : ℝ) (hr : 0 < r) (i : Fin 4) (t : unitInterval) :
    0 < quadrantFunctional i (planeCirclePoint r ((i : ℝ) / 4 + (t : ℝ) / 4)) := by
  have hθ : Real.pi * (t : ℝ) / 2 ∈ Icc 0 (Real.pi / 2) := by
    constructor
    · exact div_nonneg (mul_nonneg Real.pi_pos.le t.property.1) (by norm_num)
    · nlinarith [t.property.2, Real.pi_pos]
  have hpos := mul_pos hr (sin_add_cos_pos_first_quadrant _ hθ)
  have hc : Real.cos (Real.pi * (1 / 2 : ℝ)) = 0 := by
    rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring]
    exact Real.cos_pi_div_two
  have hs : Real.sin (Real.pi * (1 / 2 : ℝ)) = 1 := by
    rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring]
    exact Real.sin_pi_div_two
  simp only [one_div] at hc hs
  have he : quadrantFunctional i (planeCirclePoint r ((i : ℝ) / 4 + (t : ℝ) / 4)) =
      r * (Real.cos (Real.pi * (t : ℝ) / 2) + Real.sin (Real.pi * (t : ℝ) / 2)) := by
    fin_cases i <;> simp [quadrantFunctional, planeCirclePoint]
    all_goals
      ring_nf <;> norm_num <;>
      simp [Real.cos_add, Real.sin_add, hc, hs,
        show Real.pi * (3 / 2 : ℝ) = Real.pi + Real.pi / 2 by ring] <;> ring
  rw [he]
  exact hpos

public theorem planeCirclePoint_quarter (r : ℝ) (i : Fin 5) :
    planeCirclePoint r ((i : ℝ) / 4) =
      ![![r, 0], ![0, r], ![-r, 0], ![0, -r], ![r, 0]] i := by
  have hc : Real.cos (Real.pi * (2 : ℝ)⁻¹) = 0 := by
    rw [← div_eq_mul_inv]
    exact Real.cos_pi_div_two
  have hs : Real.sin (Real.pi * (2 : ℝ)⁻¹) = 1 := by
    rw [← div_eq_mul_inv]
    exact Real.sin_pi_div_two
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [planeCirclePoint] <;> ring_nf <;>
    simp [hc, hs, show Real.pi * (3 / 2 : ℝ) = Real.pi + Real.pi / 2 by ring,
      Real.cos_add, Real.sin_add]

public def planeCircleQuarterPath (r : ℝ) (i : Fin 4) :
    Path (planeCirclePoint r ((i : ℝ) / 4))
      (planeCirclePoint r (((i : ℝ) + 1) / 4)) :=
  (Path.segment ((i : ℝ) / 4) (((i : ℝ) + 1) / 4)).map
    (planeCirclePoint_continuous r)

public theorem planeCircleQuarterPath_apply (r : ℝ) (i : Fin 4) (t : unitInterval) :
    planeCircleQuarterPath r i t = planeCirclePoint r ((i : ℝ) / 4 + (t : ℝ) / 4) := by
  change planeCirclePoint r ((Path.segment ((i : ℝ) / 4) (((i : ℝ) + 1) / 4)) t) = _
  rw [Path.segment_apply, AffineMap.lineMap_apply]
  congr 1
  simp only [vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  ring

public theorem planeCircleQuarterPath_mem_halfspace (r : ℝ) (hr : 0 < r)
    (i : Fin 4) (t : unitInterval) :
    0 < quadrantFunctional i (planeCircleQuarterPath r i t) := by
  rw [planeCircleQuarterPath_apply]
  exact planeCirclePoint_quadrant r hr i t

end SphereSixComplex
