module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.GroupWithZero

@[expose] public section

noncomputable section
open Set Topology Real

namespace SphereSixComplex.CircleCell

public def param (t : ℝ) : Circle := Circle.exp (Real.pi * (t + 1))

public theorem continuous_param : Continuous param := by
  unfold param
  fun_prop

@[simp] public theorem param_neg_one : param (-1) = 1 := by
  simp [param]

@[simp] public theorem param_one : param 1 = 1 := by
  norm_num [param, show Real.pi * 2 = 2 * Real.pi by ring]

public theorem injOn_param : Set.InjOn param (Ioo (-1 : ℝ) 1) := by
  intro x hx y hy h
  have hx' : Real.pi * (x + 1) ∈ Ioc (0 : ℝ) (2 * Real.pi) := by
    constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]
  have hy' : Real.pi * (y + 1) ∈ Ioc (0 : ℝ) (2 * Real.pi) := by
    constructor <;> nlinarith [Real.pi_pos, hy.1, hy.2]
  have heq := Circle.exp_injOn_Ioc (a := 0) (b := 2 * Real.pi) (by simp) hx' hy' h
  nlinarith [Real.pi_pos]

public theorem param_ne_one {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    param t ≠ 1 := by
  intro h
  have hx : Real.pi * (t + 1) ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    constructor <;> nlinarith [Real.pi_pos, ht.1, ht.2]
  have hz : (0 : ℝ) ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    constructor <;> nlinarith [Real.pi_pos]
  have heq := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp) hx hz
    (show Circle.exp (Real.pi * (t + 1)) = Circle.exp 0 by simpa [param] using h)
  nlinarith [Real.pi_pos, ht.1]

public theorem surjOn_param :
    Set.SurjOn param (Ioo (-1 : ℝ) 1) {z : Circle | z ≠ 1} := by
  intro z hz
  have harg : Complex.arg z ≠ 0 := by simpa using hz
  have hlo := Complex.neg_pi_lt_arg (z : ℂ)
  have hhi := Complex.arg_le_pi (z : ℂ)
  by_cases hpos : 0 < Complex.arg z
  · refine ⟨Complex.arg z / Real.pi - 1, ?_, ?_⟩
    · constructor
      · have := div_pos hpos Real.pi_pos
        linarith
      · have : Complex.arg z / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr hhi
        linarith
    · unfold param
      rw [show Real.pi * (Complex.arg z / Real.pi - 1 + 1) = Complex.arg z by
        field_simp; ring]
      exact Circle.exp_arg z
  · have hneg : Complex.arg z < 0 := lt_of_le_of_ne (le_of_not_gt hpos) harg
    refine ⟨(Complex.arg z + 2 * Real.pi) / Real.pi - 1, ?_, ?_⟩
    · constructor
      · have : 0 < (Complex.arg z + 2 * Real.pi) / Real.pi :=
          div_pos (by linarith [Real.pi_pos]) Real.pi_pos
        linarith
      · have : (Complex.arg z + 2 * Real.pi) / Real.pi < 2 :=
          (div_lt_iff₀ Real.pi_pos).mpr (by linarith)
        linarith
    · unfold param
      rw [show Real.pi * ((Complex.arg z + 2 * Real.pi) / Real.pi - 1 + 1) =
        Complex.arg z + 2 * Real.pi by field_simp; ring]
      rw [Circle.exp_add_two_pi, Circle.exp_arg]

public theorem isOpenMap_param : IsOpenMap param := by
  let e : ℝ ≃ₜ ℝ := (Homeomorph.addRight (1 : ℝ)).trans
    (Homeomorph.mulLeft₀ Real.pi Real.pi_ne_zero)
  exact isLocalHomeomorph_circleExp.isOpenMap.comp e.isOpenMap

public theorem isOpenEmbedding_param :
    IsOpenEmbedding ((Ioo (-1 : ℝ) 1).domRestrict param) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_param.comp continuous_subtype_val
  · intro x y h
    exact Subtype.ext (injOn_param x.property y.property h)
  · exact isOpenMap_param.comp isOpen_Ioo.isOpenMap_subtype_val

end SphereSixComplex.CircleCell

namespace SphereSixComplex.SupNormBall

public theorem append_mem_ball_iff (m n : ℕ) (x : (Fin m → ℝ) × (Fin n → ℝ)) :
    Fin.append x.1 x.2 ∈ Metric.ball 0 1 ↔
      x ∈ (Metric.ball (0 : Fin m → ℝ) 1) ×ˢ (Metric.ball (0 : Fin n → ℝ) 1) := by
  simp [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (show (0 : ℝ) < 1 by norm_num),
    Fin.forall_fin_add]

public def prodHomeomorph (m n : ℕ) :
    Metric.ball (0 : Fin (m + n) → ℝ) 1 ≃ₜ
      (Metric.ball (0 : Fin m → ℝ) 1) × (Metric.ball (0 : Fin n → ℝ) 1) :=
  ((Fin.appendHomeomorph (X := ℝ) m n).subtype
    (fun x ↦ (append_mem_ball_iff m n x).symm)).symm.trans
      (Homeomorph.Set.prod _ _)

public def oneHomeomorphIoo : Metric.ball (0 : Fin 1 → ℝ) 1 ≃ₜ Ioo (-1 : ℝ) 1 :=
  (Homeomorph.funUnique (Fin 1) ℝ).subtype (fun x ↦ by
    simp [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (show (0 : ℝ) < 1 by norm_num),
      Real.norm_eq_abs, abs_lt])

end SphereSixComplex.SupNormBall

namespace SphereSixComplex.CircleCell

public def ballParam (x : Fin 1 → ℝ) : Circle := param (x 0)

public theorem isEmbedding_ballParam :
    IsEmbedding ((Metric.ball (0 : Fin 1 → ℝ) 1).domRestrict ballParam) := by
  have heq : (Metric.ball (0 : Fin 1 → ℝ) 1).domRestrict ballParam =
      (Ioo (-1 : ℝ) 1).domRestrict param ∘ SupNormBall.oneHomeomorphIoo := rfl
  rw [heq]
  exact isOpenEmbedding_param.isEmbedding.comp SupNormBall.oneHomeomorphIoo.isEmbedding

end SphereSixComplex.CircleCell

end
