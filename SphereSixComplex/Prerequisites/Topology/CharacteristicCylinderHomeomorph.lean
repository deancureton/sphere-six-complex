module

public import SphereSixComplex.Prerequisites.Topology.CylinderRelativeContraction
public import SphereSixComplex.Prerequisites.Topology.ConstructedCircleCell

@[expose] public section
noncomputable section
open Set Topology
namespace SphereSixComplex

public theorem cwAppend_mem_closedBall (m n : ℕ) (x : (Fin m → ℝ) × (Fin n → ℝ)) :
    Fin.append x.1 x.2 ∈ Metric.closedBall 0 1 ↔
      x ∈ (Metric.closedBall (0 : Fin m → ℝ) 1) ×ˢ (Metric.closedBall (0 : Fin n → ℝ) 1) := by
  simp [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num), Fin.forall_fin_add]

public def cwClosedBallSplitHomeomorph (m n : ℕ) :
    CWCharacteristicClosedBall (m + n) ≃ₜ
      CWCharacteristicClosedBall m × CWCharacteristicClosedBall n :=
  ((Fin.appendHomeomorph (X := ℝ) m n).subtype
    (fun x ↦ (cwAppend_mem_closedBall m n x).symm)).symm.trans
      (Homeomorph.Set.prod _ _)

public def cwClosedBallOneIntervalHomeomorph :
    CWCharacteristicClosedBall 1 ≃ₜ Icc (-1 : ℝ) 1 :=
  (Homeomorph.funUnique (Fin 1) ℝ).subtype (fun x ↦ by
    simp [Metric.mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num), Real.norm_eq_abs, abs_le])

public def cwCharacteristicCylinderHomeomorph (n : ℕ) :
    unitInterval × CWCharacteristicClosedBall n ≃ₜ CWCharacteristicClosedBall (n + 1) :=
  (Homeomorph.prodComm _ _).trans
    ((Homeomorph.prodCongr (Homeomorph.refl _)
      ((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm.trans cwClosedBallOneIntervalHomeomorph.symm)).trans
        (cwClosedBallSplitHomeomorph n 1).symm)

public theorem cwCharacteristicCylinderHomeomorph_apply (n : ℕ)
    (t : unitInterval) (b : CWCharacteristicClosedBall n) :
    (cwCharacteristicCylinderHomeomorph n (t, b)).1 = Fin.append b.1 ![2 * (t : ℝ) - 1] := by
  change Fin.append b.1
    (cwClosedBallOneIntervalHomeomorph.symm ((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm t)).1 = _
  congr 1
  ext j
  fin_cases j
  change (1 - (-1 : ℝ)) * (t : ℝ) + -1 = 2 * (t : ℝ) - 1
  ring

public theorem cwClosedBall_mem_sphere_iff_not_mem_ball (n : ℕ)
    (b : CWCharacteristicClosedBall n) :
    b.1 ∈ Metric.sphere 0 1 ↔ b.1 ∉ Metric.ball 0 1 := by
  have hb : ‖b.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using b.2
  simp only [Metric.mem_sphere, Metric.mem_ball, dist_zero_right, not_lt]
  exact ⟨fun h ↦ h.ge, fun h ↦ le_antisymm hb h⟩

public theorem cwCharacteristicCylinderHomeomorph_mem_ball (n : ℕ)
    (t : unitInterval) (b : CWCharacteristicClosedBall n) :
    (cwCharacteristicCylinderHomeomorph n (t, b)).1 ∈ Metric.ball 0 1 ↔
      b.1 ∈ Metric.ball 0 1 ∧ 0 < (t : ℝ) ∧ (t : ℝ) < 1 := by
  rw [cwCharacteristicCylinderHomeomorph_apply,
    SupNormBall.append_mem_ball_iff n 1
      (b.1, ![2 * (t : ℝ) - 1])]
  simp only [Set.mem_prod]
  apply and_congr_right
  intro _
  simp only [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1),
    Fin.forall_fin_one, Matrix.cons_val_zero, Real.norm_eq_abs, abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

public theorem cwCharacteristicCylinderHomeomorph_boundary (n : ℕ)
    (t : unitInterval) (b : CWCharacteristicClosedBall n) :
    (cwCharacteristicCylinderHomeomorph n (t, b)).1 ∈ Metric.sphere 0 1 ↔
      (t, b) ∈ cylinderBoundary {x : CWCharacteristicClosedBall n | x.1 ∈ Metric.sphere 0 1} := by
  rw [cwClosedBall_mem_sphere_iff_not_mem_ball, cwCharacteristicCylinderHomeomorph_mem_ball]
  change ¬(_ ∧ _ ∧ _) ↔ t = 0 ∨ t = 1 ∨ b.1 ∈ Metric.sphere 0 1
  rw [cwClosedBall_mem_sphere_iff_not_mem_ball]
  have h₀ : ¬0 < (t : ℝ) ↔ t = 0 := by
    rw [not_lt]
    constructor
    · intro h; exact Subtype.ext (le_antisymm h t.2.1)
    · intro h; subst t; rfl
  have h₁ : ¬(t : ℝ) < 1 ↔ t = 1 := by
    rw [not_lt]
    constructor
    · intro h; exact Subtype.ext (le_antisymm t.2.2 h)
    · intro h; subst t; rfl
  simp only [not_and_or, h₀, h₁]
  tauto

end SphereSixComplex
