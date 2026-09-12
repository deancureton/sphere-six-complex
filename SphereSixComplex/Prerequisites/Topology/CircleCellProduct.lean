module

public import SphereSixComplex.Prerequisites.Topology.ConstructedCircleCell
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Push

@[expose] public section
noncomputable section
open Set Topology Matrix Real

namespace SphereSixComplex.CircleCell

public def onePhase (i : Fin 2) (x : Fin 1 → ℝ) : Fin 2 → Circle :=
  if i = 0 then ![CircleCell.ballParam x, 1] else ![1, CircleCell.ballParam x]

public def twoPhase (x : Fin 2 → ℝ) : Fin 2 → Circle :=
  fun j ↦ CircleCell.param (x j)

public theorem isEmbedding_onePhase (i : Fin 2) :
    IsEmbedding ((Metric.ball (0 : Fin 1 → ℝ) 1).domRestrict (onePhase i)) := by
  fin_cases i
  · exact (Homeomorph.finTwoArrow (X := Circle)).symm.isEmbedding.comp
      ((isEmbedding_prodMkLeft (1 : Circle)).comp CircleCell.isEmbedding_ballParam)
  · exact (Homeomorph.finTwoArrow (X := Circle)).symm.isEmbedding.comp
      ((isEmbedding_prodMkRight (1 : Circle)).comp CircleCell.isEmbedding_ballParam)

public theorem isEmbedding_twoPhase :
    IsEmbedding ((Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict twoPhase) := by
  have heq : (Metric.ball (0 : Fin 2 → ℝ) 1).domRestrict twoPhase =
      (Homeomorph.finTwoArrow (X := Circle)).symm ∘
        Prod.map ((Metric.ball (0 : Fin 1 → ℝ) 1).domRestrict CircleCell.ballParam)
          ((Metric.ball (0 : Fin 1 → ℝ) 1).domRestrict CircleCell.ballParam) ∘
        (SupNormBall.prodHomeomorph 1 1) := by
    funext x j
    fin_cases j <;> rfl
  rw [heq]
  exact (Homeomorph.finTwoArrow (X := Circle)).symm.isEmbedding.comp
    ((CircleCell.isEmbedding_ballParam.prodMap CircleCell.isEmbedding_ballParam).comp
      (SupNormBall.prodHomeomorph 1 1).isEmbedding)

public theorem continuous_onePhase (i : Fin 2) :
    Continuous (onePhase i) := by
  have h : Continuous CircleCell.ballParam := CircleCell.continuous_param.comp (continuous_apply 0)
  fin_cases i <;> unfold onePhase <;> dsimp <;> fun_prop

public theorem continuous_twoPhase : Continuous twoPhase := by
  exact continuous_pi fun j ↦ CircleCell.continuous_param.comp (continuous_apply j)

public theorem onePhase_eq_one_of_mem_sphere (i : Fin 2) (x : Fin 1 → ℝ)
    (hx : x ∈ Metric.sphere 0 1) : onePhase i x = 1 := by
  have hn : |x 0| = 1 := by simpa [Metric.mem_sphere, dist_zero_right, Pi.norm_def] using hx
  have hx' : x 0 = -1 ∨ x 0 = 1 := by
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hn with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hcell : CircleCell.ballParam x = 1 := by
    rcases hx' with h | h <;> simp [CircleCell.ballParam, h]
  fin_cases i <;> ext j <;> fin_cases j <;> simp [onePhase, hcell]

public theorem param_eq_one_of_abs_eq {t : ℝ} (ht : |t| = 1) :
    CircleCell.param t = 1 := by
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp ht with h | h <;> simp [h]

public theorem exists_twoPhase_eq_onePhase (x : Fin 2 → ℝ)
    (hx : x ∈ Metric.sphere 0 1) :
    ∃ (i : Fin 2) (y : Fin 1 → ℝ), y ∈ Metric.closedBall 0 1 ∧
      twoPhase x = onePhase i y := by
  have hnorm : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
  have hle : ∀ j, |x j| ≤ 1 := fun j ↦ by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm x j).trans_eq hnorm
  have hcoord : |x 0| = 1 ∨ |x 1| = 1 := by
    by_contra h
    push Not at h
    have hlt : ‖x‖ < 1 := (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr (by
      intro j
      fin_cases j
      · exact lt_of_le_of_ne (hle 0) h.1
      · exact lt_of_le_of_ne (hle 1) h.2)
    rw [hnorm] at hlt
    exact (lt_irrefl 1) hlt
  rcases hcoord with h | h
  · refine ⟨1, fun _ ↦ x 1, ?_, ?_⟩
    · have hb : |x 1| ≤ 1 := hle 1
      simpa [Metric.mem_closedBall, dist_zero_right, Pi.norm_def] using hb
    · have hc := param_eq_one_of_abs_eq h
      funext j
      fin_cases j <;> simp [twoPhase, onePhase,
        CircleCell.ballParam, hc]
  · refine ⟨0, fun _ ↦ x 0, ?_, ?_⟩
    · have hb : |x 0| ≤ 1 := hle 0
      simpa [Metric.mem_closedBall, dist_zero_right, Pi.norm_def] using hb
    · have hc := param_eq_one_of_abs_eq h
      funext j
      fin_cases j <;> simp [twoPhase, onePhase,
        CircleCell.ballParam, hc]

end SphereSixComplex.CircleCell
