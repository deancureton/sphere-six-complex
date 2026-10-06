module

public import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.Variational.ZerothOrderExistence

@[expose] public section


noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

attribute [local instance] variationalAugmentedEndNormedAddCommGroup

section ParameterizedCkWitness

theorem exists_isVariationalFlowProjection_of_C
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
    {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (ht₀_Ioo : t₀ ∈ Set.Ioo tmin tmax)
    (hr_pos : (0 : ℝ) < (r : ℝ))
    (k : ℕ)
    (hf_C : ContDiffOn ℝ ((k : ℕ∞) + 1) (Function.uncurry f)
      (Set.univ : Set (ℝ × E))) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
      (Y : E × ℝ → (E →L[ℝ] E)),
      IsVariationalFlowProjection hΦ T ρ Y (k : ℕ∞) := by
  classical
  suffices haux : ∀ (k : ℕ) (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] [FiniteDimensional ℝ E]
      {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
      {Φ : E × ℝ → E}
      (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
      (_ht₀_Ioo : t₀ ∈ Set.Ioo tmin tmax)
      (_hr_pos : (0 : ℝ) < (r : ℝ))
      (_hf_C : ContDiffOn ℝ ((k : ℕ∞) + 1) (Function.uncurry f)
        (Set.univ : Set (ℝ × E))),
      ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
        (Y : E × ℝ → (E →L[ℝ] E)),
        IsVariationalFlowProjection hΦ T ρ Y (k : ℕ∞) by
    exact haux k E hΦ ht₀_Ioo hr_pos hf_C
  clear hΦ ht₀_Ioo hr_pos hf_C
  intro k
  induction k with
  | zero =>
      intro E _ _ _ _ f t₀ x₀ r tmin tmax Φ hΦ ht₀_Ioo hr_pos hf_C
      have hf_C1 : ContDiffOn ℝ 1 (Function.uncurry f) (Set.univ : Set (ℝ × E)) := by
        simpa using hf_C
      have h_witness := exists_isVariationalFlowProjection_zero_of_C1
        hΦ ht₀_Ioo hr_pos hf_C1
      obtain ⟨T, ρ, hT, hρ, Y, hY⟩ := h_witness
      refine ⟨T, ρ, hT, hρ, Y, ?_⟩
      have h_zero : ((0 : ℕ) : ℕ∞) = (0 : ℕ∞) := by norm_cast
      rw [h_zero]
      exact hY
  | succ n IH =>
      intro E _ _ _ _ f t₀ x₀ r tmin tmax Φ hΦ ht₀_Ioo hr_pos hf_C
      have h_eq_succ_plus_one : (((n + 1 : ℕ) : ℕ∞) + 1 : WithTop ℕ∞) =
          ((n : ℕ∞) + 2 : WithTop ℕ∞) := by push_cast; ring
      have hf_Cn_plus_2 : ContDiffOn ℝ ((n : ℕ∞) + 2)
          (Function.uncurry f) (Set.univ : Set (ℝ × E)) := by
        have := hf_C
        rw [h_eq_succ_plus_one] at this
        exact this
      have hf_C1 : ContDiffOn ℝ 1 (Function.uncurry f) (Set.univ : Set (ℝ × E)) := by
        refine hf_Cn_plus_2.of_le ?_
        have h1 : (1 : WithTop ℕ∞) ≤ 2 := by decide
        have h2 : (2 : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) + 2 := le_add_self
        exact le_trans h1 h2
      have hf_Cn_plus_2_as_succ : ContDiffOn ℝ (((n : ℕ∞) + 1) + 1)
          (Function.uncurry f) (Set.univ : Set (ℝ × E)) := by
        have h_eq_wt :
            ((((n : ℕ∞) : WithTop ℕ∞) + 1) + 1 : WithTop ℕ∞) =
            (((n : ℕ∞) : WithTop ℕ∞) + 2 : WithTop ℕ∞) := by
          have h2 : ((2 : WithTop ℕ∞) = 1 + 1) := by decide
          rw [h2, ← add_assoc]
        rw [h_eq_wt]
        exact hf_Cn_plus_2
      have h_augmentedVectorField_Cn_plus_1 :
          ContDiffOn ℝ ((n : ℕ∞) + 1) (Function.uncurry (augmentedVectorField f))
            (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
        augmentedVectorField_uncurry_contDiff (k := ((n : ℕ∞) + 1)) hf_Cn_plus_2_as_succ
      have h_augmentedVectorField_C1 : ContDiffOn ℝ 1 (Function.uncurry (augmentedVectorField f))
          (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
        refine h_augmentedVectorField_Cn_plus_1.of_le ?_
        have h1 : (1 : ℕ∞) ≤ (n : ℕ∞) + 1 := le_add_self
        exact_mod_cast h1
      obtain ⟨R_aug, ε_aug, hR_aug_pos, hε_aug_pos, aΦ, haΦ⟩ :=
        exists_isLocalFlow_of_contDiffOn_univ (augmentedVectorField f) h_augmentedVectorField_C1 t₀
          (x₀, ContinuousLinearMap.id ℝ E)
      have hR_aug_R : (0 : ℝ) < (R_aug : ℝ) := by exact_mod_cast hR_aug_pos
      have ht₀_a_Ioo : t₀ ∈ Set.Ioo (t₀ - ε_aug) (t₀ + ε_aug) :=
        ⟨by linarith, by linarith⟩
      have hIH := IH (E × (E →L[ℝ] E)) (f := augmentedVectorField f) (t₀ := t₀)
        (x₀ := (x₀, ContinuousLinearMap.id ℝ E)) (r := R_aug)
        (tmin := t₀ - ε_aug) (tmax := t₀ + ε_aug) (Φ := aΦ)
        haΦ ht₀_a_Ioo hR_aug_R h_augmentedVectorField_Cn_plus_1
      obtain ⟨T_ih, ρ_ih, hT_ih_pos, hρ_ih_pos, Y_ih, hY_ih⟩ := hIH
      have h_succ := exists_isVariationalFlowProjection_succ_C_step
        (f := f) (t₀ := t₀) (x₀ := x₀) (r := r) (tmin := tmin) (tmax := tmax)
        (Φ := Φ) hΦ ht₀_Ioo hr_pos n hf_Cn_plus_2
        (R_aug := R_aug) (tmin_a := t₀ - ε_aug) (tmax_a := t₀ + ε_aug)
        (aΦ := aΦ) haΦ ht₀_a_Ioo hR_aug_R
        (T_ih := T_ih) (ρ_ih := ρ_ih) (Y_ih := Y_ih)
        hT_ih_pos hρ_ih_pos hY_ih
      obtain ⟨T, ρ, hT, hρ, Y, hY⟩ := h_succ
      refine ⟨T, ρ, hT, hρ, Y, ?_⟩
      have h_lvl : ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; ring
      rw [h_lvl]
      exact hY

end ParameterizedCkWitness


end Flow
end ODE
end Analysis
end DifferentialGeometry

end
