module

public import SphereSixComplex.Prerequisites.TriangleGroup.ModularParameter
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation

open Matrix UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

@[expose] public noncomputable def normalizedJ (z : UpperHalfPlane) : ℂ :=
  ModularForm.E₄ z ^ 3 / ModularForm.discriminant z

public theorem discriminant_mdifferentiable :
    MDiff (ModularForm.discriminant : UpperHalfPlane → ℂ) := by
  change MDiff (fun z : UpperHalfPlane ↦ ModularForm.eta z ^ 24)
  exact (show MDiff (fun z : UpperHalfPlane ↦ ModularForm.eta z) by
    intro z
    exact MDifferentiableAt.comp z
      (DifferentiableAt.mdifferentiableAt
        (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet z.im_pos))
      z.mdifferentiable_coe).pow 24

public theorem normalizedJ_mdifferentiable : MDiff normalizedJ := by
  exact ((ModularFormClass.holo ModularForm.E₄).pow 3).div discriminant_mdifferentiable
    ModularForm.discriminant_ne_zero

public theorem normalizedJ_modular_invariant (g : ModularMatrix) (z : UpperHalfPlane) :
    normalizedJ (Matrix.SpecialLinearGroup.mapGL ℝ g • z) = normalizedJ z := by
  have hE := congrFun (ModularForm.E₄.slash_action_eq'
    (Matrix.SpecialLinearGroup.mapGL ℝ g) ⟨g, rfl⟩) z
  have hD := congrFun (CuspForm.discriminant.slash_action_eq'
    (Matrix.SpecialLinearGroup.mapGL ℝ g) ⟨g, rfl⟩) z
  norm_num [ModularForm.slash_apply, UpperHalfPlane.σ] at hE hD
  have hd := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) z
  field_simp [hd] at hE hD
  simp only [normalizedJ]
  rw [hE, hD]
  field_simp [ModularForm.discriminant_ne_zero z, hd]

@[expose] public def ellipticThreeParameter : UpperHalfPlane :=
  ⟨(UpperHalfPlane.ρ : ℂ) + 1, by simpa using UpperHalfPlane.ρ.im_pos⟩

public structure TriangleUniformization where
  sourceAction : Delta →* Equiv.Perm UpperHalfPlane
  sourceAction_contMDiff : ∀ g (n : WithTop ℕ∞), ContMDiff (modelWithCornersSelf ℂ ℂ)
    (modelWithCornersSelf ℂ ℂ) n (fun z : UpperHalfPlane ↦ sourceAction g • z)
  coordinate : UpperHalfPlane → ℂ
  coordinate_holomorphic : MDiff coordinate
  coordinate_invariant : ∀ g z, coordinate (sourceAction g • z) = coordinate z
  zOne : UpperHalfPlane
  zTwo : UpperHalfPlane
  zOne_fixed : sourceAction g₁ • zOne = zOne
  zTwo_fixed : sourceAction g₂ • zTwo = zTwo
  cuspRegion : Set UpperHalfPlane
  cuspRegion_nonempty : cuspRegion.Nonempty
  cuspRegion_invariant : ∀ z, sourceAction g₀ • z ∈ cuspRegion ↔ z ∈ cuspRegion


public def BoundedOn (f : UpperHalfPlane → ℂ) (s : Set UpperHalfPlane) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ s, ‖f z‖ ≤ C

/-- Subtracting a constant preserves boundedness on a set. -/
public theorem BoundedOn.sub_const {f : UpperHalfPlane → ℂ} {s : Set UpperHalfPlane}
    (h : BoundedOn f s) (c : ℂ) : BoundedOn (fun z ↦ f z - c) s := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C + ‖c‖, add_nonneg hC (norm_nonneg c), ?_⟩
  intro z hz
  exact (norm_sub_le (f z) c).trans (add_le_add (hbound z hz) le_rfl)

end SphereSixComplex.Periods
