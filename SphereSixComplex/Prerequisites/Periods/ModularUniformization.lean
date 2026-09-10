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

/-- The identity-source modular model. This is a useful diagnostic instance of
`TriangleUniformization`, but it is not the paper's source uniformization: the source triangle
upper half-plane has a genuine order-four action. `CanonicalObstruction.lean` proves that this
instance admits no compatible `mu` transformation laws. -/
public noncomputable def canonicalTriangleUniformization : TriangleUniformization where
  sourceAction := (MulAction.toPermHom (GL (Fin 2) ℝ) UpperHalfPlane).comp rhoTauReal
  sourceAction_contMDiff g n := by
    apply UpperHalfPlane.contMDiff_smul
    simp [rhoTauReal, modularToReal]
  coordinate z := normalizedJ z / 1728
  coordinate_holomorphic :=
    normalizedJ_mdifferentiable.div mdifferentiable_const (by norm_num)
  coordinate_invariant g z := by
    change normalizedJ (rhoTauReal g • z) / 1728 = normalizedJ z / 1728
    rw [show rhoTauReal g = Matrix.SpecialLinearGroup.mapGL ℝ (rhoTau g) by
      simp [rhoTauReal, modularToReal]]
    rw [normalizedJ_modular_invariant]
  zOne := ellipticThreeParameter
  zTwo := UpperHalfPlane.I
  zOne_fixed := by
    change rhoTauReal g₁ • ellipticThreeParameter = ellipticThreeParameter
    apply UpperHalfPlane.coe_injective
    rw [rhoTauReal_g1_smul]
    have hz : (ellipticThreeParameter : ℂ) ≠ 0 := ellipticThreeParameter.ne_zero
    field_simp [hz]
    rw [show (ellipticThreeParameter : ℂ) = UpperHalfPlane.ρ + 1 by rfl]
    rw [show ((UpperHalfPlane.ρ : ℂ) + 1) ^ 2 =
        (UpperHalfPlane.ρ : ℂ) ^ 2 + 2 * UpperHalfPlane.ρ + 1 by ring]
    rw [UpperHalfPlane.ρ_sq]
    ring
  zTwo_fixed := by
    change rhoTauReal g₂ • UpperHalfPlane.I = UpperHalfPlane.I
    apply UpperHalfPlane.coe_injective
    rw [rhoTauReal_g2_smul]
    norm_num [UpperHalfPlane.I]
  cuspRegion := {z | 1 ≤ z.im}
  cuspRegion_nonempty := by
    refine ⟨UpperHalfPlane.I, ?_⟩
    norm_num [UpperHalfPlane.I]
  cuspRegion_invariant z := by
    change 1 ≤ (rhoTauReal g₀ • z).im ↔ 1 ≤ z.im
    rw [rhoTauReal_g₀]
    have h := congrArg Complex.im (rhoTauReal_g0_smul z)
    norm_num at h
    rw [h]

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
