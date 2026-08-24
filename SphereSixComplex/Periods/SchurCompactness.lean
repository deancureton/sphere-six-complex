module

public import SphereSixComplex.Periods.Functions
import all SphereSixComplex.Periods.Functions
import all SphereSixComplex.TriangleGroup.Representation

/-!
# Compactness reduction for period nondegeneracy

This file formalizes the compactness argument in Proposition 3.15 for an arbitrary triangle
uniformization. The Schur quantity is invariant under the full source action, is bounded above on
the distinguished cusp region, and is therefore globally bounded above once a compact core meets
every remaining orbit. Shifting `beta` by a negative imaginary constant then gives a nondegenerate
period family.
-/

open Matrix UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

private theorem cyclicThree_cases (a : CyclicThree) :
    a = 1 ∨ a = Multiplicative.ofAdd (1 : ZMod 3) ∨
      a = Multiplicative.ofAdd (2 : ZMod 3) := by
  have hlt : a.toAdd.val < 3 := ZMod.val_lt a.toAdd
  interval_cases h : a.toAdd.val
  · left
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 3
    norm_num at h ⊢
    exact h
  · right
    left
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 3
    norm_num at h ⊢
    exact h
  · right
    right
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 3
    norm_num at h ⊢
    exact h

private theorem cyclicFour_cases (a : CyclicFour) :
    a = 1 ∨ a = Multiplicative.ofAdd (1 : ZMod 4) ∨
      a = Multiplicative.ofAdd (2 : ZMod 4) ∨
        a = Multiplicative.ofAdd (3 : ZMod 4) := by
  have hlt : a.toAdd.val < 4 := ZMod.val_lt a.toAdd
  interval_cases h : a.toAdd.val
  · left
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 4
    norm_num at h ⊢
    exact h
  · right
    left
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 4
    norm_num at h ⊢
    exact h
  · right
    right
    left
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 4
    norm_num at h ⊢
    exact h
  · right
    right
    right
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 4
    norm_num at h ⊢
    exact h

private theorem inl_two :
    Monoid.Coprod.inl (Multiplicative.ofAdd (2 : ZMod 3)) = g₁ * g₁ := by
  calc
    Monoid.Coprod.inl (Multiplicative.ofAdd (2 : ZMod 3)) =
        Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 3) *
          Multiplicative.ofAdd (1 : ZMod 3)) := by congr 1
    _ = g₁ * g₁ := by rw [map_mul]; rfl

private theorem inr_two :
    Monoid.Coprod.inr (Multiplicative.ofAdd (2 : ZMod 4)) = g₂ * g₂ := by
  calc
    Monoid.Coprod.inr (Multiplicative.ofAdd (2 : ZMod 4)) =
        Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4) *
          Multiplicative.ofAdd (1 : ZMod 4)) := by congr 1
    _ = g₂ * g₂ := by rw [map_mul]; rfl

private theorem inr_three :
    Monoid.Coprod.inr (Multiplicative.ofAdd (3 : ZMod 4)) = g₂ * g₂ * g₂ := by
  calc
    Monoid.Coprod.inr (Multiplicative.ofAdd (3 : ZMod 4)) =
        Monoid.Coprod.inr ((Multiplicative.ofAdd (1 : ZMod 4) *
          Multiplicative.ofAdd (1 : ZMod 4)) *
            Multiplicative.ofAdd (1 : ZMod 4)) := by congr 1
    _ = g₂ * g₂ * g₂ := by rw [map_mul, map_mul]; rfl

/-- The Schur quantity is invariant under the order-three source generator. -/
public theorem PrePeriodFunctions.schurQuantity_transform_one
    {U : TriangleUniformization} (F : PrePeriodFunctions U) (z : UpperHalfPlane) :
    schurQuantity (periodValues F.tau F.mu F.beta (U.sourceAction g₁ • z)) =
      schurQuantity (periodValues F.tau F.mu F.beta z) := by
  rw [F.transform_one]
  exact schurQuantity_transformOne _ (F.tau z).im_pos.ne'

/-- The Schur quantity is invariant under the order-four source generator. -/
public theorem PrePeriodFunctions.schurQuantity_transform_two
    {U : TriangleUniformization} (F : PrePeriodFunctions U) (z : UpperHalfPlane) :
    schurQuantity (periodValues F.tau F.mu F.beta (U.sourceAction g₂ • z)) =
      schurQuantity (periodValues F.tau F.mu F.beta z) := by
  rw [F.transform_two]
  exact schurQuantity_transformTwo _ (F.tau z).im_pos.ne'

/-- The generator calculations imply invariance under every element of the source triangle
group. -/
public theorem PrePeriodFunctions.schurQuantity_invariant
    {U : TriangleUniformization} (F : PrePeriodFunctions U) (g : Delta)
    (z : UpperHalfPlane) :
    schurQuantity (periodValues F.tau F.mu F.beta (U.sourceAction g • z)) =
      schurQuantity (periodValues F.tau F.mu F.beta z) := by
  revert z
  induction g using Monoid.Coprod.induction_on with
  | inl a =>
      intro z
      rcases cyclicThree_cases a with rfl | rfl | rfl
      · simp
      · exact F.schurQuantity_transform_one z
      · rw [inl_two, map_mul, mul_smul, F.schurQuantity_transform_one,
          F.schurQuantity_transform_one]
  | inr a =>
      intro z
      rcases cyclicFour_cases a with rfl | rfl | rfl | rfl
      · simp
      · exact F.schurQuantity_transform_two z
      · rw [inr_two, map_mul, mul_smul, F.schurQuantity_transform_two,
          F.schurQuantity_transform_two]
      · rw [inr_three, map_mul, map_mul, mul_smul, mul_smul,
          F.schurQuantity_transform_two, F.schurQuantity_transform_two,
          F.schurQuantity_transform_two]
  | mul x y hx hy =>
      intro z
      rw [map_mul, mul_smul, hx, hy]

/-- The Schur quantity associated with holomorphic pre-period data is continuous. -/
public theorem PrePeriodFunctions.schurQuantity_continuous
    {U : TriangleUniformization} (F : PrePeriodFunctions U) :
    Continuous fun z : UpperHalfPlane =>
      schurQuantity (periodValues F.tau F.mu F.beta z) := by
  have htau : Continuous F.tau := F.tau_holomorphic.continuous
  have hmu : Continuous F.mu := F.mu_holomorphic.continuous
  have hbeta : Continuous F.beta := F.beta_holomorphic.continuous
  change Continuous fun z : UpperHalfPlane =>
    (F.beta z).im - 6 * (F.mu z).im ^ 2 / (F.tau z).im
  exact (Complex.continuous_im.comp hbeta).sub
    ((((Complex.continuous_im.comp hmu).pow 2).const_mul 6).div
      (UpperHalfPlane.continuous_im.comp htau) fun z => (F.tau z).im_pos.ne')

/-- The cusp bound on `beta + tau` bounds the Schur quantity from above on the distinguished
cusp region. -/
public theorem PrePeriodFunctions.schurQuantity_cusp_bounded_above
    {U : TriangleUniformization} (F : PrePeriodFunctions U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ U.cuspRegion,
      schurQuantity (periodValues F.tau F.mu F.beta z) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := F.beta_add_tau_cusp_bounded
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hnonneg : 0 ≤ 6 * (F.mu z).im ^ 2 / (F.tau z).im := by positivity
  have hbeta : (F.beta z).im ≤ (F.beta z + (F.tau z : ℂ)).im := by
    rw [Complex.add_im, UpperHalfPlane.coe_im]
    linarith [(F.tau z).im_pos]
  calc
    schurQuantity (periodValues F.tau F.mu F.beta z) =
        (F.beta z).im - 6 * (F.mu z).im ^ 2 / (F.tau z).im := rfl
    _ ≤ (F.beta z).im := sub_le_self _ hnonneg
    _ ≤ (F.beta z + (F.tau z : ℂ)).im := hbeta
    _ ≤ ‖F.beta z + (F.tau z : ℂ)‖ := Complex.im_le_norm _
    _ ≤ C := hbound z hz

/-- A compact core for a triangle quotient outside its distinguished cusp region. -/
public structure QuotientCompactCore (U : TriangleUniformization) where
  /-- A compact subset meeting every orbit not represented in the cusp region. -/
  carrier : Set UpperHalfPlane
  /-- Compactness of the core. -/
  compact : IsCompact carrier
  /-- Every source orbit meets either the cusp region or the compact core. -/
  cover : ∀ z, ∃ g : Delta,
    U.sourceAction g • z ∈ U.cuspRegion ∨ U.sourceAction g • z ∈ carrier

/-- Cusp boundedness and a compact quotient core give the global upper bound used in the final
imaginary shift of `beta`. -/
public theorem PrePeriodFunctions.schurQuantity_bounded_above_of_compactCore
    {U : TriangleUniformization} (F : PrePeriodFunctions U) (K : QuotientCompactCore U) :
    ∃ M : ℝ, ∀ z, schurQuantity (periodValues F.tau F.mu F.beta z) ≤ M := by
  obtain ⟨C, -, hC⟩ := F.schurQuantity_cusp_bounded_above
  obtain ⟨M, hM⟩ := K.compact.bddAbove_image F.schurQuantity_continuous.continuousOn
  refine ⟨max C M, ?_⟩
  intro z
  obtain ⟨g, hz | hz⟩ := K.cover z
  · calc
      schurQuantity (periodValues F.tau F.mu F.beta z) =
          schurQuantity (periodValues F.tau F.mu F.beta (U.sourceAction g • z)) :=
        (F.schurQuantity_invariant g z).symm
      _ ≤ C := hC _ hz
      _ ≤ max C M := le_max_left C M
  · calc
      schurQuantity (periodValues F.tau F.mu F.beta z) =
          schurQuantity (periodValues F.tau F.mu F.beta (U.sourceAction g • z)) :=
        (F.schurQuantity_invariant g z).symm
      _ ≤ M := hM ⟨_, hz, rfl⟩
      _ ≤ max C M := le_max_right C M

/-- Shift only the `beta` component of a period parameter by `-c i`. -/
@[expose] public noncomputable def shiftParametersBeta (x : Parameters) (c : ℝ) : Parameters where
  tau := x.tau
  mu := x.mu
  beta := x.beta - c * Complex.I

public theorem shiftParametersBeta_transformOne (x : Parameters) (c : ℝ) :
    shiftParametersBeta (transformOne x) c = transformOne (shiftParametersBeta x c) := by
  apply Parameters.ext
  · rfl
  · rfl
  · simp [shiftParametersBeta, transformOne.eq_def]
    ring

public theorem shiftParametersBeta_transformTwo (x : Parameters) (c : ℝ) :
    shiftParametersBeta (transformTwo x) c = transformTwo (shiftParametersBeta x c) := by
  apply Parameters.ext
  · rfl
  · rfl
  · simp [shiftParametersBeta, transformTwo.eq_def]
    ring

public theorem shiftParametersBeta_transformCusp (x : Parameters) (c : ℝ) :
    shiftParametersBeta (transformCusp x) c = transformCusp (shiftParametersBeta x c) := by
  apply Parameters.ext
  · rfl
  · rfl
  · simp [shiftParametersBeta, transformCusp.eq_def]
    ring

/-- Subtracting a constant imaginary part preserves all analytic and equivariance properties of
pre-period data. -/
public noncomputable def PrePeriodFunctions.shiftBeta
    {U : TriangleUniformization} (F : PrePeriodFunctions U) (c : ℝ) : PrePeriodFunctions U where
  tau := F.tau
  mu := F.mu
  beta z := F.beta z - c * Complex.I
  tau_holomorphic := F.tau_holomorphic
  mu_holomorphic := F.mu_holomorphic
  beta_holomorphic := F.beta_holomorphic.sub mdifferentiable_const
  modular_equation := F.modular_equation
  tau_at_zOne := F.tau_at_zOne
  tau_at_zTwo := F.tau_at_zTwo
  transform_one z := by
    change shiftParametersBeta (periodValues F.tau F.mu F.beta (U.sourceAction g₁ • z)) c =
      transformOne (shiftParametersBeta (periodValues F.tau F.mu F.beta z) c)
    rw [F.transform_one, shiftParametersBeta_transformOne]
  transform_two z := by
    change shiftParametersBeta (periodValues F.tau F.mu F.beta (U.sourceAction g₂ • z)) c =
      transformTwo (shiftParametersBeta (periodValues F.tau F.mu F.beta z) c)
    rw [F.transform_two, shiftParametersBeta_transformTwo]
  transform_cusp z := by
    change shiftParametersBeta (periodValues F.tau F.mu F.beta (U.sourceAction g₀ • z)) c =
      transformCusp (shiftParametersBeta (periodValues F.tau F.mu F.beta z) c)
    rw [F.transform_cusp, shiftParametersBeta_transformCusp]
  mu_cusp_bounded := F.mu_cusp_bounded
  beta_add_tau_cusp_bounded := by
    convert F.beta_add_tau_cusp_bounded.sub_const (c * Complex.I) using 1
    funext z
    ring

/-- A compact quotient core converts equivariant holomorphic pre-period data into a nondegenerate
period family by the paper's final imaginary shift. -/
public theorem PrePeriodFunctions.exists_shiftedPeriodFunctions
    {U : TriangleUniformization} (F : PrePeriodFunctions U) (K : QuotientCompactCore U) :
    Nonempty (PeriodFunctions U) := by
  obtain ⟨M, hM⟩ := F.schurQuantity_bounded_above_of_compactCore K
  let c : ℝ := max M 0 + 1
  let E := F.shiftBeta c
  refine ⟨{
    toPrePeriodFunctions := E
    setup_inequalities := ?_
  }⟩
  intro z
  constructor
  · exact (E.tau z).im_pos
  · change schurQuantity (periodValues E.tau E.mu E.beta z) < 0
    have hshift : schurQuantity (periodValues E.tau E.mu E.beta z) =
        schurQuantity (periodValues F.tau F.mu F.beta z) - c := by
      simp [E, PrePeriodFunctions.shiftBeta, schurQuantity, periodValues,
        Complex.mul_im]
      ring
    rw [hshift]
    have hc : M - c < 0 := by
      dsimp [c]
      linarith [le_max_left M 0]
    exact lt_of_le_of_lt (sub_le_sub_right (hM z) c) hc

/-- The generic compactness argument supplies the exact Theorem 3.4 existence statement. -/
public theorem theorem3_4Existence_of_prePeriodFunctions_compactCore
    {U : TriangleUniformization} (F : PrePeriodFunctions U) (K : QuotientCompactCore U) :
    Theorem3_4Existence U :=
  F.exists_shiftedPeriodFunctions K

end SphereSixComplex.Periods
