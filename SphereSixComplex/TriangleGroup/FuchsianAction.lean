module

public import SphereSixComplex.TriangleGroup.Representation
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.GroupTheory.OrderOfElement
import all SphereSixComplex.TriangleGroup.Representation

/-!
# The Fuchsian source action of the `(3, 4, ∞)` triangle group

This is the source action from Proposition 2.11 of the paper.  It is deliberately distinct from
`rhoTauReal`: the latter is the modular action on the target of the period map and sends the
order-four generator to a projective transformation of order two.

The order-four source generator cannot be represented by a homomorphism into `GL (Fin 2) ℝ`,
because its fourth matrix power is the scalar `-1`.  The scalar acts trivially on the upper half-
plane, so the action is instead represented in `Equiv.Perm UpperHalfPlane`.
-/

open Matrix UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace SphereSixComplex.TriangleGroup

public abbrev SL2R := Matrix.SpecialLinearGroup (Fin 2) ℝ

private theorem gOne_eq : g₁ = Monoid.Coprod.inl (Multiplicative.ofAdd 1) :=
  SphereSixComplex.TriangleGroup.g₁.eq_def

private theorem gTwo_eq : g₂ = Monoid.Coprod.inr (Multiplicative.ofAdd 1) :=
  SphereSixComplex.TriangleGroup.g₂.eq_def

private theorem gCusp_eq : g₀ = (g₁ * g₂)⁻¹ :=
  SphereSixComplex.TriangleGroup.g₀.eq_def

/-- A lift of the order-three elliptic source transformation. -/
@[expose] public def fuchsianOneSL : SL2R :=
  ⟨!![-1, 1; -1, 0], by norm_num [Matrix.det_fin_two]⟩

/-- A lift of the order-four elliptic source transformation. -/
@[expose] public noncomputable def fuchsianTwoSL : SL2R :=
  ⟨!![0, -1; 1, Real.sqrt 2], by norm_num [Matrix.det_fin_two]⟩

/-- The inverse of the parabolic product, representing `g₀`. -/
@[expose] public noncomputable def fuchsianCuspSL : SL2R :=
  ⟨!![1, -(1 + Real.sqrt 2); 0, 1], by norm_num [Matrix.det_fin_two]⟩

@[expose] public noncomputable def fuchsianProductSL : SL2R :=
  ⟨!![1, 1 + Real.sqrt 2; 0, 1], by norm_num [Matrix.det_fin_two]⟩

@[expose] public noncomputable def fuchsianTwoSquaredSL : SL2R :=
  ⟨!![-1, -Real.sqrt 2; Real.sqrt 2, 1], by
    norm_num [Matrix.det_fin_two,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]⟩

@[expose] public noncomputable def fuchsianOneGL : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ fuchsianOneSL

@[expose] public noncomputable def fuchsianTwoGL : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ fuchsianTwoSL

@[expose] public noncomputable def fuchsianCuspGL : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ fuchsianCuspSL

@[expose] public noncomputable def fuchsianProductGL : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ fuchsianProductSL

@[expose] public noncomputable def fuchsianTwoSquaredGL : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ fuchsianTwoSquaredSL

public theorem fuchsianOneSL_pow_three : fuchsianOneSL ^ 3 = 1 := by
  apply Subtype.ext
  change (fuchsianOneSL : Matrix (Fin 2) (Fin 2) ℝ) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fuchsianOneSL, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem fuchsianTwoSL_pow_four : fuchsianTwoSL ^ 4 = -1 := by
  apply Subtype.ext
  change (fuchsianTwoSL : Matrix (Fin 2) (Fin 2) ℝ) ^ 4 = -1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fuchsianTwoSL, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

public theorem fuchsianTwoSL_pow_two :
    fuchsianTwoSL ^ 2 = fuchsianTwoSquaredSL := by
  apply Subtype.ext
  change (!![0, -1; 1, Real.sqrt 2] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 =
    !![-1, -Real.sqrt 2; Real.sqrt 2, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

public theorem fuchsianOneSL_mul_fuchsianTwoSL :
    fuchsianOneSL * fuchsianTwoSL = fuchsianProductSL := by
  apply Subtype.ext
  change (!![-1, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
      !![0, -1; 1, Real.sqrt 2] = !![1, 1 + Real.sqrt 2; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fuchsianOneSL, fuchsianTwoSL, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem fuchsianOneSL_mul_fuchsianTwoSL_mul_fuchsianCuspSL :
    fuchsianOneSL * fuchsianTwoSL * fuchsianCuspSL = 1 := by
  apply Subtype.ext
  change (!![-1, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
      !![0, -1; 1, Real.sqrt 2] * !![1, -(1 + Real.sqrt 2); 0, 1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fuchsianOneSL, fuchsianTwoSL, fuchsianCuspSL, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- The projective action of real special-linear matrices on the upper half-plane. -/
@[expose] public noncomputable def fuchsianSLAction : SL2R →* Equiv.Perm UpperHalfPlane :=
  (MulAction.toPermHom (GL (Fin 2) ℝ) UpperHalfPlane).comp
    (Matrix.SpecialLinearGroup.mapGL ℝ)

@[expose] public noncomputable def fuchsianOnePerm : Equiv.Perm UpperHalfPlane :=
  fuchsianSLAction fuchsianOneSL

@[expose] public noncomputable def fuchsianTwoPerm : Equiv.Perm UpperHalfPlane :=
  fuchsianSLAction fuchsianTwoSL

@[expose] public noncomputable def fuchsianCuspPerm : Equiv.Perm UpperHalfPlane :=
  fuchsianSLAction fuchsianCuspSL

public theorem fuchsianOnePerm_pow_three : fuchsianOnePerm ^ 3 = 1 := by
  rw [show fuchsianOnePerm ^ 3 = fuchsianSLAction (fuchsianOneSL ^ 3) by
    exact (map_pow _ _ _).symm]
  rw [fuchsianOneSL_pow_three, map_one]

public theorem fuchsianTwoPerm_pow_four : fuchsianTwoPerm ^ 4 = 1 := by
  rw [show fuchsianTwoPerm ^ 4 = fuchsianSLAction (fuchsianTwoSL ^ 4) by
    exact (map_pow _ _ _).symm]
  rw [fuchsianTwoSL_pow_four]
  apply Equiv.ext
  intro z
  change (Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL2R)) • z = z
  apply UpperHalfPlane.coe_injective
  rw [UpperHalfPlane.coe_smul_of_det_pos]
  · simp [UpperHalfPlane.num, UpperHalfPlane.denom]
  · norm_num

public theorem fuchsianOnePerm_mul_fuchsianTwoPerm_mul_fuchsianCuspPerm :
    fuchsianOnePerm * fuchsianTwoPerm * fuchsianCuspPerm = 1 := by
  change fuchsianSLAction fuchsianOneSL * fuchsianSLAction fuchsianTwoSL *
    fuchsianSLAction fuchsianCuspSL = 1
  rw [← map_mul, ← map_mul,
    fuchsianOneSL_mul_fuchsianTwoSL_mul_fuchsianCuspSL, map_one]

/-- The genuine source action of `Delta(3, 4, ∞)` on its upper half-plane. -/
@[expose] public noncomputable def fuchsianSourceAction : Delta →* Equiv.Perm UpperHalfPlane :=
  Monoid.Coprod.lift
    (cyclicRepresentation 3 fuchsianOnePerm fuchsianOnePerm_pow_three)
    (cyclicRepresentation 4 fuchsianTwoPerm fuchsianTwoPerm_pow_four)

@[simp]
public theorem fuchsianSourceAction_g₁ : fuchsianSourceAction g₁ = fuchsianOnePerm := by
  rw [gOne_eq]
  simp [fuchsianSourceAction.eq_def]

@[simp]
public theorem fuchsianSourceAction_g₂ : fuchsianSourceAction g₂ = fuchsianTwoPerm := by
  rw [gTwo_eq]
  simp [fuchsianSourceAction.eq_def]

@[simp]
public theorem fuchsianSourceAction_g₀ : fuchsianSourceAction g₀ = fuchsianCuspPerm := by
  rw [gCusp_eq, map_inv, map_mul,
    fuchsianSourceAction_g₁, fuchsianSourceAction_g₂]
  exact inv_eq_of_mul_eq_one_right
    fuchsianOnePerm_mul_fuchsianTwoPerm_mul_fuchsianCuspPerm

public theorem fuchsianOneGL_matrix :
    (fuchsianOneGL : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, 1; -1, 0] := by
  change (((Matrix.SpecialLinearGroup.mapGL ℝ) fuchsianOneSL : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ) = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

public theorem fuchsianTwoGL_matrix :
    (fuchsianTwoGL : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, Real.sqrt 2] := by
  change (((Matrix.SpecialLinearGroup.mapGL ℝ) fuchsianTwoSL : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ) = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

public theorem fuchsianCuspGL_matrix :
    (fuchsianCuspGL : Matrix (Fin 2) (Fin 2) ℝ) = !![1, -(1 + Real.sqrt 2); 0, 1] := by
  change (((Matrix.SpecialLinearGroup.mapGL ℝ) fuchsianCuspSL : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ) = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

public theorem fuchsianProductGL_matrix :
    (fuchsianProductGL : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, 1 + Real.sqrt 2; 0, 1] := by
  change (((Matrix.SpecialLinearGroup.mapGL ℝ) fuchsianProductSL : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ) = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

public theorem fuchsianTwoSquaredGL_matrix :
    (fuchsianTwoSquaredGL : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-1, -Real.sqrt 2; Real.sqrt 2, 1] := by
  change (((Matrix.SpecialLinearGroup.mapGL ℝ) fuchsianTwoSquaredSL : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ) = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

public theorem fuchsianSourceAction_g₁_apply (z : UpperHalfPlane) :
    (((fuchsianSourceAction g₁) z : UpperHalfPlane) : ℂ) = (z - 1) / z := by
  rw [fuchsianSourceAction_g₁]
  change (((fuchsianOneGL • z : UpperHalfPlane) : ℂ)) = _
  rw [UpperHalfPlane.coe_smul_of_det_pos]
  · simp [UpperHalfPlane.num, UpperHalfPlane.denom, fuchsianOneGL_matrix]
    field_simp [z.ne_zero]
    ring
  · simp [fuchsianOneGL.eq_def]

public theorem fuchsianSourceAction_g₂_apply (z : UpperHalfPlane) :
    (((fuchsianSourceAction g₂) z : UpperHalfPlane) : ℂ) =
      -1 / (z + Real.sqrt 2) := by
  rw [fuchsianSourceAction_g₂]
  change (((fuchsianTwoGL • z : UpperHalfPlane) : ℂ)) = _
  rw [UpperHalfPlane.coe_smul_of_det_pos]
  · simp [UpperHalfPlane.num, UpperHalfPlane.denom, fuchsianTwoGL_matrix]
  · simp [fuchsianTwoGL.eq_def]

public theorem fuchsianOnePerm_apply (z : UpperHalfPlane) :
    ((fuchsianOnePerm z : UpperHalfPlane) : ℂ) = (z - 1) / z := by
  rw [← fuchsianSourceAction_g₁]
  exact fuchsianSourceAction_g₁_apply z

public theorem fuchsianTwoPerm_apply (z : UpperHalfPlane) :
    ((fuchsianTwoPerm z : UpperHalfPlane) : ℂ) = -1 / (z + Real.sqrt 2) := by
  rw [← fuchsianSourceAction_g₂]
  exact fuchsianSourceAction_g₂_apply z

public theorem fuchsianOnePerm_ne_one : fuchsianOnePerm ≠ 1 := by
  intro h
  have hz := congrArg (fun e : Equiv.Perm UpperHalfPlane ↦ e UpperHalfPlane.I) h
  have hc := congrArg (fun z : UpperHalfPlane ↦ (z : ℂ)) hz
  rw [fuchsianOnePerm_apply] at hc
  norm_num [UpperHalfPlane.I] at hc
  have hr := congrArg Complex.re hc
  norm_num at hr

public theorem fuchsianTwoPerm_sq_ne_one : fuchsianTwoPerm ^ 2 ≠ 1 := by
  intro h
  have hz := congrArg (fun e : Equiv.Perm UpperHalfPlane ↦ e UpperHalfPlane.I) h
  have hpow : fuchsianTwoPerm ^ 2 = fuchsianSLAction (fuchsianTwoSL ^ 2) := by
    exact (map_pow _ _ _).symm
  rw [hpow, fuchsianTwoSL_pow_two] at hz
  have hc := congrArg (fun z : UpperHalfPlane ↦ (z : ℂ)) hz
  change ((fuchsianTwoSquaredGL • UpperHalfPlane.I : UpperHalfPlane) : ℂ) =
    UpperHalfPlane.I at hc
  rw [UpperHalfPlane.coe_smul_of_det_pos] at hc
  · simp [UpperHalfPlane.num, UpperHalfPlane.denom, UpperHalfPlane.I,
      fuchsianTwoSquaredGL_matrix] at hc
    have hden : Complex.I * (Real.sqrt 2 : ℂ) + 1 ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      norm_num at him
    field_simp [hden] at hc
    have him := congrArg Complex.im hc
    norm_num at him
  · simp [fuchsianTwoSquaredGL.eq_def]

public theorem orderOf_fuchsianOnePerm : orderOf fuchsianOnePerm = 3 :=
  orderOf_eq_prime fuchsianOnePerm_pow_three fuchsianOnePerm_ne_one

public theorem orderOf_fuchsianTwoPerm : orderOf fuchsianTwoPerm = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1)
    fuchsianTwoPerm_sq_ne_one fuchsianTwoPerm_pow_four
  exact h

/-- The order-three elliptic fixed point of the source action. -/
@[expose] public noncomputable def fuchsianOneFixedPoint : UpperHalfPlane :=
  ⟨⟨1 / 2, Real.sqrt 3 / 2⟩, by positivity⟩

/-- The order-four elliptic fixed point of the source action. -/
@[expose] public noncomputable def fuchsianTwoFixedPoint : UpperHalfPlane :=
  ⟨⟨-Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩, by positivity⟩

public theorem fuchsianOneFixedPoint_fixed :
    fuchsianSourceAction g₁ • fuchsianOneFixedPoint = fuchsianOneFixedPoint := by
  apply UpperHalfPlane.coe_injective
  change (((fuchsianSourceAction g₁) fuchsianOneFixedPoint : UpperHalfPlane) : ℂ) =
    fuchsianOneFixedPoint
  rw [fuchsianSourceAction_g₁_apply]
  change ((⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) - 1) /
      ⟨1 / 2, Real.sqrt 3 / 2⟩ = ⟨1 / 2, Real.sqrt 3 / 2⟩
  have hz : (⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  apply (div_eq_iff hz).2
  apply Complex.ext <;>
    norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
  all_goals ring

public theorem fuchsianTwoFixedPoint_fixed :
    fuchsianSourceAction g₂ • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint := by
  apply UpperHalfPlane.coe_injective
  change (((fuchsianSourceAction g₂) fuchsianTwoFixedPoint : UpperHalfPlane) : ℂ) =
    fuchsianTwoFixedPoint
  rw [fuchsianSourceAction_g₂_apply]
  change -1 / ((⟨-Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩ : ℂ) + Real.sqrt 2) =
    ⟨-Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩
  have hz : (⟨-Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩ : ℂ) + Real.sqrt 2 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  apply (div_eq_iff hz).2
  apply Complex.ext <;>
    norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  all_goals ring

public theorem fuchsianProductPerm_apply (z : UpperHalfPlane) :
    (((fuchsianOnePerm * fuchsianTwoPerm) z : UpperHalfPlane) : ℂ) =
      z + (1 + Real.sqrt 2) := by
  change (((fuchsianSLAction fuchsianOneSL * fuchsianSLAction fuchsianTwoSL) z :
    UpperHalfPlane) : ℂ) = _
  rw [← map_mul, fuchsianOneSL_mul_fuchsianTwoSL]
  change (((fuchsianProductGL • z : UpperHalfPlane) : ℂ)) = _
  rw [UpperHalfPlane.coe_smul_of_det_pos]
  · simp [UpperHalfPlane.num, UpperHalfPlane.denom, fuchsianProductGL_matrix]
  · simp [fuchsianProductGL.eq_def]

public theorem fuchsianSourceAction_g₀_apply (z : UpperHalfPlane) :
    (((fuchsianSourceAction g₀) z : UpperHalfPlane) : ℂ) =
      z - (1 + Real.sqrt 2) := by
  rw [fuchsianSourceAction_g₀]
  change (((fuchsianCuspGL • z : UpperHalfPlane) : ℂ)) = _
  rw [UpperHalfPlane.coe_smul_of_det_pos]
  · simp [UpperHalfPlane.num, UpperHalfPlane.denom, fuchsianCuspGL_matrix]
    ring
  · simp [fuchsianCuspGL.eq_def]

/-- A standard horodisc based at the parabolic fixed point `∞`. -/
@[expose] public def fuchsianCuspRegion : Set UpperHalfPlane :=
  {z | 1 ≤ z.im}

public theorem fuchsianCuspRegion_nonempty : fuchsianCuspRegion.Nonempty := by
  refine ⟨UpperHalfPlane.I, ?_⟩
  change (1 : ℝ) ≤ 1
  norm_num

public theorem fuchsianSourceAction_g₀_im (z : UpperHalfPlane) :
    ((fuchsianSourceAction g₀) z).im = z.im := by
  have h := congrArg Complex.im (fuchsianSourceAction_g₀_apply z)
  simpa using h

public theorem fuchsianCuspRegion_invariant (z : UpperHalfPlane) :
    (fuchsianSourceAction g₀) z ∈ fuchsianCuspRegion ↔ z ∈ fuchsianCuspRegion := by
  change 1 ≤ ((fuchsianSourceAction g₀) z).im ↔ 1 ≤ z.im
  rw [fuchsianSourceAction_g₀_im]

end SphereSixComplex.TriangleGroup
