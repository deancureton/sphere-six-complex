module

public import SphereSixComplex.Periods.FuchsianModularParameterExistence
import all SphereSixComplex.Periods.FuchsianModularParameterExistence

@[expose] public section

open Complex UpperHalfPlane

noncomputable section

namespace SphereSixComplex.Periods.TriangleReflections

open SphereSixComplex.TriangleGroup

/-! The three antiholomorphic side reflections for the source and modular triangles. -/

def sourceRight (z : ℂ) : ℂ := 1 - starRingEnd ℂ z

def sourceCircle (z : ℂ) : ℂ := (starRingEnd ℂ z)⁻¹

def sourceLeft (z : ℂ) : ℂ := -Real.sqrt 2 - starRingEnd ℂ z

def targetRight (z : ℂ) : ℂ := 1 - starRingEnd ℂ z

def targetCircle (z : ℂ) : ℂ := (starRingEnd ℂ z)⁻¹

def targetLeft (z : ℂ) : ℂ := -starRingEnd ℂ z

@[simp] theorem sourceRight_im (z : ℂ) : (sourceRight z).im = z.im := by
  simp [sourceRight]

@[simp] theorem sourceLeft_im (z : ℂ) : (sourceLeft z).im = z.im := by
  simp [sourceLeft]

@[simp] theorem targetRight_im (z : ℂ) : (targetRight z).im = z.im := by
  simp [targetRight]

@[simp] theorem targetLeft_im (z : ℂ) : (targetLeft z).im = z.im := by
  simp [targetLeft]

theorem sourceCircle_im (z : ℂ) : (sourceCircle z).im = z.im / normSq z := by
  rw [sourceCircle, inv_im]
  simp [normSq_conj]

theorem targetCircle_im (z : ℂ) : (targetCircle z).im = z.im / normSq z :=
  sourceCircle_im z

def sourceRightUHP : Equiv.Perm UpperHalfPlane where
  toFun z := ⟨sourceRight z, by simpa using z.im_pos⟩
  invFun z := ⟨sourceRight z, by simpa using z.im_pos⟩
  left_inv z := by
    apply UpperHalfPlane.coe_injective
    simp [sourceRight]
  right_inv z := by
    apply UpperHalfPlane.coe_injective
    simp [sourceRight]

def sourceCircleUHP : Equiv.Perm UpperHalfPlane where
  toFun z := ⟨sourceCircle z, by
    rw [sourceCircle_im]
    exact div_pos z.im_pos z.normSq_pos⟩
  invFun z := ⟨sourceCircle z, by
    rw [sourceCircle_im]
    exact div_pos z.im_pos z.normSq_pos⟩
  left_inv z := by
    apply UpperHalfPlane.coe_injective
    change (starRingEnd ℂ ((starRingEnd ℂ (z : ℂ))⁻¹))⁻¹ = z
    rw [map_inv₀, starRingEnd_self_apply, inv_inv]
  right_inv z := by
    apply UpperHalfPlane.coe_injective
    change (starRingEnd ℂ ((starRingEnd ℂ (z : ℂ))⁻¹))⁻¹ = z
    rw [map_inv₀, starRingEnd_self_apply, inv_inv]

def sourceLeftUHP : Equiv.Perm UpperHalfPlane where
  toFun z := ⟨sourceLeft z, by simpa using z.im_pos⟩
  invFun z := ⟨sourceLeft z, by simpa using z.im_pos⟩
  left_inv z := by
    apply UpperHalfPlane.coe_injective
    simp [sourceLeft]
  right_inv z := by
    apply UpperHalfPlane.coe_injective
    simp [sourceLeft]

def targetRightUHP : Equiv.Perm UpperHalfPlane := sourceRightUHP

def targetCircleUHP : Equiv.Perm UpperHalfPlane := sourceCircleUHP

def targetLeftUHP : Equiv.Perm UpperHalfPlane where
  toFun z := ⟨targetLeft z, by simpa using z.im_pos⟩
  invFun z := ⟨targetLeft z, by simpa using z.im_pos⟩
  left_inv z := by
    apply UpperHalfPlane.coe_injective
    simp [targetLeft]
  right_inv z := by
    apply UpperHalfPlane.coe_injective
    simp [targetLeft]

@[simp] theorem coe_sourceRightUHP (z : UpperHalfPlane) :
    (sourceRightUHP z : ℂ) = sourceRight z := rfl

@[simp] theorem coe_sourceCircleUHP (z : UpperHalfPlane) :
    (sourceCircleUHP z : ℂ) = sourceCircle z := rfl

@[simp] theorem coe_sourceLeftUHP (z : UpperHalfPlane) :
    (sourceLeftUHP z : ℂ) = sourceLeft z := rfl

@[simp] theorem coe_targetRightUHP (z : UpperHalfPlane) :
    (targetRightUHP z : ℂ) = targetRight z := rfl

@[simp] theorem coe_targetCircleUHP (z : UpperHalfPlane) :
    (targetCircleUHP z : ℂ) = targetCircle z := rfl

@[simp] theorem coe_targetLeftUHP (z : UpperHalfPlane) :
    (targetLeftUHP z : ℂ) = targetLeft z := rfl

/-- The order-three source generator is the product of the right and circular reflections. -/
theorem sourceRight_sourceCircle (z : UpperHalfPlane) :
  sourceRightUHP (sourceCircleUHP z) = fuchsianSourceAction g₁ • z := by
  apply UpperHalfPlane.coe_injective
  change sourceRight (sourceCircle z) =
    (((fuchsianSourceAction g₁) z : UpperHalfPlane) : ℂ)
  rw [fuchsianSourceAction_g₁_apply]
  change 1 - starRingEnd ℂ ((starRingEnd ℂ (z : ℂ))⁻¹) = ((z : ℂ) - 1) / z
  rw [map_inv₀, starRingEnd_self_apply]
  field_simp [z.ne_zero]

/-- The order-four source generator is the product of the circular and left reflections. -/
theorem sourceCircle_sourceLeft (z : UpperHalfPlane) :
  sourceCircleUHP (sourceLeftUHP z) = fuchsianSourceAction g₂ • z := by
  apply UpperHalfPlane.coe_injective
  change sourceCircle (sourceLeft z) =
    (((fuchsianSourceAction g₂) z : UpperHalfPlane) : ℂ)
  rw [fuchsianSourceAction_g₂_apply]
  change (starRingEnd ℂ (-Real.sqrt 2 - starRingEnd ℂ (z : ℂ)))⁻¹ =
    -1 / ((z : ℂ) + Real.sqrt 2)
  have hsqrt : starRingEnd ℂ (Real.sqrt 2 : ℂ) = Real.sqrt 2 := by
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  rw [map_sub, map_neg, hsqrt, starRingEnd_self_apply]
  rw [show -(Real.sqrt 2 : ℂ) - (z : ℂ) =
    -((Real.sqrt 2 : ℂ) + z) by ring, inv_neg]
  simp only [div_eq_mul_inv, neg_mul, one_mul, add_comm]

/-- The modular order-three generator is the analogous product of target reflections. -/
theorem targetRight_targetCircle (z : UpperHalfPlane) :
    targetRightUHP (targetCircleUHP z) = rhoTauReal g₁ • z := by
  apply UpperHalfPlane.coe_injective
  rw [rhoTauReal_g1_smul]
  change 1 - starRingEnd ℂ ((starRingEnd ℂ (z : ℂ))⁻¹) = ((z : ℂ) - 1) / z
  rw [map_inv₀, starRingEnd_self_apply]
  field_simp [z.ne_zero]

/-- The modular order-two generator is the product of the circular and imaginary-axis
reflections. -/
theorem targetCircle_targetLeft (z : UpperHalfPlane) :
    targetCircleUHP (targetLeftUHP z) = rhoTauReal g₂ • z := by
  apply UpperHalfPlane.coe_injective
  rw [rhoTauReal_g2_smul]
  change (starRingEnd ℂ (-starRingEnd ℂ (z : ℂ)))⁻¹ = -1 / (z : ℂ)
  rw [map_neg, starRingEnd_self_apply]
  ring


end SphereSixComplex.Periods.TriangleReflections
