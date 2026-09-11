module

public import SphereSixComplex.Prerequisites.Periods.FuchsianModularParameterExistence
import all SphereSixComplex.Prerequisites.Periods.FuchsianModularParameterExistence

@[expose] public section

open Complex UpperHalfPlane

noncomputable section

namespace SphereSixComplex.Periods.TriangleReflections

open SphereSixComplex.TriangleGroup

/-! The three antiholomorphic side reflections for the source and modular triangles. -/

def sourceRight (z : ℂ) : ℂ := 1 - starRingEnd ℂ z

def sourceCircle (z : ℂ) : ℂ := (starRingEnd ℂ z)⁻¹

def sourceLeft (z : ℂ) : ℂ := -Real.sqrt 2 - starRingEnd ℂ z




@[simp] theorem sourceRight_im (z : ℂ) : (sourceRight z).im = z.im := by
  simp [sourceRight]

@[simp] theorem sourceLeft_im (z : ℂ) : (sourceLeft z).im = z.im := by
  simp [sourceLeft]



theorem sourceCircle_im (z : ℂ) : (sourceCircle z).im = z.im / normSq z := by
  rw [sourceCircle, inv_im]
  simp [normSq_conj]


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










@[simp] theorem coe_sourceRightUHP (z : UpperHalfPlane) :
    (sourceRightUHP z : ℂ) = sourceRight z := rfl

@[simp] theorem coe_sourceCircleUHP (z : UpperHalfPlane) :
    (sourceCircleUHP z : ℂ) = sourceCircle z := rfl

@[simp] theorem coe_sourceLeftUHP (z : UpperHalfPlane) :
    (sourceLeftUHP z : ℂ) = sourceLeft z := rfl

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




end SphereSixComplex.Periods.TriangleReflections
