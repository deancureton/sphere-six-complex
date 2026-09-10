module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Tactic

namespace SphereSixComplex.Geometry.EllipticLocalCoordinates

open Complex
open scoped ComplexConjugate

noncomputable section

/-- The open complex unit disc as a type. -/
public abbrev ComplexUnitDisc := {w : ℂ // ‖w‖ < 1}

/-- Cayley coordinate centered at a point of the upper half-plane. -/
@[expose] public noncomputable def cayleyCoordinate
    (a z : UpperHalfPlane) : ℂ :=
  ((z : ℂ) - a) / ((z : ℂ) - conj (a : ℂ))

private theorem cayley_denominator_ne_zero (a z : UpperHalfPlane) :
    (z : ℂ) - conj (a : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im] at him
  norm_num at him
  have hpos : 0 < (z : ℂ).im + (a : ℂ).im := add_pos z.im_pos a.im_pos
  change 0 < z.im + a.im at hpos
  linarith

private theorem norm_sub_lt_norm_sub_conj (a z : UpperHalfPlane) :
    ‖(z : ℂ) - a‖ < ‖(z : ℂ) - conj (a : ℂ)‖ := by
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im]
  have hprod : 0 < (z : ℂ).im * (a : ℂ).im := mul_pos z.im_pos a.im_pos
  ring_nf
  linarith

public theorem norm_cayleyCoordinate_lt_one (a z : UpperHalfPlane) :
    ‖cayleyCoordinate a z‖ < 1 := by
  rw [cayleyCoordinate, norm_div, div_lt_one (norm_pos_iff.mpr
    (cayley_denominator_ne_zero a z))]
  exact norm_sub_lt_norm_sub_conj a z

/-- The Cayley coordinate valued in the open unit disc. -/
@[expose] public noncomputable def cayleyDiscCoordinate
    (a : UpperHalfPlane) (z : UpperHalfPlane) : ComplexUnitDisc :=
  ⟨cayleyCoordinate a z, norm_cayleyCoordinate_lt_one a z⟩

@[simp]
public theorem cayleyCoordinate_center (a : UpperHalfPlane) :
    cayleyCoordinate a a = 0 := by
  simp [cayleyCoordinate]

/-- Multiplication by a unit complex scalar as a permutation of the open unit disc. -/
@[expose] public noncomputable def discScalarEquiv (lambda : ℂ) (hlambda : ‖lambda‖ = 1) :
    Equiv.Perm ComplexUnitDisc where
  toFun w := ⟨lambda * w.1, by simpa [norm_mul, hlambda] using w.2⟩
  invFun w := ⟨lambda⁻¹ * w.1, by
    have hnorm : ‖lambda⁻¹‖ = 1 := by simp [hlambda]
    simpa [norm_mul, hnorm] using w.2⟩
  left_inv w := by
    apply Subtype.ext
    change lambda⁻¹ * (lambda * w.1) = w.1
    rw [← mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mp (by simp [hlambda])), one_mul]
  right_inv w := by
    apply Subtype.ext
    change lambda * (lambda⁻¹ * w.1) = w.1
    rw [← mul_assoc, mul_inv_cancel₀ (norm_pos_iff.mp (by simp [hlambda])), one_mul]

@[simp]
public theorem discScalarEquiv_apply_val (lambda : ℂ) (hlambda : ‖lambda‖ = 1)
    (w : ComplexUnitDisc) :
    (discScalarEquiv lambda hlambda w).1 = lambda * w.1 := rfl

public theorem discScalarEquiv_pow_apply_val (lambda : ℂ) (hlambda : ‖lambda‖ = 1)
    (k : ℕ) (w : ComplexUnitDisc) :
    ((discScalarEquiv lambda hlambda ^ k) w).1 = lambda ^ k * w.1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, discScalarEquiv_apply_val, ih]
      rw [pow_succ']
      ring

public theorem discScalarEquiv_pow_eq_one (lambda : ℂ) (hlambda : ‖lambda‖ = 1)
    (m : ℕ) (hm : lambda ^ m = 1) :
    discScalarEquiv lambda hlambda ^ m = 1 := by
  apply Equiv.ext
  intro w
  apply Subtype.ext
  rw [discScalarEquiv_pow_apply_val, hm]
  simp

@[expose] public def discCenter : ComplexUnitDisc := ⟨0, by norm_num⟩

public theorem discScalarEquiv_pow_fixed_iff (lambda : ℂ) (hlambda : ‖lambda‖ = 1)
    (k : ℕ) (hk : lambda ^ k ≠ 1) (w : ComplexUnitDisc) :
    (discScalarEquiv lambda hlambda ^ k) w = w ↔ w = discCenter := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    rw [discScalarEquiv_pow_apply_val] at hv
    apply Subtype.ext
    change w.1 = 0
    have hmul : (lambda ^ k - 1) * w.1 = 0 := by
      rw [sub_mul, one_mul, hv, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hk)
  · rintro rfl
    apply Subtype.ext
    simp [discScalarEquiv_pow_apply_val, discCenter]

end

end SphereSixComplex.Geometry.EllipticLocalCoordinates
