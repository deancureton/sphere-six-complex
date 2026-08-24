module

public import SphereSixComplex.Geometry.EllipticLocalCoordinates
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# The Cayley homeomorphism at an elliptic point

The Cayley coordinate centered at any point of the upper half-plane is identified explicitly with
a homeomorphism onto the open complex unit disc.  This supplies the actual local base chart used by
the elliptic filling construction.
-/

namespace SphereSixComplex.Geometry.EllipticCayleyHomeomorph

open Complex SphereSixComplex.Geometry.EllipticLocalCoordinates
open scoped ComplexConjugate Manifold

noncomputable section

/-- The inverse fractional-linear expression for the Cayley coordinate centered at `a`. -/
@[expose] public noncomputable def cayleyInverse
    (a : UpperHalfPlane) (w : ComplexUnitDisc) : ℂ :=
  ((a : ℂ) - w.1 * conj (a : ℂ)) / (1 - w.1)

private theorem one_sub_disc_ne_zero (w : ComplexUnitDisc) : (1 : ℂ) - w.1 ≠ 0 := by
  intro h
  have hw : w.1 = 1 := (sub_eq_zero.mp h).symm
  have := w.2
  rw [hw] at this
  norm_num at this

public theorem cayleyInverse_im (a : UpperHalfPlane) (w : ComplexUnitDisc) :
    (cayleyInverse a w).im =
      a.im * (1 - Complex.normSq w.1) / Complex.normSq (1 - w.1) := by
  simp only [cayleyInverse, Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring_nf
  ac_rfl

public theorem cayleyInverse_im_pos (a : UpperHalfPlane) (w : ComplexUnitDisc) :
    0 < (cayleyInverse a w).im := by
  rw [cayleyInverse_im]
  have hnorm : ‖w.1‖ ^ 2 < 1 := by nlinarith [norm_nonneg w.1, w.2]
  have hsq : Complex.normSq w.1 < 1 := by
    simpa [Complex.sq_norm] using hnorm
  have hden : 0 < Complex.normSq (1 - w.1) :=
    Complex.normSq_pos.mpr (one_sub_disc_ne_zero w)
  positivity

/-- The inverse Cayley coordinate, valued in the upper half-plane. -/
@[expose] public noncomputable def cayleyInverseUpper
    (a : UpperHalfPlane) (w : ComplexUnitDisc) : UpperHalfPlane :=
  ⟨cayleyInverse a w, cayleyInverse_im_pos a w⟩

public theorem cayleyInverse_cayley (a z : UpperHalfPlane) :
    cayleyInverseUpper a (cayleyDiscCoordinate a z) = z := by
  apply UpperHalfPlane.ext
  change (((a : ℂ) - cayleyCoordinate a z * conj (a : ℂ)) /
      (1 - cayleyCoordinate a z)) = (z : ℂ)
  unfold cayleyCoordinate
  have hd : (z : ℂ) - conj (a : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im] at him
    have hpos : 0 < z.im + a.im := add_pos z.im_pos a.im_pos
    norm_num at him
    linarith
  have ha : (a : ℂ) - conj (a : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im] at him
    norm_num at him
    linarith [a.im_pos]
  field_simp [hd, ha]
  ring

public theorem cayley_cayleyInverse (a : UpperHalfPlane) (w : ComplexUnitDisc) :
    cayleyDiscCoordinate a (cayleyInverseUpper a w) = w := by
  apply Subtype.ext
  change ((((cayleyInverse a w) - (a : ℂ)) /
      ((cayleyInverse a w) - conj (a : ℂ)))) = w.1
  have hd : (1 : ℂ) - w.1 ≠ 0 := one_sub_disc_ne_zero w
  have ha : (a : ℂ) - conj (a : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im] at him
    norm_num at him
    linarith [a.im_pos]
  have hnum : cayleyInverse a w - (a : ℂ) =
      w.1 * ((a : ℂ) - conj (a : ℂ)) / (1 - w.1) := by
    unfold cayleyInverse
    field_simp [hd]
    ring
  have hden : cayleyInverse a w - conj (a : ℂ) =
      ((a : ℂ) - conj (a : ℂ)) / (1 - w.1) := by
    unfold cayleyInverse
    field_simp [hd]
    ring
  rw [hnum, hden]
  field_simp [hd, ha]

public theorem continuous_cayleyDiscCoordinate (a : UpperHalfPlane) :
    Continuous (cayleyDiscCoordinate a) := by
  unfold cayleyDiscCoordinate cayleyCoordinate
  apply Continuous.subtype_mk
  exact (UpperHalfPlane.continuous_coe.sub continuous_const).div
    (UpperHalfPlane.continuous_coe.sub continuous_const) (fun z ↦ by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.conj_im] at him
      norm_num at him
      linarith [z.im_pos, a.im_pos])

public theorem cayleyCoordinate_mdifferentiable (a : UpperHalfPlane) :
    MDiff (cayleyCoordinate a) := by
  intro z
  unfold cayleyCoordinate
  exact (z.mdifferentiable_coe.sub mdifferentiableAt_const).div
    (z.mdifferentiable_coe.sub mdifferentiableAt_const) (by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.conj_im] at him
      norm_num at him
      linarith [z.im_pos, a.im_pos])

public theorem continuous_cayleyInverseUpper (a : UpperHalfPlane) :
    Continuous (cayleyInverseUpper a) := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun w : ComplexUnitDisc ↦
    ((a : ℂ) - w.1 * conj (a : ℂ)) / (1 - w.1))
  exact (continuous_const.sub (continuous_subtype_val.mul continuous_const)).div
    (continuous_const.sub continuous_subtype_val) (fun w ↦ one_sub_disc_ne_zero w)

/-- The Cayley coordinate centered at `a` as a homeomorphism from the upper half-plane to the open
unit disc. -/
@[expose] public noncomputable def cayleyHomeomorph
    (a : UpperHalfPlane) : UpperHalfPlane ≃ₜ ComplexUnitDisc where
  toFun := cayleyDiscCoordinate a
  invFun := cayleyInverseUpper a
  left_inv := cayleyInverse_cayley a
  right_inv := cayley_cayleyInverse a
  continuous_toFun := continuous_cayleyDiscCoordinate a
  continuous_invFun := continuous_cayleyInverseUpper a

/-- The order-three elliptic base chart. -/
@[expose] public noncomputable def orderThreeCayleyHomeomorph :
    UpperHalfPlane ≃ₜ ComplexUnitDisc :=
  cayleyHomeomorph SphereSixComplex.TriangleGroup.fuchsianOneFixedPoint

/-- The order-four elliptic base chart. -/
@[expose] public noncomputable def orderFourCayleyHomeomorph :
    UpperHalfPlane ≃ₜ ComplexUnitDisc :=
  cayleyHomeomorph SphereSixComplex.TriangleGroup.fuchsianTwoFixedPoint

public theorem orderThreeCayleyHomeomorph_generator (z : UpperHalfPlane) :
    orderThreeCayleyHomeomorph
        (SphereSixComplex.TriangleGroup.fuchsianSourceAction
          SphereSixComplex.TriangleGroup.g₁ • z) =
      orderThreeDiscRotation (orderThreeCayleyHomeomorph z) := by
  apply Subtype.ext
  exact orderThreeCayley_generator z

public theorem orderFourCayleyHomeomorph_generator (z : UpperHalfPlane) :
    orderFourCayleyHomeomorph
        (SphereSixComplex.TriangleGroup.fuchsianSourceAction
          SphereSixComplex.TriangleGroup.g₂ • z) =
      orderFourDiscRotation (orderFourCayleyHomeomorph z) := by
  apply Subtype.ext
  exact orderFourCayley_generator z

end

end SphereSixComplex.Geometry.EllipticCayleyHomeomorph
