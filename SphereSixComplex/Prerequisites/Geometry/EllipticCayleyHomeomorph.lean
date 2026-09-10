module

public import SphereSixComplex.Prerequisites.Geometry.FuchsianEllipticCoordinates
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The Cayley homeomorphism at an elliptic point

The Cayley coordinate centered at any point of the upper half-plane is identified explicitly with
a homeomorphism onto the open complex unit disc.  This supplies the actual local base chart used by
the elliptic filling construction.
-/

namespace SphereSixComplex

open Complex SphereSixComplex.Geometry.EllipticLocalCoordinates
open scoped ComplexConjugate Manifold

noncomputable section

private theorem ComplexUnitDisc.one_sub_coe_ne_zero (w : ComplexUnitDisc) : (1 : ℂ) - w.1 ≠ 0 := by
  intro h
  have hw : w.1 = 1 := (sub_eq_zero.mp h).symm
  have := w.2
  rw [hw] at this
  norm_num at this

namespace UpperHalfPlane

/-- The inverse fractional-linear expression for the Cayley coordinate centered at `a`. -/
@[expose] public noncomputable def cayleyInv
    (a : _root_.UpperHalfPlane) (w : ComplexUnitDisc) : ℂ :=
  ((a : ℂ) - w.1 * conj (a : ℂ)) / (1 - w.1)

public theorem cayleyInv_im (a : _root_.UpperHalfPlane) (w : ComplexUnitDisc) :
    (cayleyInv a w).im =
      a.im * (1 - Complex.normSq w.1) / Complex.normSq (1 - w.1) := by
  simp only [cayleyInv, Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring_nf
  ac_rfl

public theorem cayleyInv_im_pos (a : _root_.UpperHalfPlane) (w : ComplexUnitDisc) :
    0 < (cayleyInv a w).im := by
  rw [cayleyInv_im]
  have hnorm : ‖w.1‖ ^ 2 < 1 := by nlinarith [norm_nonneg w.1, w.2]
  have hsq : Complex.normSq w.1 < 1 := by
    simpa [Complex.sq_norm] using hnorm
  have hden : 0 < Complex.normSq (1 - w.1) :=
    Complex.normSq_pos.mpr (ComplexUnitDisc.one_sub_coe_ne_zero w)
  positivity

/-- The inverse Cayley coordinate, valued in the upper half-plane. -/
@[expose] public noncomputable def cayleyFromDisc
    (a : _root_.UpperHalfPlane) (w : ComplexUnitDisc) : _root_.UpperHalfPlane :=
  ⟨cayleyInv a w, cayleyInv_im_pos a w⟩

public theorem cayleyFromDisc_cayleyToDisc (a z : _root_.UpperHalfPlane) :
    cayleyFromDisc a (cayleyToDisc a z) = z := by
  apply _root_.UpperHalfPlane.ext
  change (((a : ℂ) - cayley a z * conj (a : ℂ)) /
      (1 - cayley a z)) = (z : ℂ)
  unfold cayley
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

public theorem cayleyToDisc_cayleyFromDisc (a : _root_.UpperHalfPlane) (w : ComplexUnitDisc) :
    cayleyToDisc a (cayleyFromDisc a w) = w := by
  apply Subtype.ext
  change ((((cayleyInv a w) - (a : ℂ)) /
      ((cayleyInv a w) - conj (a : ℂ)))) = w.1
  have hd : (1 : ℂ) - w.1 ≠ 0 := ComplexUnitDisc.one_sub_coe_ne_zero w
  have ha : (a : ℂ) - conj (a : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im] at him
    norm_num at him
    linarith [a.im_pos]
  have hnum : cayleyInv a w - (a : ℂ) =
      w.1 * ((a : ℂ) - conj (a : ℂ)) / (1 - w.1) := by
    unfold cayleyInv
    field_simp [hd]
    ring
  have hden : cayleyInv a w - conj (a : ℂ) =
      ((a : ℂ) - conj (a : ℂ)) / (1 - w.1) := by
    unfold cayleyInv
    field_simp [hd]
    ring
  rw [hnum, hden]
  field_simp [hd, ha]

public theorem continuous_cayleyToDisc (a : _root_.UpperHalfPlane) :
    Continuous (cayleyToDisc a) := by
  unfold cayleyToDisc cayley
  apply Continuous.subtype_mk
  exact (_root_.UpperHalfPlane.continuous_coe.sub continuous_const).div
    (_root_.UpperHalfPlane.continuous_coe.sub continuous_const) (fun z ↦ by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.conj_im] at him
      norm_num at him
      linarith [z.im_pos, a.im_pos])

public theorem mdifferentiable_cayley (a : _root_.UpperHalfPlane) :
    MDiff (cayley a) := by
  intro z
  unfold cayley
  exact (z.mdifferentiable_coe.sub mdifferentiableAt_const).div
    (z.mdifferentiable_coe.sub mdifferentiableAt_const) (by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.conj_im] at him
      norm_num at him
      linarith [z.im_pos, a.im_pos])

public theorem continuous_cayleyFromDisc (a : _root_.UpperHalfPlane) :
    Continuous (cayleyFromDisc a) := by
  apply _root_.UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun w : ComplexUnitDisc ↦
    ((a : ℂ) - w.1 * conj (a : ℂ)) / (1 - w.1))
  exact (continuous_const.sub (continuous_subtype_val.mul continuous_const)).div
    (continuous_const.sub continuous_subtype_val) (fun w ↦ ComplexUnitDisc.one_sub_coe_ne_zero w)

/-- The Cayley coordinate centered at `a` as a homeomorphism from the upper half-plane to the open
unit disc. -/
@[expose] public noncomputable def cayleyHomeomorph
    (a : _root_.UpperHalfPlane) : _root_.UpperHalfPlane ≃ₜ ComplexUnitDisc where
  toFun := cayleyToDisc a
  invFun := cayleyFromDisc a
  left_inv := cayleyFromDisc_cayleyToDisc a
  right_inv := cayleyToDisc_cayleyFromDisc a
  continuous_toFun := continuous_cayleyToDisc a
  continuous_invFun := continuous_cayleyFromDisc a

end UpperHalfPlane

end

end SphereSixComplex

namespace SphereSixComplex.Geometry.EllipticCayleyHomeomorph

open SphereSixComplex.Geometry.EllipticLocalCoordinates

noncomputable section

/-- The order-three elliptic base chart. -/
@[expose] public noncomputable def orderThreeCayleyHomeomorph :
    UpperHalfPlane ≃ₜ ComplexUnitDisc :=
  UpperHalfPlane.cayleyHomeomorph SphereSixComplex.TriangleGroup.fuchsianOneFixedPoint

/-- The order-four elliptic base chart. -/
@[expose] public noncomputable def orderFourCayleyHomeomorph :
    UpperHalfPlane ≃ₜ ComplexUnitDisc :=
  UpperHalfPlane.cayleyHomeomorph SphereSixComplex.TriangleGroup.fuchsianTwoFixedPoint

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
