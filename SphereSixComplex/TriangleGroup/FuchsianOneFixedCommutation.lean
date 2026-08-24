module

public import SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints

/-!
# Commutation forced by the order-three Fuchsian fixed point

An element of the explicit triangle group that fixes the order-three elliptic point commutes
with the order-three generator.  The proof works with the canonical special-linear lift: the
fixed-point equation forces its matrix to lie in the centralizer of `fuchsianOneSL`, and
faithfulness of the Fuchsian action then reflects commutation back to the free product.
-/

open Matrix UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace SphereSixComplex.TriangleGroup

open FuchsianArithmeticTermination

/-- A triangle-group element fixing the order-three elliptic point commutes with the
order-three generator. -/
public theorem commute_gOne_of_fuchsianOneFixed (g : Delta)
    (hg : fuchsianSourceAction g • fuchsianOneFixedPoint = fuchsianOneFixedPoint) :
    Commute g g₁ := by
  let A : SL2R := deltaRealSL g
  have hfix :
      (Matrix.SpecialLinearGroup.mapGL ℝ A) • fuchsianOneFixedPoint =
        fuchsianOneFixedPoint := by
    rw [fuchsianSourceAction_eq_deltaRealSL] at hg
    exact hg
  have hquad :=
    (UpperHalfPlane.gl_smul_eq_self_iff_quadratic
      (g := Matrix.SpecialLinearGroup.mapGL ℝ A)
      (z := fuchsianOneFixedPoint)
      (by norm_num [Matrix.SpecialLinearGroup.det_mapGL])).mp hfix
  simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.algebraMap_self, RingHom.id_apply, fuchsianOneFixedPoint] at hquad
  change
    ((A 1 0 : ℂ) *
          ((⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) * ⟨1 / 2, Real.sqrt 3 / 2⟩) +
        ((A 1 1 : ℂ) - (A 0 0 : ℂ)) * ⟨1 / 2, Real.sqrt 3 / 2⟩ +
        -(A 0 1 : ℂ)) = 0 at hquad
  have him := congrArg Complex.im hquad
  have hre := congrArg Complex.re hquad
  norm_num [Complex.mul_re, Complex.mul_im] at him hre
  have hsqrtmul : Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = (3 : ℝ) / 4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hsqrtmul] at hre
  have him' :
      (Real.sqrt 3 / 2) * (A 1 0 + A 1 1 - A 0 0) = 0 := by
    linear_combination him
  have hsqrt : Real.sqrt 3 / 2 ≠ 0 := by positivity
  have hdiag : A 1 1 = A 0 0 - A 1 0 := by
    have := (mul_eq_zero.mp him').resolve_left hsqrt
    linarith
  have hoff : A 0 1 = -A 1 0 := by
    linarith
  have hA : Commute A fuchsianOneSL := by
    apply Subtype.ext
    change
      (A : Matrix (Fin 2) (Fin 2) ℝ) *
          (fuchsianOneSL : Matrix (Fin 2) (Fin 2) ℝ) =
        (fuchsianOneSL : Matrix (Fin 2) (Fin 2) ℝ) *
          (A : Matrix (Fin 2) (Fin 2) ℝ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, fuchsianOneSL, hdiag, hoff]
    all_goals ring
  apply FuchsianPingPong.fuchsianSourceAction_injective
  rw [map_mul, map_mul, fuchsianSourceAction_eq_deltaRealSL,
    fuchsianSourceAction_g₁]
  change fuchsianSLAction A * fuchsianSLAction fuchsianOneSL =
    fuchsianSLAction fuchsianOneSL * fuchsianSLAction A
  simpa only [← map_mul] using congrArg fuchsianSLAction hA.eq

end SphereSixComplex.TriangleGroup
