module

public import SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
public import SphereSixComplex.TriangleGroup.FuchsianPingPong

/-!
# Commutation forced by the order-four fixed point

An element of the `(3, 4, ∞)` triangle group which fixes the order-four
elliptic point commutes with the order-four generator.  The proof is carried
out on the chosen real special-linear lift and then transported back through
the faithful Fuchsian action.
-/

open Matrix UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace SphereSixComplex.TriangleGroup.FuchsianTwoFixedCommutation

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

private theorem specialLinear_commutes_with_fuchsianTwo_of_fixed
    (A : SL2R)
    (hfixed : fuchsianSLAction A • fuchsianTwoFixedPoint =
      fuchsianTwoFixedPoint) :
    Commute A fuchsianTwoSL := by
  let G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ A
  have hcomplex := congrArg (fun z : UpperHalfPlane ↦ (z : ℂ)) hfixed
  change ((G • fuchsianTwoFixedPoint : UpperHalfPlane) : ℂ) =
    (fuchsianTwoFixedPoint : ℂ) at hcomplex
  rw [UpperHalfPlane.coe_smul_of_det_pos] at hcomplex
  · have hden : UpperHalfPlane.denom G (fuchsianTwoFixedPoint : ℂ) ≠ 0 :=
      UpperHalfPlane.denom_ne_zero G fuchsianTwoFixedPoint
    have hcross := (div_eq_iff hden).mp hcomplex
    change
      (A 0 0 : ℂ) * (fuchsianTwoFixedPoint : ℂ) + A 0 1 =
        (fuchsianTwoFixedPoint : ℂ) *
          ((A 1 0 : ℂ) * (fuchsianTwoFixedPoint : ℂ) + A 1 1)
      at hcross
    have hre := congrArg Complex.re hcross
    have him := congrArg Complex.im hcross
    have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    norm_num [fuchsianTwoFixedPoint, Complex.mul_re, Complex.mul_im] at hre him
    have hd : A 1 1 = A 0 0 + Real.sqrt 2 * A 1 0 := by
      have hmul : Real.sqrt 2 *
          (A 1 1 - A 0 0 - Real.sqrt 2 * A 1 0) = 0 := by
        nlinarith [hsqrt]
      have hzero := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hsqrt_pos)
      nlinarith
    have hb : A 0 1 = -A 1 0 := by
      rw [hd] at hre
      ring_nf at hre
      rw [hsqrt] at hre
      linarith
    apply Subtype.ext
    change
      (A : Matrix (Fin 2) (Fin 2) ℝ) *
          (!![0, -1; 1, Real.sqrt 2] : Matrix (Fin 2) (Fin 2) ℝ) =
        (!![0, -1; 1, Real.sqrt 2] : Matrix (Fin 2) (Fin 2) ℝ) * A
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, hb, hd]
    all_goals ring
  · simp [G, Matrix.SpecialLinearGroup.det_mapGL]

/-- Fixing the order-four elliptic point forces commutation with `g₂`. -/
public theorem commute_gTwo_of_fuchsianTwoFixedPoint_fixed
    (g : Delta)
    (hfixed : fuchsianSourceAction g • fuchsianTwoFixedPoint =
      fuchsianTwoFixedPoint) :
    Commute g g₂ := by
  have hmatrix : Commute (deltaRealSL g) fuchsianTwoSL :=
    specialLinear_commutes_with_fuchsianTwo_of_fixed (deltaRealSL g) (by
      rw [← fuchsianSourceAction_eq_deltaRealSL g]
      exact hfixed)
  apply FuchsianPingPong.fuchsianSourceAction_injective
  simp only [map_mul, fuchsianSourceAction_eq_deltaRealSL g,
    fuchsianSourceAction_g₂]
  change
    fuchsianSLAction (deltaRealSL g) * fuchsianSLAction fuchsianTwoSL =
      fuchsianSLAction fuchsianTwoSL * fuchsianSLAction (deltaRealSL g)
  rw [← map_mul, ← map_mul, hmatrix.eq]

end SphereSixComplex.TriangleGroup.FuchsianTwoFixedCommutation
