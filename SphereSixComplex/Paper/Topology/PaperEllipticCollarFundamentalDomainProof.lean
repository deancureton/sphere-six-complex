module

public import SphereSixComplex.Prerequisites.Topology.CyclicPuncturedProductMappingTorus
public import SphereSixComplex.Paper.Geometry.EllipticLocalCoordinates

@[expose] public section
noncomputable section
open Set Topology
open scoped Real
namespace SphereSixComplex
namespace CyclicAngularFundamentalDomain
section ActualMultipliers

open Geometry Geometry.EllipticLocalCoordinates

/-- The order-three collar multiplier is the standard clockwise third of a turn. -/
public theorem orderThreeMultiplier_eq_standardMultiplier :
    orderThreeMultiplier = standardMultiplier 3 := by
  have hsplit : (2 * π / (3 : ℕ) : ℝ) = π - π / 3 := by
    push_cast
    ring
  apply Complex.ext
  · show (-1 / 2 : ℝ) = (Complex.exp (((-(2 * π / (3 : ℕ)) : ℝ) : ℂ) * Complex.I)).re
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg, hsplit, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  · show (-Real.sqrt 3 / 2 : ℝ) = (Complex.exp (((-(2 * π / (3 : ℕ)) : ℝ) : ℂ) * Complex.I)).im
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg, hsplit, Real.sin_pi_sub,
      Real.sin_pi_div_three]
    ring

/-- The order-four collar multiplier is the standard clockwise quarter of a turn. -/
public theorem orderFourMultiplier_eq_standardMultiplier :
    orderFourMultiplier = standardMultiplier 4 := by
  have hsplit : (2 * π / (4 : ℕ) : ℝ) = π / 2 := by
    push_cast
    ring
  apply Complex.ext
  · show (-Complex.I).re = (Complex.exp (((-(2 * π / (4 : ℕ)) : ℝ) : ℂ) * Complex.I)).re
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg, hsplit, Real.cos_pi_div_two]
    simp
  · show (-Complex.I).im = (Complex.exp (((-(2 * π / (4 : ℕ)) : ℝ) : ℂ) * Complex.I)).im
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg, hsplit, Real.sin_pi_div_two]
    simp

end ActualMultipliers

end CyclicAngularFundamentalDomain

end SphereSixComplex
