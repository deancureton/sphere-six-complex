module

public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianFundamentalDomain

/-!
# Deterministic reduction toward a Ford region

The cusp translation first moves a point into a centered strip of width `1 + √2`.  If the
result lies inside the unit circle, the order-three generator strictly increases its imaginary
part.  Re-centering does not change that height.  These facts isolate the remaining arithmetic
termination statement: an orbit must contain a point of maximal imaginary part.
-/

noncomputable section

namespace SphereSixComplex.TriangleGroup.FuchsianTessellation

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain

/-- The exact action of every integral power of the positive cusp translation. -/
public theorem product_zpow_apply (n : ℤ) (z : UpperHalfPlane) :
    (((fuchsianSourceAction ((g₁ * g₂) ^ n)) z : UpperHalfPlane) : ℂ) =
      z + n * cuspWidth := by
  cases n with
  | ofNat n =>
      simpa [zpow_ofNat] using product_pow_apply n z
  | negSucc n =>
      rw [zpow_negSucc, ← inv_pow]
      have hinv : (g₁ * g₂)⁻¹ = g₀ :=
        (eq_inv_of_mul_eq_one_right g₁_mul_g₂_mul_g₀).symm
      rw [hinv, cusp_pow_apply]
      push_cast
      ring

public theorem product_zpow_re (n : ℤ) (z : UpperHalfPlane) :
    (fuchsianSourceAction ((g₁ * g₂) ^ n) • z).re = z.re + n * cuspWidth := by
  have h := congrArg Complex.re (product_zpow_apply n z)
  simpa using h

public theorem product_zpow_im (n : ℤ) (z : UpperHalfPlane) :
    (fuchsianSourceAction ((g₁ * g₂) ^ n) • z).im = z.im := by
  have h := congrArg Complex.im (product_zpow_apply n z)
  simpa using h

/-- The canonical exponent which centers the real part in a cusp strip. -/
@[expose] public noncomputable def centerExponent (z : UpperHalfPlane) : ℤ :=
  -⌊(z.re + cuspWidth / 2) / cuspWidth⌋

/-- The canonical cusp translate of a point into the centered strip. -/
@[expose] public noncomputable def centerPoint (z : UpperHalfPlane) : UpperHalfPlane :=
  fuchsianSourceAction ((g₁ * g₂) ^ centerExponent z) • z

public theorem centerPoint_re_lower (z : UpperHalfPlane) :
    -cuspWidth / 2 ≤ (centerPoint z).re := by
  rw [centerPoint, product_zpow_re]
  have h := Int.sub_floor_div_mul_nonneg (z.re + cuspWidth / 2) cuspWidth_pos
  dsimp only [centerExponent]
  push_cast at h ⊢
  nlinarith

public theorem centerPoint_re_upper (z : UpperHalfPlane) :
    (centerPoint z).re < cuspWidth / 2 := by
  rw [centerPoint, product_zpow_re]
  have h := Int.sub_floor_div_mul_lt (z.re + cuspWidth / 2) cuspWidth_pos
  dsimp only [centerExponent]
  push_cast at h ⊢
  nlinarith

public theorem centerPoint_im (z : UpperHalfPlane) : (centerPoint z).im = z.im := by
  exact product_zpow_im (centerExponent z) z


/-- The order-three side pairing divides imaginary height by the squared norm. -/
public theorem gOne_im_eq_div_normSq (z : UpperHalfPlane) :
    (fuchsianSourceAction g₁ • z).im = z.im / Complex.normSq (z : ℂ) := by
  have h := congrArg Complex.im (fuchsianSourceAction_g₁_apply z)
  rw [Complex.div_im] at h
  norm_num at h
  rw [fuchsianSourceAction_g₁]
  change (fuchsianOnePerm z).im = _
  rw [h]
  ring

/-- Crossing the unit-circle side strictly increases imaginary height. -/
public theorem gOne_strictly_increases_im_of_normSq_lt_one (z : UpperHalfPlane)
    (hz : Complex.normSq (z : ℂ) < 1) :
    z.im < (fuchsianSourceAction g₁ • z).im := by
  rw [gOne_im_eq_div_normSq]
  have hnorm : 0 < Complex.normSq (z : ℂ) := z.normSq_pos
  apply (lt_div_iff₀ hnorm).2
  nlinarith [z.im_pos]

/-- A coarse Ford region bounded by the cusp strip and the unit semicircle. -/
@[expose] public noncomputable def coarseFordRegion : Set UpperHalfPlane :=
  {z | -cuspWidth / 2 ≤ z.re ∧ z.re < cuspWidth / 2 ∧ 1 ≤ Complex.normSq (z : ℂ)}








/-- A point has maximal height in its orbit when no group element raises its imaginary part. -/
@[expose] public def IsOrbitHeightMaximal (z : UpperHalfPlane) : Prop :=
  ∀ g : Delta, (fuchsianSourceAction g • z).im ≤ z.im

public theorem IsOrbitHeightMaximal.normSq_ge_one {z : UpperHalfPlane}
    (hz : IsOrbitHeightMaximal z) :
    1 ≤ Complex.normSq (z : ℂ) := by
  by_contra h
  have hlt : Complex.normSq (z : ℂ) < 1 := lt_of_not_ge h
  exact (not_lt_of_ge (hz g₁)) (gOne_strictly_increases_im_of_normSq_lt_one z hlt)

public theorem IsOrbitHeightMaximal.product_zpow {z : UpperHalfPlane}
    (hz : IsOrbitHeightMaximal z) (n : ℤ) :
    IsOrbitHeightMaximal (fuchsianSourceAction ((g₁ * g₂) ^ n) • z) := by
  intro g
  calc
    (fuchsianSourceAction g • fuchsianSourceAction ((g₁ * g₂) ^ n) • z).im =
        (fuchsianSourceAction (g * (g₁ * g₂) ^ n) • z).im := by
          rw [map_mul, mul_smul]
    _ ≤ z.im := hz _
    _ = (fuchsianSourceAction ((g₁ * g₂) ^ n) • z).im :=
      (product_zpow_im n z).symm

/-- A maximal-height point can be moved into the coarse Ford region. -/
public theorem IsOrbitHeightMaximal.exists_mem_coarseFordRegion {z : UpperHalfPlane}
    (hz : IsOrbitHeightMaximal z) :
    ∃ n : ℤ, fuchsianSourceAction ((g₁ * g₂) ^ n) • z ∈ coarseFordRegion := by
  refine ⟨centerExponent z, centerPoint_re_lower z, centerPoint_re_upper z, ?_⟩
  exact (hz.product_zpow (centerExponent z)).normSq_ge_one


end SphereSixComplex.TriangleGroup.FuchsianTessellation
