module

public import SphereSixComplex.Prerequisites.Geometry.ComplexUnitDisc
public import SphereSixComplex.Prerequisites.Geometry.FiniteCyclicAffineAction
public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianAction
import all SphereSixComplex.Prerequisites.Geometry.ComplexUnitDisc
import all SphereSixComplex.Prerequisites.TriangleGroup.SourceGroup

namespace SphereSixComplex.Geometry.EllipticLocalCoordinates

open Complex SphereSixComplex.TriangleGroup SphereSixComplex.Geometry
open scoped ComplexConjugate Manifold

noncomputable section

@[expose] public noncomputable def orderThreeCayley (z : UpperHalfPlane) : ℂ :=
  UpperHalfPlane.cayley fuchsianOneFixedPoint z

@[expose] public noncomputable def orderFourCayley (z : UpperHalfPlane) : ℂ :=
  UpperHalfPlane.cayley fuchsianTwoFixedPoint z

public theorem norm_orderThreeCayley_lt_one (z : UpperHalfPlane) :
    ‖orderThreeCayley z‖ < 1 :=
  UpperHalfPlane.norm_cayley_lt_one fuchsianOneFixedPoint z

public theorem norm_orderFourCayley_lt_one (z : UpperHalfPlane) :
    ‖orderFourCayley z‖ < 1 :=
  UpperHalfPlane.norm_cayley_lt_one fuchsianTwoFixedPoint z

@[simp]
public theorem orderThreeCayley_fixedPoint :
    orderThreeCayley fuchsianOneFixedPoint = 0 :=
  UpperHalfPlane.cayley_self fuchsianOneFixedPoint

@[simp]
public theorem orderFourCayley_fixedPoint :
    orderFourCayley fuchsianTwoFixedPoint = 0 :=
  UpperHalfPlane.cayley_self fuchsianTwoFixedPoint

/-- Rotation multiplier of the order-three source generator in Cayley coordinates. -/
@[expose] public noncomputable def orderThreeMultiplier : ℂ :=
  ⟨-1 / 2, -Real.sqrt 3 / 2⟩

/-- Rotation multiplier of the order-four source generator in Cayley coordinates. -/
@[expose] public def orderFourMultiplier : ℂ := -Complex.I

public theorem norm_orderThreeMultiplier : ‖orderThreeMultiplier‖ = 1 := by
  rw [Complex.norm_def]
  have hsq : Complex.normSq orderThreeMultiplier = 1 := by
    simp only [orderThreeMultiplier, Complex.normSq_apply]
    norm_num
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [hsq]
  norm_num

public theorem norm_orderFourMultiplier : ‖orderFourMultiplier‖ = 1 := by
  simp [orderFourMultiplier]

/-- The order-four Fuchsian generator becomes multiplication by `-i` in its Cayley coordinate. -/
public theorem orderFourCayley_generator (z : UpperHalfPlane) :
    orderFourCayley (fuchsianSourceAction g₂ • z) =
      orderFourMultiplier * orderFourCayley z := by
  unfold orderFourCayley UpperHalfPlane.cayley orderFourMultiplier
  change (((((fuchsianSourceAction g₂) z : UpperHalfPlane) : ℂ) -
      (fuchsianTwoFixedPoint : ℂ)) /
    ((((fuchsianSourceAction g₂) z : UpperHalfPlane) : ℂ) -
      conj (fuchsianTwoFixedPoint : ℂ))) = _
  rw [fuchsianSourceAction_g₂_apply]
  have hz : (z : ℂ) + Real.sqrt 2 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    exact z.im_pos.ne' him
  have hd := UpperHalfPlane.cayley_denominator_ne_zero fuchsianTwoFixedPoint z
  have hd' := UpperHalfPlane.cayley_denominator_ne_zero fuchsianTwoFixedPoint
    (fuchsianSourceAction g₂ • z)
  change (((fuchsianSourceAction g₂) z : UpperHalfPlane) : ℂ) -
    conj (fuchsianTwoFixedPoint : ℂ) ≠ 0 at hd'
  rw [fuchsianSourceAction_g₂_apply] at hd'
  have hratio : -1 / ((z : ℂ) + Real.sqrt 2) -
      conj (fuchsianTwoFixedPoint : ℂ) =
      (-1 - ((z : ℂ) + Real.sqrt 2) *
        conj (fuchsianTwoFixedPoint : ℂ)) / ((z : ℂ) + Real.sqrt 2) := by
    field_simp [hz]
  rw [hratio] at hd'
  have hcombo : -1 - ((z : ℂ) + Real.sqrt 2) *
      conj (fuchsianTwoFixedPoint : ℂ) ≠ 0 := (div_ne_zero_iff.mp hd').1
  field_simp [hz, hd, hd', hcombo]
  apply Complex.ext <;>
    norm_num [fuchsianTwoFixedPoint, Complex.mul_re, Complex.mul_im]
  all_goals
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hcube : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      rw [show Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring, hsq]
    ring_nf
    rw [hcube]
    rw [hsq]
    ring

/-- The order-three Fuchsian generator becomes the primitive cubic rotation with multiplier
`(-1 - i sqrt 3) / 2` in its Cayley coordinate. -/
public theorem orderThreeCayley_generator (z : UpperHalfPlane) :
    orderThreeCayley (fuchsianSourceAction g₁ • z) =
      orderThreeMultiplier * orderThreeCayley z := by
  unfold orderThreeCayley UpperHalfPlane.cayley orderThreeMultiplier
  change (((((fuchsianSourceAction g₁) z : UpperHalfPlane) : ℂ) -
      (fuchsianOneFixedPoint : ℂ)) /
    ((((fuchsianSourceAction g₁) z : UpperHalfPlane) : ℂ) -
      conj (fuchsianOneFixedPoint : ℂ))) = _
  rw [fuchsianSourceAction_g₁_apply]
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hd := UpperHalfPlane.cayley_denominator_ne_zero fuchsianOneFixedPoint z
  have hd' := UpperHalfPlane.cayley_denominator_ne_zero fuchsianOneFixedPoint
    (fuchsianSourceAction g₁ • z)
  change (((fuchsianSourceAction g₁) z : UpperHalfPlane) : ℂ) -
    conj (fuchsianOneFixedPoint : ℂ) ≠ 0 at hd'
  rw [fuchsianSourceAction_g₁_apply] at hd'
  have hratio : ((z : ℂ) - 1) / z - conj (fuchsianOneFixedPoint : ℂ) =
      ((z : ℂ) - 1 - z * conj (fuchsianOneFixedPoint : ℂ)) / z := by
    field_simp [hz]
  rw [hratio] at hd'
  have hcombo : (z : ℂ) - 1 - z * conj (fuchsianOneFixedPoint : ℂ) ≠ 0 :=
    (div_ne_zero_iff.mp hd').1
  field_simp [hz, hd, hd', hcombo]
  apply Complex.ext <;>
    norm_num [fuchsianOneFixedPoint, Complex.mul_re, Complex.mul_im]
  all_goals
    have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hcube : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
      rw [show Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 by ring, hsq]
    ring_nf
    rw [hcube]
    rw [hsq]
    ring

public theorem orderThreeMultiplier_pow_three : orderThreeMultiplier ^ 3 = 1 := by
  apply Complex.ext <;>
    norm_num [orderThreeMultiplier, Complex.mul_re, Complex.mul_im, pow_succ]
  all_goals
    ring_nf
    have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hcube : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
      rw [show Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 by ring, hsq]
    first
    | rw [hcube]; ring
    | rw [hsq]; ring

public theorem orderFourMultiplier_pow_four : orderFourMultiplier ^ 4 = 1 := by
  norm_num [orderFourMultiplier, pow_succ]

private theorem orderThreeMultiplier_ne_one : orderThreeMultiplier ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  norm_num [orderThreeMultiplier] at him

private theorem orderThreeMultiplier_sq_ne_one : orderThreeMultiplier ^ 2 ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  norm_num [orderThreeMultiplier, Complex.mul_im, pow_two] at him
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  linarith

private theorem orderFourMultiplier_ne_one : orderFourMultiplier ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  norm_num [orderFourMultiplier] at him

private theorem orderFourMultiplier_sq_ne_one : orderFourMultiplier ^ 2 ≠ 1 := by
  norm_num [orderFourMultiplier, pow_two]

private theorem orderFourMultiplier_cube_ne_one : orderFourMultiplier ^ 3 ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  norm_num [orderFourMultiplier, pow_succ] at him

/-- The order-three rotation on the explicit Cayley disc. -/
@[expose] public noncomputable def orderThreeDiscRotation : Equiv.Perm ComplexUnitDisc :=
  ComplexUnitDisc.rotation orderThreeMultiplier norm_orderThreeMultiplier

/-- The order-four rotation on the explicit Cayley disc. -/
@[expose] public noncomputable def orderFourDiscRotation : Equiv.Perm ComplexUnitDisc :=
  ComplexUnitDisc.rotation orderFourMultiplier norm_orderFourMultiplier

public theorem orderThreeDiscRotation_pow : orderThreeDiscRotation ^ 3 = 1 :=
  ComplexUnitDisc.rotation_pow_eq_one orderThreeMultiplier norm_orderThreeMultiplier 3
    orderThreeMultiplier_pow_three

public theorem orderFourDiscRotation_pow : orderFourDiscRotation ^ 4 = 1 :=
  ComplexUnitDisc.rotation_pow_eq_one orderFourMultiplier norm_orderFourMultiplier 4
    orderFourMultiplier_pow_four

@[expose] public def discOffCenter : ComplexUnitDisc := ⟨1 / 2, by norm_num⟩

public theorem discOffCenter_ne : discOffCenter ≠ ComplexUnitDisc.center := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [discOffCenter, ComplexUnitDisc.center] at hv

public theorem orderThreeDiscRotation_fixed_iff
    (k : ℕ) (hk : 0 < k) (hkm : k < 3) (w : ComplexUnitDisc) :
    (orderThreeDiscRotation ^ k) w = w ↔ w = ComplexUnitDisc.center := by
  have hkCases : k = 1 ∨ k = 2 := by omega
  rcases hkCases with rfl | rfl
  · exact ComplexUnitDisc.rotation_pow_eq_self_iff orderThreeMultiplier norm_orderThreeMultiplier 1
      (by simpa using orderThreeMultiplier_ne_one) w
  · exact ComplexUnitDisc.rotation_pow_eq_self_iff orderThreeMultiplier norm_orderThreeMultiplier 2
      orderThreeMultiplier_sq_ne_one w

public theorem orderFourDiscRotation_fixed_iff
    (k : ℕ) (hk : 0 < k) (hkm : k < 4) (w : ComplexUnitDisc) :
    (orderFourDiscRotation ^ k) w = w ↔ w = ComplexUnitDisc.center := by
  have hkCases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkCases with rfl | rfl | rfl
  · exact ComplexUnitDisc.rotation_pow_eq_self_iff orderFourMultiplier norm_orderFourMultiplier 1
      (by simpa using orderFourMultiplier_ne_one) w
  · exact ComplexUnitDisc.rotation_pow_eq_self_iff orderFourMultiplier norm_orderFourMultiplier 2
      orderFourMultiplier_sq_ne_one w
  · exact ComplexUnitDisc.rotation_pow_eq_self_iff orderFourMultiplier norm_orderFourMultiplier 3
      orderFourMultiplier_cube_ne_one w









end

end SphereSixComplex.Geometry.EllipticLocalCoordinates
