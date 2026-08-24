module

public import SphereSixComplex.Geometry.EllipticComplexFilling
public import SphereSixComplex.TriangleGroup.FuchsianAction

/-!
# Explicit local coordinates at the elliptic points

The Cayley coordinate centered at `a ∈ ℍ` is `(z - a) / (z - conj a)`.  It identifies the
upper half-plane with the open unit disc and conjugates the two explicit elliptic generators to
scalar rotations.  These are purely local statements and use no global uniformization.
-/

open scoped ComplexConjugate

namespace SphereSixComplex.Geometry.EllipticLocalCoordinates

open Complex SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry

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

@[expose] public noncomputable def orderThreeCayley (z : UpperHalfPlane) : ℂ :=
  cayleyCoordinate fuchsianOneFixedPoint z

@[expose] public noncomputable def orderFourCayley (z : UpperHalfPlane) : ℂ :=
  cayleyCoordinate fuchsianTwoFixedPoint z

public theorem norm_orderThreeCayley_lt_one (z : UpperHalfPlane) :
    ‖orderThreeCayley z‖ < 1 :=
  norm_cayleyCoordinate_lt_one fuchsianOneFixedPoint z

public theorem norm_orderFourCayley_lt_one (z : UpperHalfPlane) :
    ‖orderFourCayley z‖ < 1 :=
  norm_cayleyCoordinate_lt_one fuchsianTwoFixedPoint z

@[simp]
public theorem orderThreeCayley_fixedPoint :
    orderThreeCayley fuchsianOneFixedPoint = 0 :=
  cayleyCoordinate_center fuchsianOneFixedPoint

@[simp]
public theorem orderFourCayley_fixedPoint :
    orderFourCayley fuchsianTwoFixedPoint = 0 :=
  cayleyCoordinate_center fuchsianTwoFixedPoint

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
  unfold orderFourCayley cayleyCoordinate orderFourMultiplier
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
  have hd := cayley_denominator_ne_zero fuchsianTwoFixedPoint z
  have hd' := cayley_denominator_ne_zero fuchsianTwoFixedPoint
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
  unfold orderThreeCayley cayleyCoordinate orderThreeMultiplier
  change (((((fuchsianSourceAction g₁) z : UpperHalfPlane) : ℂ) -
      (fuchsianOneFixedPoint : ℂ)) /
    ((((fuchsianSourceAction g₁) z : UpperHalfPlane) : ℂ) -
      conj (fuchsianOneFixedPoint : ℂ))) = _
  rw [fuchsianSourceAction_g₁_apply]
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hd := cayley_denominator_ne_zero fuchsianOneFixedPoint z
  have hd' := cayley_denominator_ne_zero fuchsianOneFixedPoint
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

/-- The order-three rotation on the explicit Cayley disc. -/
@[expose] public noncomputable def orderThreeDiscRotation : Equiv.Perm ComplexUnitDisc :=
  discScalarEquiv orderThreeMultiplier norm_orderThreeMultiplier

/-- The order-four rotation on the explicit Cayley disc. -/
@[expose] public noncomputable def orderFourDiscRotation : Equiv.Perm ComplexUnitDisc :=
  discScalarEquiv orderFourMultiplier norm_orderFourMultiplier

public theorem orderThreeDiscRotation_pow : orderThreeDiscRotation ^ 3 = 1 :=
  discScalarEquiv_pow_eq_one orderThreeMultiplier norm_orderThreeMultiplier 3
    orderThreeMultiplier_pow_three

public theorem orderFourDiscRotation_pow : orderFourDiscRotation ^ 4 = 1 :=
  discScalarEquiv_pow_eq_one orderFourMultiplier norm_orderFourMultiplier 4
    orderFourMultiplier_pow_four

@[expose] public def discOffCenter : ComplexUnitDisc := ⟨1 / 2, by norm_num⟩

public theorem discOffCenter_ne : discOffCenter ≠ discCenter := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [discOffCenter, discCenter] at hv

public theorem orderThreeDiscRotation_fixed_iff
    (k : ℕ) (hk : 0 < k) (hkm : k < 3) (w : ComplexUnitDisc) :
    (orderThreeDiscRotation ^ k) w = w ↔ w = discCenter := by
  have hkCases : k = 1 ∨ k = 2 := by omega
  rcases hkCases with rfl | rfl
  · exact discScalarEquiv_pow_fixed_iff orderThreeMultiplier norm_orderThreeMultiplier 1
      (by simpa using orderThreeMultiplier_ne_one) w
  · exact discScalarEquiv_pow_fixed_iff orderThreeMultiplier norm_orderThreeMultiplier 2
      orderThreeMultiplier_sq_ne_one w

public theorem orderFourDiscRotation_fixed_iff
    (k : ℕ) (hk : 0 < k) (hkm : k < 4) (w : ComplexUnitDisc) :
    (orderFourDiscRotation ^ k) w = w ↔ w = discCenter := by
  have hkCases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkCases with rfl | rfl | rfl
  · exact discScalarEquiv_pow_fixed_iff orderFourMultiplier norm_orderFourMultiplier 1
      (by simpa using orderFourMultiplier_ne_one) w
  · exact discScalarEquiv_pow_fixed_iff orderFourMultiplier norm_orderFourMultiplier 2
      orderFourMultiplier_sq_ne_one w
  · exact discScalarEquiv_pow_fixed_iff orderFourMultiplier norm_orderFourMultiplier 3
      orderFourMultiplier_cube_ne_one w

/-- Order-three Cayley coordinate with codomain the open unit disc. -/
@[expose] public noncomputable def orderThreeDiscCoordinate
    (z : UpperHalfPlane) : ComplexUnitDisc :=
  ⟨orderThreeCayley z, norm_orderThreeCayley_lt_one z⟩

/-- Order-four Cayley coordinate with codomain the open unit disc. -/
@[expose] public noncomputable def orderFourDiscCoordinate
    (z : UpperHalfPlane) : ComplexUnitDisc :=
  ⟨orderFourCayley z, norm_orderFourCayley_lt_one z⟩

/-- Local cyclic representation at the order-three elliptic point. -/
@[expose] public noncomputable def orderThreeDiscRepresentation :
    FiniteCyclic 3 →* Equiv.Perm ComplexUnitDisc :=
  cyclicRepresentation 3 orderThreeDiscRotation orderThreeDiscRotation_pow

/-- Local cyclic representation at the order-four elliptic point. -/
@[expose] public noncomputable def orderFourDiscRepresentation :
    FiniteCyclic 4 →* Equiv.Perm ComplexUnitDisc :=
  cyclicRepresentation 4 orderFourDiscRotation orderFourDiscRotation_pow

@[simp]
public theorem orderThreeDiscRepresentation_generator :
    orderThreeDiscRepresentation (cyclicGenerator 3) = orderThreeDiscRotation :=
  cyclicRepresentation_generator 3 orderThreeDiscRotation orderThreeDiscRotation_pow

@[simp]
public theorem orderFourDiscRepresentation_generator :
    orderFourDiscRepresentation (cyclicGenerator 4) = orderFourDiscRotation :=
  cyclicRepresentation_generator 4 orderFourDiscRotation orderFourDiscRotation_pow

/-- The order-three Cayley coordinate intertwines the Fuchsian stabilizer generator with the
local cyclic disc representation. -/
public theorem orderThreeDiscCoordinate_equivariant (z : UpperHalfPlane) :
    orderThreeDiscRepresentation (cyclicGenerator 3) (orderThreeDiscCoordinate z) =
      orderThreeDiscCoordinate (fuchsianSourceAction g₁ • z) := by
  apply Subtype.ext
  rw [orderThreeDiscRepresentation_generator]
  change orderThreeMultiplier * orderThreeCayley z =
    orderThreeCayley (fuchsianSourceAction g₁ • z)
  exact (orderThreeCayley_generator z).symm

/-- The order-four Cayley coordinate intertwines the Fuchsian stabilizer generator with the
local cyclic disc representation. -/
public theorem orderFourDiscCoordinate_equivariant (z : UpperHalfPlane) :
    orderFourDiscRepresentation (cyclicGenerator 4) (orderFourDiscCoordinate z) =
      orderFourDiscCoordinate (fuchsianSourceAction g₂ • z) := by
  apply Subtype.ext
  rw [orderFourDiscRepresentation_generator]
  change orderFourMultiplier * orderFourCayley z =
    orderFourCayley (fuchsianSourceAction g₂ • z)
  exact (orderFourCayley_generator z).symm

open SphereSixComplex.LatticeData

/-- The fibre-side input left by the local Cayley calculation.  It is exactly the torus-affine
part of `EllipticActionData`; all base rotation fields are discharged explicitly below. -/
public structure EllipticFiberData (m : ℕ) [NeZero m]
    (Torus : Type*) [AddCommGroup Torus] where
  automorphism : Torus ≃+ Torus
  translation : Torus
  translationVector : Lattice
  translation_fixed : automorphism translation = translation
  automorphism_pow : automorphism.toEquiv ^ m = 1
  translation_torsion : m • translation = 0
  fiber_fixed_iff : ∀ k, 0 < k → k < m →
    ((∃ x : Torus, (affineEquiv automorphism translation ^ k) x = x) ↔
      (m : ℤ) ∣ (k : ℤ) * gamma translationVector)

namespace EllipticFiberData

variable {Torus : Type*} [AddCommGroup Torus]

/-- Complete order-three filling data obtained by adjoining the explicit Cayley-disc base. -/
@[expose] public noncomputable def orderThreeActionData
    (D : EllipticFiberData 3 Torus) :
    EllipticActionData 3 ComplexUnitDisc Torus where
  rotation := orderThreeDiscRotation
  center := discCenter
  offCenter := discOffCenter
  offCenter_ne := discOffCenter_ne
  rotation_pow := orderThreeDiscRotation_pow
  rotation_fixed_iff := orderThreeDiscRotation_fixed_iff
  automorphism := D.automorphism
  translation := D.translation
  translationVector := D.translationVector
  translation_fixed := D.translation_fixed
  automorphism_pow := D.automorphism_pow
  translation_torsion := D.translation_torsion
  fiber_fixed_iff := D.fiber_fixed_iff

/-- Complete order-four filling data obtained by adjoining the explicit Cayley-disc base. -/
@[expose] public noncomputable def orderFourActionData
    (D : EllipticFiberData 4 Torus) :
    EllipticActionData 4 ComplexUnitDisc Torus where
  rotation := orderFourDiscRotation
  center := discCenter
  offCenter := discOffCenter
  offCenter_ne := discOffCenter_ne
  rotation_pow := orderFourDiscRotation_pow
  rotation_fixed_iff := orderFourDiscRotation_fixed_iff
  automorphism := D.automorphism
  translation := D.translation
  translationVector := D.translationVector
  translation_fixed := D.translation_fixed
  automorphism_pow := D.automorphism_pow
  translation_torsion := D.translation_torsion
  fiber_fixed_iff := D.fiber_fixed_iff

/-- The existing order-three filling freeness theorem applies directly to the explicit local
Cayley base. -/
public theorem orderThreeActionData_free (D : EllipticFiberData 3 Torus)
    (hv : D.translationVector = epsilon) :
    letI := D.orderThreeActionData.diagonalAction
    IsCancelSMul (FiniteCyclic 3) (ComplexUnitDisc × Torus) :=
  epsilon_action_free D.orderThreeActionData hv

/-- The existing order-four filling freeness theorem applies directly to the explicit local
Cayley base. -/
public theorem orderFourActionData_free (D : EllipticFiberData 4 Torus)
    (hv : D.translationVector = -epsilon') :
    letI := D.orderFourActionData.diagonalAction
    IsCancelSMul (FiniteCyclic 4) (ComplexUnitDisc × Torus) :=
  neg_epsilonPrime_action_free D.orderFourActionData hv

/-- The complex-filling theorem specializes to the explicit order-three Cayley base once the
remaining affine torus action is holomorphic. -/
public theorem orderThreeActionData_quotient_isManifold
    {E H : Type*} [TopologicalSpace (ComplexUnitDisc × Torus)] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : ModelWithCorners ℂ E H)
    [T2Space (ComplexUnitDisc × Torus)] [LocallyCompactSpace (ComplexUnitDisc × Torus)]
    [ChartedSpace H (ComplexUnitDisc × Torus)]
    [IsManifold I ω (ComplexUnitDisc × Torus)]
    (D : EllipticFiberData 3 Torus) (hv : D.translationVector = epsilon)
    (hholomorphic : ∀ g : FiniteCyclic 3,
      ContMDiff I I ω (fun p : ComplexUnitDisc × Torus ↦
        D.orderThreeActionData.representation g p)) :
    let A := D.orderThreeActionData
    letI := A.diagonalAction
    let hf := quotient_isQuotientCoveringMap A (epsilon_action_free A hv)
      (fun g ↦ (hholomorphic g).continuous)
    letI : ChartedSpace H
      (MulAction.orbitRel.Quotient (FiniteCyclic 3) (ComplexUnitDisc × Torus)) :=
      hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
    IsManifold I ω
      (MulAction.orbitRel.Quotient (FiniteCyclic 3) (ComplexUnitDisc × Torus)) := by
  exact epsilonQuotient_isManifold I D.orderThreeActionData hv hholomorphic

/-- The complex-filling theorem specializes to the explicit order-four Cayley base once the
remaining affine torus action is holomorphic. -/
public theorem orderFourActionData_quotient_isManifold
    {E H : Type*} [TopologicalSpace (ComplexUnitDisc × Torus)] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : ModelWithCorners ℂ E H)
    [T2Space (ComplexUnitDisc × Torus)] [LocallyCompactSpace (ComplexUnitDisc × Torus)]
    [ChartedSpace H (ComplexUnitDisc × Torus)]
    [IsManifold I ω (ComplexUnitDisc × Torus)]
    (D : EllipticFiberData 4 Torus) (hv : D.translationVector = -epsilon')
    (hholomorphic : ∀ g : FiniteCyclic 4,
      ContMDiff I I ω (fun p : ComplexUnitDisc × Torus ↦
        D.orderFourActionData.representation g p)) :
    let A := D.orderFourActionData
    letI := A.diagonalAction
    let hf := quotient_isQuotientCoveringMap A (neg_epsilonPrime_action_free A hv)
      (fun g ↦ (hholomorphic g).continuous)
    letI : ChartedSpace H
      (MulAction.orbitRel.Quotient (FiniteCyclic 4) (ComplexUnitDisc × Torus)) :=
      hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
    IsManifold I ω
      (MulAction.orbitRel.Quotient (FiniteCyclic 4) (ComplexUnitDisc × Torus)) := by
  exact negEpsilonPrimeQuotient_isManifold I D.orderFourActionData hv hholomorphic

end EllipticFiberData

end

end SphereSixComplex.Geometry.EllipticLocalCoordinates
