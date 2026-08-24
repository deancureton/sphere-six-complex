module

public import SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
import all SphereSixComplex.Geometry.GlobalTorusFamily
import all SphereSixComplex.TriangleGroup.Representation

/-!
# The cusp obstruction for the affine free-product action

The paper uses the linear triangle-group action on the global torus family.  Its affine elliptic
actions live on the two local fillings and are identified with the linear action only after the
logarithmic collar changes of coordinates.  Extending both affine generators directly to the
free product does not recover the linear action at the cusp: its invariant translation character
is `1 / 3 - 1 / 4 = 1 / 12`.
-/

namespace SphereSixComplex.Geometry.EllipticAffineCuspObstruction

open Matrix
open SphereSixComplex.LatticeData SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- The invariant real period character is preserved by first-generator transport over every
point of the period domain. -/
public theorem gammaCoordinate_transport_gOne (x : PeriodDomain) (z : ComplexTwoSpace) :
    gammaCoordinate (rhoParameters g₁ x) (periodTransport g₁ x z) = gammaCoordinate x z := by
  change gammaReal (periodCoordinates (rhoParameters g₁ x) (periodTransport g₁ x z)) =
    gammaReal (periodCoordinates x z)
  rw [periodCoordinates_transport, gammaReal_rhoLambdaReal_gOne]

/-- The order-three twist has invariant character `1 / 3` over every period domain. -/
public theorem gammaCoordinate_oneThirdPeriod (x : PeriodDomain) :
    gammaCoordinate x ((3 : ℂ)⁻¹ • periodVector x.1 epsilon) = (3 : ℝ)⁻¹ := by
  have hs : ((3 : ℂ)⁻¹ • periodVector x.1 epsilon) =
      (3 : ℝ)⁻¹ • periodVector x.1 epsilon := by
    ext i
    simp [Complex.real_smul]
  rw [hs, map_smul, gammaCoordinate_periodVector, gamma_epsilon]
  norm_num

/-- The order-four twist has invariant character `-1 / 4` over every period domain. -/
public theorem gammaCoordinate_negOneQuarterPeriod (x : PeriodDomain) :
    gammaCoordinate x ((4 : ℂ)⁻¹ • periodVector x.1 (-epsilon')) = -(4 : ℝ)⁻¹ := by
  have hs : ((4 : ℂ)⁻¹ • periodVector x.1 (-epsilon')) =
      (4 : ℝ)⁻¹ • periodVector x.1 (-epsilon') := by
    ext i
    simp [Complex.real_smul]
  rw [hs, map_smul, gammaCoordinate_periodVector, gamma_neg_epsilon']
  norm_num

/-- Translation accumulated when the two affine elliptic generators are composed. -/
@[expose] public noncomputable def ellipticAffineProductTranslation
    (z : UpperHalfPlane) : ComplexTwoSpace :=
  orderThreeTwistSection F (U.sourceAction g₁ • (U.sourceAction g₂ • z)) +
    periodTransport g₁ (parameterMap F (U.sourceAction g₂ • z))
      (orderFourTwistSection F (U.sourceAction g₂ • z))

/-- The accumulated elliptic translation has invariant character exactly `1 / 12`. -/
public theorem gammaCoordinate_ellipticAffineProductTranslation (z : UpperHalfPlane) :
    gammaCoordinate (parameterMap F (U.sourceAction g₁ • (U.sourceAction g₂ • z)))
      (ellipticAffineProductTranslation F z) = (12 : ℝ)⁻¹ := by
  have hparam := parameterMap_equivariant F g₁
  rw [ParameterEquivariant.eq_def] at hparam
  rw [ellipticAffineProductTranslation, orderThreeTwistSection.eq_def,
    orderFourTwistSection.eq_def, hparam (U.sourceAction g₂ • z), map_add,
    gammaCoordinate_oneThirdPeriod, gammaCoordinate_transport_gOne,
    gammaCoordinate_negOneQuarterPeriod]
  norm_num

public theorem affineGlobalFamilyRepresentation_gOne :
    affineGlobalFamilyRepresentation F g₁ = orderThreeAffineFamilyGenerator F := by
  rw [SphereSixComplex.TriangleGroup.g₁.eq_def, affineGlobalFamilyRepresentation_inl]
  exact cyclicRepresentation_generator 3 _ _

public theorem affineGlobalFamilyRepresentation_gTwo :
    affineGlobalFamilyRepresentation F g₂ = orderFourAffineFamilyGenerator F := by
  rw [SphereSixComplex.TriangleGroup.g₂.eq_def, affineGlobalFamilyRepresentation_inr]
  exact cyclicRepresentation_generator 4 _ _

public theorem affineGlobalFamilyRepresentation_product_zero (z : UpperHalfPlane) :
    affineGlobalFamilyRepresentation F (g₁ * g₂)
        (Quotient.mk _ (z, (0 : ComplexTwoSpace))) =
      Quotient.mk _ (U.sourceAction g₁ • (U.sourceAction g₂ • z),
        ellipticAffineProductTranslation F z) := by
  rw [map_mul, Equiv.Perm.mul_apply, affineGlobalFamilyRepresentation_gOne,
    affineGlobalFamilyRepresentation_gTwo]
  simp only [orderThreeAffineFamilyGenerator.eq_def, orderFourAffineFamilyGenerator.eq_def,
    Equiv.Perm.mul_apply, familyDeckEquiv_apply, familyDeckMap_mk, deckMap.eq_def,
    familyTranslationEquiv_apply, familyTranslationMap_mk, familyTranslationCover.eq_def,
    map_zero, add_zero, ellipticAffineProductTranslation]

public theorem familyDeckEquiv_product_zero (z : UpperHalfPlane) :
    familyDeckEquiv F (g₁ * g₂) (Quotient.mk _ (z, (0 : ComplexTwoSpace))) =
      Quotient.mk _
        (U.sourceAction g₁ • (U.sourceAction g₂ • z), (0 : ComplexTwoSpace)) := by
  simp only [familyDeckEquiv_apply, familyDeckMap_mk, deckMap.eq_def, map_zero, map_mul,
    mul_smul]

/-- The free-product extension of the affine elliptic generators is not the linear deck action
on the product of the two generators. -/
public theorem affineGlobalFamilyRepresentation_product_ne_familyDeckEquiv :
    affineGlobalFamilyRepresentation F (g₁ * g₂) ≠ familyDeckEquiv F (g₁ * g₂) := by
  intro h
  let z : UpperHalfPlane := UpperHalfPlane.I
  have hq := DFunLike.congr_fun h (Quotient.mk _ (z, (0 : ComplexTwoSpace)))
  rw [affineGlobalFamilyRepresentation_product_zero, familyDeckEquiv_product_zero] at hq
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hq
  obtain ⟨a, ha⟩ := hq
  have hv := congrArg Prod.snd ha
  simp only [family_smul_snd, add_zero] at hv
  have hgamma := congrArg
    (gammaCoordinate
      (parameterMap F (U.sourceAction g₁ • (U.sourceAction g₂ • z)))) hv
  rw [gammaCoordinate_periodVector, gammaCoordinate_ellipticAffineProductTranslation] at hgamma
  have h12 : (12 : ℝ) * ((gamma a.coeff : ℤ) : ℝ) = 1 := by
    rw [hgamma]
    norm_num
  have h12z : (12 : ℤ) * gamma a.coeff = 1 := by
    exact_mod_cast h12
  omega

/-- In particular, the cusp generator of the affine free-product action is not the untwisted
linear cusp deck map. -/
public theorem affineGlobalFamilyRepresentation_gZero_ne_familyDeckEquiv :
    affineGlobalFamilyRepresentation F g₀ ≠ familyDeckEquiv F g₀ := by
  intro h
  apply affineGlobalFamilyRepresentation_product_ne_familyDeckEquiv F
  change affineGlobalFamilyRepresentation F g₀ = familyDeckRepresentation F g₀ at h
  rw [g₀, map_inv, map_inv] at h
  exact inv_injective h

end

end SphereSixComplex.Geometry.EllipticAffineCuspObstruction
