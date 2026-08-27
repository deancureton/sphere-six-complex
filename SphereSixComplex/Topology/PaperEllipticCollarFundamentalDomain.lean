module

public import SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
public import SphereSixComplex.Topology.PaperCollarMappingTorusAdapters
public import SphereSixComplex.Topology.PaperEllipticCollarFundamentalDomainProof

/-!
# Angular fundamental domains for the elliptic collars

The punctured elliptic collars retain an open radial coordinate.  Consequently their correct
global model is an open radial interval times a mapping torus, rather than the mapping torus
alone.  This file proves the analytic collar's reduction to the explicit diagonal product
quotient and isolates the remaining general angular-fundamental-domain theorem.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex

open Geometry Geometry.EllipticLocalCoordinates
open Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.TriangleGroup

/-- The open radial coordinate occurring in a punctured disc of radius `r`. -/
public abbrev OpenRadialInterval (r : ℝ) := {s : ℝ // 0 < s ∧ s < r}

/-- General data for the quotient of a punctured disc--fibre product by a cyclic diagonal
action.  The hypotheses mention only the action, its generator, and the scalar rotation. -/
public structure CyclicPuncturedProductData
    (m : ℕ) [NeZero m] (T : Type) [TopologicalSpace T] (r : ℝ) where
  radius_pos : 0 < r
  radius_lt_one : r < 1
  action : MulAction (FiniteCyclic m) (ComplexUnitDisc × T)
  clutching : T ≃ₜ T
  multiplier : ℂ
  multiplier_norm : ‖multiplier‖ = 1
  generator_formula : ∀ p : ComplexUnitDisc × T,
    actionMap action (cyclicGenerator m) p =
      (discScalarEquiv multiplier multiplier_norm p.1, clutching p.2)
  rotation_fixed_iff : ∀ k : ℕ, 0 < k → k < m → ∀ w : ComplexUnitDisc,
    (discScalarEquiv multiplier multiplier_norm ^ k) w = w ↔ w = discCenter
  action_continuous : ∀ g : FiniteCyclic m, Continuous (actionMap action g)
  radius_invariant : ∀ (g : FiniteCyclic m) (p : ComplexUnitDisc × T),
    ‖((actionMap action g p).1 : ℂ)‖ = ‖(p.1 : ℂ)‖

namespace CyclicPuncturedProductData

variable {m : ℕ} [NeZero m] {T : Type} [TopologicalSpace T] {r : ℝ}
    (D : CyclicPuncturedProductData m T r)

/-- The invariant punctured product on which the angular cyclic quotient is taken. -/
public noncomputable def carrier : InvariantOpenCarrier D.action where
  carrier := {p | 0 < ‖(p.1 : ℂ)‖ ∧ ‖(p.1 : ℂ)‖ < r}
  isOpen_carrier :=
    (isOpen_lt continuous_const
      (continuous_norm.comp (continuous_subtype_val.comp continuous_fst))).inter
    (isOpen_lt
      (continuous_norm.comp (continuous_subtype_val.comp continuous_fst)) continuous_const)
  invariant g p hp := by
    change 0 < ‖((actionMap D.action g p).1 : ℂ)‖ ∧
      ‖((actionMap D.action g p).1 : ℂ)‖ < r
    rw [D.radius_invariant]
    exact hp

end CyclicPuncturedProductData

namespace EstablishedCyclicAngularFundamentalDomain

/-- A free scalar cyclic action on a punctured disc, diagonal with a fibre homeomorphism, has
quotient equal to the radial interval times the corresponding mapping torus, provided its
generator rotates the disc clockwise by exactly one `m`-th of a full turn.

This is the general quotient/fundamental-domain theorem missing from Mathlib.  The mapping-torus
orientation uses the sector from the generator ray to the identity ray, so its clutching map is
`D.clutching` rather than its inverse.

The hypothesis `hmul` is not a normalisation convenience and must not be dropped: primitivity of
`D.multiplier` alone is *not* enough.  For a general primitive multiplier `exp (2 π I j / m)` the
angular fundamental sector still spans the angle `2 π / m`, so the group element gluing its two
ends is `g ^ (j⁻¹ mod m)` rather than `g`, and the quotient is the mapping torus of
`D.clutching ^ (j⁻¹ mod m)`.  That agrees with the mapping torus of `D.clutching` only when
`j ≡ ± 1 [MOD m]`, hence only for `m ∈ {1, 2, 3, 4, 6}`.

The unhypothesised form is refuted by `m = 5`, `j = 2`, with `T` a genus-two surface carrying the
free-away-from-branch-points `C₅`-action with branch data `(1, 1, 3)`: the branch multisets of
`φ`, `φ ^ 2` and `φ⁻¹` are `{1, 1, 3}`, `{1, 2, 2}` and `{2, 4, 4}`, so `φ ^ 2` is conjugate to
neither `φ` nor `φ⁻¹`; the two mapping tori then have non-isomorphic fundamental groups, and
their products with the radial interval remain non-homeomorphic.  All fields of
`CyclicPuncturedProductData` are satisfiable for that data.

Both collars of this paper have `multiplier = exp (-2 π I / m)`, that is `j = -1`, so `hmul`
holds for them by `CyclicAngularFundamentalDomain.orderThreeMultiplier_eq_standardMultiplier` and
`CyclicAngularFundamentalDomain.orderFourMultiplier_eq_standardMultiplier`. -/
public noncomputable def quotientHomeomorphRadialMappingTorus
    {m : ℕ} [NeZero m] {T : Type} [TopologicalSpace T] {r : ℝ}
    (D : CyclicPuncturedProductData m T r)
    (hmul : D.multiplier = CyclicAngularFundamentalDomain.standardMultiplier m) :
    Quotient (restrictedOrbitRel D.action D.carrier) ≃ₜ
      OpenRadialInterval r × CircleMappingTorus D.clutching :=
  CyclicAngularFundamentalDomain.quotientHomeomorphRadialMappingTorusOfStandardMultiplier
    D.action D.clutching D.radius_lt_one.le D.carrier rfl
    (CyclicAngularFundamentalDomain.isStandardGenerator_of_multiplier_eq D.action D.clutching
      D.multiplier D.multiplier_norm hmul D.generator_formula)
    D.action_continuous

end EstablishedCyclicAngularFundamentalDomain

namespace Geometry

open AnalyticTorusFamily EllipticActualActionTopology EllipticFamilySpecialization
open EllipticFixedPointCriterion EllipticLocalCoordinates
open EllipticPuncturedCollarGaugeHomeomorph EllipticRealPeriodProductTrivialization
open EllipticVaryingFamilyQuotient
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

variable {U : TriangleUniformization}

/-- The actual order-three diagonal product action, with all hypotheses of the general angular
fundamental-domain theorem discharged. -/
public noncomputable def orderThreeCyclicPuncturedProductData
    (F : PeriodFunctions U) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    CyclicPuncturedProductData 3
      (AdditiveTorus (parameterMap F U.zOne).1) r where
  radius_pos := hr
  radius_lt_one := hr1
  action := (orderThreeActionData F).diagonalAction
  clutching := orderThreeAffineClutchingHomeomorph F
  multiplier := orderThreeMultiplier
  multiplier_norm := norm_orderThreeMultiplier
  generator_formula p := by
    change (orderThreeActionData F).representation (cyclicGenerator 3) p = _
    rw [(orderThreeActionData F).representation_generator]
    rfl
  rotation_fixed_iff := orderThreeDiscRotation_fixed_iff
  action_continuous := orderThreeRepresentation_continuous F
  radius_invariant g p := by
    rw [cyclic_eq_generator_pow g]
    rw [actionMap.eq_def]
    change ‖(((orderThreeActionData F).representation
      (cyclicGenerator 3 ^ (Multiplicative.toAdd g).val) p).1 : ℂ)‖ = ‖(p.1 : ℂ)‖
    rw [map_pow, (orderThreeActionData F).representation_generator]
    change ‖((((orderThreeActionData F).diagonalGenerator ^
      (Multiplicative.toAdd g).val) p).1 : ℂ)‖ = ‖(p.1 : ℂ)‖
    rw [(orderThreeActionData F).diagonalGenerator_pow_apply]
    change ‖(((orderThreeDiscRotation ^ (Multiplicative.toAdd g).val) p.1 :
      ComplexUnitDisc) : ℂ)‖ = ‖(p.1 : ℂ)‖
    rw [orderThreeDiscRotation.eq_def,
      discScalarEquiv_pow_apply_val, norm_mul, norm_pow, norm_orderThreeMultiplier,
      one_pow, one_mul]

/-- The actual order-four diagonal product action, with all hypotheses of the general angular
fundamental-domain theorem discharged. -/
public noncomputable def orderFourCyclicPuncturedProductData
    (F : PeriodFunctions U) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    CyclicPuncturedProductData 4
      (AdditiveTorus (parameterMap F U.zTwo).1) r where
  radius_pos := hr
  radius_lt_one := hr1
  action := (orderFourActionData F).diagonalAction
  clutching := orderFourAffineClutchingHomeomorph F
  multiplier := orderFourMultiplier
  multiplier_norm := norm_orderFourMultiplier
  generator_formula p := by
    change (orderFourActionData F).representation (cyclicGenerator 4) p = _
    rw [(orderFourActionData F).representation_generator]
    rfl
  rotation_fixed_iff := orderFourDiscRotation_fixed_iff
  action_continuous := orderFourRepresentation_continuous F
  radius_invariant g p := by
    rw [cyclic_eq_generator_pow g]
    rw [actionMap.eq_def]
    change ‖(((orderFourActionData F).representation
      (cyclicGenerator 4 ^ (Multiplicative.toAdd g).val) p).1 : ℂ)‖ = ‖(p.1 : ℂ)‖
    rw [map_pow, (orderFourActionData F).representation_generator]
    change ‖((((orderFourActionData F).diagonalGenerator ^
      (Multiplicative.toAdd g).val) p).1 : ℂ)‖ = ‖(p.1 : ℂ)‖
    rw [(orderFourActionData F).diagonalGenerator_pow_apply]
    change ‖(((orderFourDiscRotation ^ (Multiplicative.toAdd g).val) p.1 :
      ComplexUnitDisc) : ℂ)‖ = ‖(p.1 : ℂ)‖
    rw [orderFourDiscRotation.eq_def,
      discScalarEquiv_pow_apply_val, norm_mul, norm_pow, norm_orderFourMultiplier,
      one_pow, one_mul]

/-- Product coordinates restricted to the punctured order-three collar. -/
public noncomputable def orderThreePuncturedProductHomeomorph
    (F : PeriodFunctions U) (hsource : U.sourceAction = fuchsianSourceAction)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (orderThreeAffinePuncturedCarrier F hsource r).carrier ≃ₜ
      (orderThreeCyclicPuncturedProductData F r hr hr1).carrier.carrier :=
  (orderThreeRealPeriodProductHomeomorph F).subtype fun q ↦ by
    change (0 < orderThreeFamilyRadius F q ∧ orderThreeFamilyRadius F q < r) ↔
      (0 < ‖((orderThreeRealPeriodProductHomeomorph F q).1 : ℂ)‖ ∧
        ‖((orderThreeRealPeriodProductHomeomorph F q).1 : ℂ)‖ < r)
    rw [orderThreeFamilyRadius_eq_productNorm]

/-- Product coordinates restricted to the punctured order-four collar. -/
public noncomputable def orderFourPuncturedProductHomeomorph
    (F : PeriodFunctions U) (hsource : U.sourceAction = fuchsianSourceAction)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (orderFourAffinePuncturedCarrier F hsource r).carrier ≃ₜ
      (orderFourCyclicPuncturedProductData F r hr hr1).carrier.carrier :=
  (orderFourRealPeriodProductHomeomorph F).subtype fun q ↦ by
    change (0 < orderFourFamilyRadius F q ∧ orderFourFamilyRadius F q < r) ↔
      (0 < ‖((orderFourRealPeriodProductHomeomorph F q).1 : ℂ)‖ ∧
        ‖((orderFourRealPeriodProductHomeomorph F q).1 : ℂ)‖ < r)
    rw [orderFourFamilyRadius_eq_productNorm]

/-- The restricted order-three product chart is equivariant for the actual affine action. -/
public noncomputable def orderThreePuncturedProductEquivariantHomeomorph
    (F : PeriodFunctions U) (hsource : U.sourceAction = fuchsianSourceAction)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    EquivariantOpenHomeomorphOfActions
      (orderThreeAffineFamilyAction F)
      (orderThreeCyclicPuncturedProductData F r hr hr1).action
      (orderThreeAffinePuncturedCarrier F hsource r)
      (orderThreeCyclicPuncturedProductData F r hr hr1).carrier where
  toHomeomorph := orderThreePuncturedProductHomeomorph F hsource r hr hr1
  equivariant g q := by
    apply Subtype.ext
    rw [orderThreePuncturedProductHomeomorph.eq_def]
    change orderThreeRealPeriodProductHomeomorph F
        (orderThreeAffineFamilyRepresentation F g q) =
      (orderThreeActionData F).representation g
        (orderThreeRealPeriodProductHomeomorph F q)
    exact orderThreeRealPeriodProductHomeomorph_equivariant F hsource g q

/-- The restricted order-four product chart is equivariant for the actual affine action. -/
public noncomputable def orderFourPuncturedProductEquivariantHomeomorph
    (F : PeriodFunctions U) (hsource : U.sourceAction = fuchsianSourceAction)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    EquivariantOpenHomeomorphOfActions
      (orderFourAffineFamilyAction F)
      (orderFourCyclicPuncturedProductData F r hr hr1).action
      (orderFourAffinePuncturedCarrier F hsource r)
      (orderFourCyclicPuncturedProductData F r hr hr1).carrier where
  toHomeomorph := orderFourPuncturedProductHomeomorph F hsource r hr hr1
  equivariant g q := by
    apply Subtype.ext
    rw [orderFourPuncturedProductHomeomorph.eq_def]
    change orderFourRealPeriodProductHomeomorph F
        (orderFourAffineFamilyRepresentation F g q) =
      (orderFourActionData F).representation g
        (orderFourRealPeriodProductHomeomorph F q)
    exact orderFourRealPeriodProductHomeomorph_equivariant F hsource g q

/-- The actual punctured order-three collar quotient reduced to the explicit diagonal product
quotient. -/
public noncomputable def orderThreePuncturedCollarProductQuotientHomeomorph
    (F : PeriodFunctions U) (hsource : U.sourceAction = fuchsianSourceAction)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction F)
      (orderThreeAffinePuncturedCarrier F hsource r)) ≃ₜ
      Quotient (restrictedOrbitRel
        (orderThreeCyclicPuncturedProductData F r hr hr1).action
        (orderThreeCyclicPuncturedProductData F r hr hr1).carrier) :=
  restrictedOrbitQuotientHomeomorph
    (orderThreePuncturedProductEquivariantHomeomorph F hsource r hr hr1)

/-- The actual punctured order-four collar quotient reduced to the explicit diagonal product
quotient. -/
public noncomputable def orderFourPuncturedCollarProductQuotientHomeomorph
    (F : PeriodFunctions U) (hsource : U.sourceAction = fuchsianSourceAction)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Quotient (restrictedOrbitRel (orderFourAffineFamilyAction F)
      (orderFourAffinePuncturedCarrier F hsource r)) ≃ₜ
      Quotient (restrictedOrbitRel
        (orderFourCyclicPuncturedProductData F r hr hr1).action
        (orderFourCyclicPuncturedProductData F r hr hr1).carrier) :=
  restrictedOrbitQuotientHomeomorph
    (orderFourPuncturedProductEquivariantHomeomorph F hsource r hr hr1)

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- Correct radial-mapping-torus model of the actual order-three open collar. -/
public noncomputable def orderThreeCollarRadialMappingTorusHomeomorph :
    A.starCollarSourceType 1 ≃ₜ
      OpenRadialInterval A.starSeparation.orderThree.radius ×
        CircleMappingTorus (orderThreeAffineClutchingHomeomorph A.periods) := by
  let D := orderThreeCyclicPuncturedProductData A.periods
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one
  have hclutch : D.clutching = orderThreeAffineClutchingHomeomorph A.periods := rfl
  rw [← hclutch]
  exact (orderThreePuncturedCollarProductQuotientHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one).trans
      (EstablishedCyclicAngularFundamentalDomain.quotientHomeomorphRadialMappingTorus D
        CyclicAngularFundamentalDomain.orderThreeMultiplier_eq_standardMultiplier)

/-- Correct radial-mapping-torus model of the actual order-four open collar. -/
public noncomputable def orderFourCollarRadialMappingTorusHomeomorph :
    A.starCollarSourceType 2 ≃ₜ
      OpenRadialInterval A.starSeparation.orderFour.radius ×
        CircleMappingTorus (orderFourAffineClutchingHomeomorph A.periods) := by
  let D := orderFourCyclicPuncturedProductData A.periods
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one
  have hclutch : D.clutching = orderFourAffineClutchingHomeomorph A.periods := rfl
  rw [← hclutch]
  exact (orderFourPuncturedCollarProductQuotientHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one).trans
      (EstablishedCyclicAngularFundamentalDomain.quotientHomeomorphRadialMappingTorus D
        CyclicAngularFundamentalDomain.orderFourMultiplier_eq_standardMultiplier)

end PaperAnalyticData

end Geometry

end SphereSixComplex
