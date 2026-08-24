module

public import SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
public import SphereSixComplex.Geometry.PaperOpenEmbeddingStar
public import SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction

/-!
# Real-period radial charts for the actual elliptic fillings

The unconditional real-period product trivialization restricts to the selected varying filling,
with image exactly the corresponding radial product ball. Its affine equivariance transports the
fixed-product radial deformation retraction to the actual order-three and order-four fillings.
-/

namespace SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial

open scoped ContinuousMap
open Set SphereSixComplex.Geometry SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open _root_.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction

noncomputable section

variable (A : PaperAnalyticData) (r : ℝ)

/-- The whole-family order-three product chart restricted to the radius-`r` filling. -/
@[expose] public def orderThreeFillingProductMap :
    A.orderThreeFillingOpen r →
      ComplexUnitDisc × A.orderThreeTorus :=
  fun q ↦ orderThreeRealPeriodProductHomeomorph A.periods q.1

/-- The whole-family order-four product chart restricted to the radius-`r` filling. -/
@[expose] public def orderFourFillingProductMap :
    A.orderFourFillingOpen r →
      ComplexUnitDisc × A.orderFourTorus :=
  fun q ↦ orderFourRealPeriodProductHomeomorph A.periods q.1

public theorem orderThreeFillingProductMap_isOpenEmbedding :
    IsOpenEmbedding (orderThreeFillingProductMap A r) :=
  (orderThreeRealPeriodProductHomeomorph A.periods).isOpenEmbedding.comp
    (A.orderThreeFillingOpen r).2.isOpenEmbedding_subtypeVal

public theorem orderFourFillingProductMap_isOpenEmbedding :
    IsOpenEmbedding (orderFourFillingProductMap A r) :=
  (orderFourRealPeriodProductHomeomorph A.periods).isOpenEmbedding.comp
    (A.orderFourFillingOpen r).2.isOpenEmbedding_subtypeVal

public theorem orderThreeFillingProductMap_equivariant
    (g : FiniteCyclic 3) (x : A.orderThreeFillingOpen r) :
    orderThreeFillingProductMap A r
        (actionMap (A.orderThreeFillingAction r) g x) =
      actionMap (orderThreeActionData A.periods).diagonalAction g
        (orderThreeFillingProductMap A r x) := by
  exact orderThreeRealPeriodProductHomeomorph_equivariant A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction g x

public theorem orderFourFillingProductMap_equivariant
    (g : FiniteCyclic 4) (x : A.orderFourFillingOpen r) :
    orderFourFillingProductMap A r
        (actionMap (A.orderFourFillingAction r) g x) =
      actionMap (orderFourActionData A.periods).diagonalAction g
        (orderFourFillingProductMap A r x) := by
  exact orderFourRealPeriodProductHomeomorph_equivariant A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction g x

/-- The image of the actual order-three filling is exactly the radial product ball. -/
public theorem orderThreeFillingProductMap_range :
    Set.range (orderThreeFillingProductMap A r) =
      {p | ‖(p.1 : ℂ)‖ < r} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    have hq := q.property
    change orderThreeFamilyRadius A.periods q.1 < r at hq
    rwa [orderThreeFamilyRadius_eq_productNorm] at hq
  · intro hp
    let q := (orderThreeRealPeriodProductHomeomorph A.periods).symm p
    have hq : orderThreeFamilyRadius A.periods q < r := by
      rw [orderThreeFamilyRadius_eq_productNorm]
      rw [(orderThreeRealPeriodProductHomeomorph A.periods).apply_symm_apply]
      exact hp
    refine ⟨⟨q, hq⟩, ?_⟩
    exact (orderThreeRealPeriodProductHomeomorph A.periods).apply_symm_apply p

/-- The image of the actual order-four filling is exactly the radial product ball. -/
public theorem orderFourFillingProductMap_range :
    Set.range (orderFourFillingProductMap A r) =
      {p | ‖(p.1 : ℂ)‖ < r} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    have hq := q.property
    change orderFourFamilyRadius A.periods q.1 < r at hq
    rwa [orderFourFamilyRadius_eq_productNorm] at hq
  · intro hp
    let q := (orderFourRealPeriodProductHomeomorph A.periods).symm p
    have hq : orderFourFamilyRadius A.periods q < r := by
      rw [orderFourFamilyRadius_eq_productNorm]
      rw [(orderFourRealPeriodProductHomeomorph A.periods).apply_symm_apply]
      exact hp
    refine ⟨⟨q, hq⟩, ?_⟩
    exact (orderFourRealPeriodProductHomeomorph A.periods).apply_symm_apply p

public theorem orderThreeFillingOpen_nonempty (hr : 0 < r) :
    Nonempty (A.orderThreeFillingOpen r) := by
  let p : ComplexUnitDisc × A.orderThreeTorus := (discCenter, 0)
  let q := (orderThreeRealPeriodProductHomeomorph A.periods).symm p
  refine ⟨⟨q, ?_⟩⟩
  change orderThreeFamilyRadius A.periods q < r
  rw [orderThreeFamilyRadius_eq_productNorm]
  rw [(orderThreeRealPeriodProductHomeomorph A.periods).apply_symm_apply]
  simpa [p, discCenter] using hr

public theorem orderFourFillingOpen_nonempty (hr : 0 < r) :
    Nonempty (A.orderFourFillingOpen r) := by
  let p : ComplexUnitDisc × A.orderFourTorus := (discCenter, 0)
  let q := (orderFourRealPeriodProductHomeomorph A.periods).symm p
  refine ⟨⟨q, ?_⟩⟩
  change orderFourFamilyRadius A.periods q < r
  rw [orderFourFamilyRadius_eq_productNorm]
  rw [(orderFourRealPeriodProductHomeomorph A.periods).apply_symm_apply]
  simpa [p, discCenter] using hr

/-- Exact whole-filling chart for the actual order-three varying family. -/
@[expose] public def orderThreeRadialWholeFillingChart
    (hr : 0 < r) (hr1 : r < 1) :
    RadialWholeFillingChart (A.orderThreeFillingOpen r)
      (orderThreeRadialActionData A.periods) r := by
  let _ : Nonempty (A.orderThreeFillingOpen r) := orderThreeFillingOpen_nonempty A r hr
  let f := orderThreeFillingProductMap A r
  let hf := orderThreeFillingProductMap_isOpenEmbedding A r
  exact
    { radius_pos := hr
      radius_lt_one := hr1
      gluing := hf.toOpenPartialHomeomorph f
      source_eq_univ := IsOpenEmbedding.toOpenPartialHomeomorph_source f hf
      target_eq_ball := by
        rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
        exact orderThreeFillingProductMap_range A r }

/-- Exact whole-filling chart for the actual order-four varying family. -/
@[expose] public def orderFourRadialWholeFillingChart
    (hr : 0 < r) (hr1 : r < 1) :
    RadialWholeFillingChart (A.orderFourFillingOpen r)
      (orderFourRadialActionData A.periods) r := by
  let _ : Nonempty (A.orderFourFillingOpen r) := orderFourFillingOpen_nonempty A r hr
  let f := orderFourFillingProductMap A r
  let hf := orderFourFillingProductMap_isOpenEmbedding A r
  exact
    { radius_pos := hr
      radius_lt_one := hr1
      gluing := hf.toOpenPartialHomeomorph f
      source_eq_univ := IsOpenEmbedding.toOpenPartialHomeomorph_source f hf
      target_eq_ball := by
        rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
        exact orderFourFillingProductMap_range A r }

@[simp]
public theorem orderThreeRadialWholeFillingChart_apply_fst_val
    (hr : 0 < r) (hr1 : r < 1) (x : A.orderThreeFillingOpen r) :
    (((orderThreeRadialWholeFillingChart A r hr hr1).toProductHomeomorph x).1 : ℂ) =
      (orderThreeFillingProductMap A r x).1.1 / (r : ℂ) := rfl

@[simp]
public theorem orderThreeRadialWholeFillingChart_apply_snd
    (hr : 0 < r) (hr1 : r < 1) (x : A.orderThreeFillingOpen r) :
    ((orderThreeRadialWholeFillingChart A r hr hr1).toProductHomeomorph x).2 =
      (orderThreeFillingProductMap A r x).2 := rfl

@[simp]
public theorem orderFourRadialWholeFillingChart_apply_fst_val
    (hr : 0 < r) (hr1 : r < 1) (x : A.orderFourFillingOpen r) :
    (((orderFourRadialWholeFillingChart A r hr hr1).toProductHomeomorph x).1 : ℂ) =
      (orderFourFillingProductMap A r x).1.1 / (r : ℂ) := rfl

@[simp]
public theorem orderFourRadialWholeFillingChart_apply_snd
    (hr : 0 < r) (hr1 : r < 1) (x : A.orderFourFillingOpen r) :
    ((orderFourRadialWholeFillingChart A r hr hr1).toProductHomeomorph x).2 =
      (orderFourFillingProductMap A r x).2 := rfl

/-- The actual order-three varying filling has the action-correct radial product chart. -/
@[expose] public def orderThreeAffineRadialCompatibility
    (hr : 0 < r) (hr1 : r < 1) :
    OrderThreeAffineRadialWholeFillingCompatibility A r where
  chart := orderThreeRadialWholeFillingChart A r hr hr1
  equivariant := by
    intro g x
    apply Prod.ext
    · apply Subtype.ext
      simp only [orderThreeRadialWholeFillingChart_apply_fst_val]
      rw [orderThreeFillingProductMap_equivariant]
      change ((orderThreeActionData A.periods).representation g
          (orderThreeFillingProductMap A r x)).1.1 / (r : ℂ) =
        ((orderThreeActionData A.periods).representation g
          ((orderThreeRadialWholeFillingChart A r hr hr1).toProductHomeomorph x)).1.1
      rw [cyclic_eq_generator_pow g, map_pow,
        (orderThreeActionData A.periods).representation_generator]
      rw [(orderThreeActionData A.periods).diagonalGenerator_pow_apply,
        (orderThreeActionData A.periods).diagonalGenerator_pow_apply]
      change ((orderThreeDiscRotation ^ (Multiplicative.toAdd g).val)
          (orderThreeFillingProductMap A r x).1).1 / (r : ℂ) =
        ((orderThreeDiscRotation ^ (Multiplicative.toAdd g).val)
          ((orderThreeRadialWholeFillingChart A r hr hr1).toProductHomeomorph x).1).1
      rw [show orderThreeDiscRotation =
          discScalarEquiv orderThreeMultiplier norm_orderThreeMultiplier from rfl,
        discScalarEquiv_pow_apply_val, discScalarEquiv_pow_apply_val,
        orderThreeRadialWholeFillingChart_apply_fst_val]
      ring
    · simp only [orderThreeRadialWholeFillingChart_apply_snd]
      rw [orderThreeFillingProductMap_equivariant]
      change ((orderThreeActionData A.periods).representation g
          (orderThreeFillingProductMap A r x)).2 =
        ((orderThreeActionData A.periods).representation g
          ((orderThreeRadialWholeFillingChart A r hr hr1).toProductHomeomorph x)).2
      rw [cyclic_eq_generator_pow g, map_pow,
        (orderThreeActionData A.periods).representation_generator]
      simp only [(orderThreeActionData A.periods).diagonalGenerator_pow_apply,
        orderThreeRadialWholeFillingChart_apply_snd]

/-- The actual order-four varying filling has the action-correct radial product chart. -/
@[expose] public def orderFourAffineRadialCompatibility
    (hr : 0 < r) (hr1 : r < 1) :
    OrderFourAffineRadialWholeFillingCompatibility A r where
  chart := orderFourRadialWholeFillingChart A r hr hr1
  equivariant := by
    intro g x
    apply Prod.ext
    · apply Subtype.ext
      simp only [orderFourRadialWholeFillingChart_apply_fst_val]
      rw [orderFourFillingProductMap_equivariant]
      change ((orderFourActionData A.periods).representation g
          (orderFourFillingProductMap A r x)).1.1 / (r : ℂ) =
        ((orderFourActionData A.periods).representation g
          ((orderFourRadialWholeFillingChart A r hr hr1).toProductHomeomorph x)).1.1
      rw [cyclic_eq_generator_pow g, map_pow,
        (orderFourActionData A.periods).representation_generator]
      rw [(orderFourActionData A.periods).diagonalGenerator_pow_apply,
        (orderFourActionData A.periods).diagonalGenerator_pow_apply]
      change ((orderFourDiscRotation ^ (Multiplicative.toAdd g).val)
          (orderFourFillingProductMap A r x).1).1 / (r : ℂ) =
        ((orderFourDiscRotation ^ (Multiplicative.toAdd g).val)
          ((orderFourRadialWholeFillingChart A r hr hr1).toProductHomeomorph x).1).1
      rw [show orderFourDiscRotation =
          discScalarEquiv orderFourMultiplier norm_orderFourMultiplier from rfl,
        discScalarEquiv_pow_apply_val, discScalarEquiv_pow_apply_val,
        orderFourRadialWholeFillingChart_apply_fst_val]
      ring
    · simp only [orderFourRadialWholeFillingChart_apply_snd]
      rw [orderFourFillingProductMap_equivariant]
      change ((orderFourActionData A.periods).representation g
          (orderFourFillingProductMap A r x)).2 =
        ((orderFourActionData A.periods).representation g
          ((orderFourRadialWholeFillingChart A r hr hr1).toProductHomeomorph x)).2
      rw [cyclic_eq_generator_pow g, map_pow,
        (orderFourActionData A.periods).representation_generator]
      simp only [(orderFourActionData A.periods).diagonalGenerator_pow_apply,
        orderFourRadialWholeFillingChart_apply_snd]

/-- The order-three radial compatibility at the radius selected by the paper's star data. -/
@[expose] public def orderThreeSelectedAffineRadialCompatibility (A : PaperAnalyticData) :
    OrderThreeAffineRadialWholeFillingCompatibility A
      A.starSeparation.orderThree.radius :=
  orderThreeAffineRadialCompatibility A A.starSeparation.orderThree.radius
    A.starSeparation.orderThree.radius_pos A.starSeparation.orderThree.radius_lt_one

/-- The order-four radial compatibility at the radius selected by the paper's star data. -/
@[expose] public def orderFourSelectedAffineRadialCompatibility (A : PaperAnalyticData) :
    OrderFourAffineRadialWholeFillingCompatibility A
      A.starSeparation.orderFour.radius :=
  orderFourAffineRadialCompatibility A A.starSeparation.orderFour.radius
    A.starSeparation.orderFour.radius_pos A.starSeparation.orderFour.radius_lt_one

/-- The selected actual order-three filling retracts, up to homotopy, to its reduced central
bielliptic fibre. -/
@[expose] public def orderThreeSelectedFillingHomotopyEquivCentralFiber
    (A : PaperAnalyticData) :
    A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius ≃ₕ
      OrderThreeReducedCentralFiber A.periods :=
  orderThreeVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart A
    A.starSeparation.orderThree.radius (orderThreeSelectedAffineRadialCompatibility A)

/-- The selected actual order-four filling retracts, up to homotopy, to its reduced central
bielliptic fibre. -/
@[expose] public def orderFourSelectedFillingHomotopyEquivCentralFiber
    (A : PaperAnalyticData) :
    A.OrderFourVaryingFilling A.starSeparation.orderFour.radius ≃ₕ
      OrderFourReducedCentralFiber A.periods :=
  orderFourVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart A
    A.starSeparation.orderFour.radius (orderFourSelectedAffineRadialCompatibility A)

/-- Integral singular chains of the selected actual order-three filling and central fibre are
chain-homotopy equivalent. -/
@[expose] public def orderThreeSelectedFillingSingularChainHomotopyEquiv
    (A : PaperAnalyticData) :=
  orderThreeVaryingFillingSingularChainHomotopyEquiv_of_affineRadialChart A
    A.starSeparation.orderThree.radius (orderThreeSelectedAffineRadialCompatibility A)

/-- Integral singular chains of the selected actual order-four filling and central fibre are
chain-homotopy equivalent. -/
@[expose] public def orderFourSelectedFillingSingularChainHomotopyEquiv
    (A : PaperAnalyticData) :=
  orderFourVaryingFillingSingularChainHomotopyEquiv_of_affineRadialChart A
    A.starSeparation.orderFour.radius (orderFourSelectedAffineRadialCompatibility A)

end

end SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
