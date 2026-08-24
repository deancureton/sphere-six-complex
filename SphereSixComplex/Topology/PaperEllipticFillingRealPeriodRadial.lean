module

public import SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
public import SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction

/-!
# Real-period radial charts for the actual elliptic fillings

The unconditional real-period product trivialization restricts to the selected varying filling,
with image exactly the corresponding radial product ball. Its affine equivariance transports the
fixed-product radial deformation retraction to the actual order-three and order-four fillings.
-/

namespace SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial

open Set SphereSixComplex.Geometry SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open _root_.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
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

end

end SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
