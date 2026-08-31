module

public import SphereSixComplex.Geometry.PaperOpenEmbeddingStarNonempty
public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderFourNamedSheetStabilizerReduction

/-!
# One-entry separation for the order-four Cayley collar

The selected star-separation datum controls a deck transformation when both a point and its
translate lie in the order-four Cayley collar.  This file records the exact implication and shows
that membership of the translate alone cannot force the deck transformation into the order-four
stabilizer, even when the translate lies in the punctured collar.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.TriangleGroup

/-- Once a deck translate lies in the selected order-four collar, the deck transformation fixes
the order-four centre exactly when the source point lies in that collar too. -/
public theorem orderFour_deck_fixes_center_iff_source_cayley_lt_of_target_cayley_lt
    (A : PaperAnalyticData) (z : UpperHalfPlane) (g : Delta)
    (htarget : ‖(orderFourCayleyHomeomorph (fuchsianSourceAction g • z) : ℂ)‖ <
      A.starSeparation.orderFour.radius) :
    fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint ↔
      ‖(orderFourCayleyHomeomorph z : ℂ)‖ < A.starSeparation.orderFour.radius := by
  constructor
  · intro hfix
    rw [← orderFourCayleyHomeomorph_norm_eq_of_fix_fuchsianTwo g z hfix]
    exact htarget
  · intro hsourceSmall
    apply (establishedFuchsianTwoStabilizerExact g).mpr
    let U := A.modular.modularParameter.toTriangleUniformization
    have hsource : U.sourceAction = fuchsianSourceAction :=
      A.modular.modularParameter.toTriangleUniformization_sourceAction
    have D := A.starSeparation.orderFour.sourceData
    rw [OrderFourLinearCollarSourceData.eq_def] at D
    exact D.2 (fuchsianSourceAction g • z) z htarget hsourceSmall g (by rw [hsource])

/-- Target membership alone cannot imply order-four stabilizer membership.  For the order-three
generator, an inverse translate of any point in the selected punctured order-four collar is a
counterexample. -/
public theorem exists_nonstabilizer_deck_entering_orderFourPuncturedCayleyCollar
    (A : PaperAnalyticData) :
    ∃ (z : UpperHalfPlane) (g : Delta),
      0 < ‖(orderFourCayleyHomeomorph (fuchsianSourceAction g • z) : ℂ)‖ ∧
      ‖(orderFourCayleyHomeomorph (fuchsianSourceAction g • z) : ℂ)‖ <
        A.starSeparation.orderFour.radius ∧
      fuchsianSourceAction g • fuchsianTwoFixedPoint ≠ fuchsianTwoFixedPoint := by
  obtain ⟨q⟩ := A.orderFourAffinePuncturedCarrier_nonempty
    A.starSeparation.orderFour.radius
    A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one
  let y := familyTotalSpaceBase A.periods q.1
  have hcancel : fuchsianSourceAction g₁ • (fuchsianSourceAction g₁⁻¹ • y) = y := by
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have hq := q.property
  change 0 < orderFourFamilyRadius A.periods q.1 ∧
    orderFourFamilyRadius A.periods q.1 < A.starSeparation.orderFour.radius at hq
  refine ⟨fuchsianSourceAction g₁⁻¹ • y, g₁, ?_, ?_, ?_⟩
  · rw [hcancel]
    simpa only [orderFourFamilyRadius.eq_def, y] using hq.1
  · rw [hcancel]
    simpa only [orderFourFamilyRadius.eq_def, y] using hq.2
  · intro hfix
    exact orderFourCayleyHomeomorph_norm_not_invariant_under_gOne
      (orderFourCayleyHomeomorph_norm_eq_of_fix_fuchsianTwo
        g₁ fuchsianTwoFixedPoint hfix)

end SphereSixComplex.Geometry.PaperAnalyticData

end
