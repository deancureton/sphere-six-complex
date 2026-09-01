module

public import SphereSixComplex.Topology.PaperSectionSevenAffineActualCuspCrossingCayleySeparation

/-!
# The marked-band radius obstruction

The separation-data interface is stable under shrinking its two elliptic radii.  Consequently it
does not force the identity sheets at the pinned crossing to enter the selected collars: there
are valid simultaneous separation data whose radii are smaller than the corresponding positive
pinned Cayley norms.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.EllipticCayleyHomeomorph

/-- Simultaneous collar separation alone cannot force the two pinned identity-sheet bounds.
Indeed, any valid separation datum can be shrunk so that both bounds fail strictly. -/
public theorem CollarSeparationData.exists_shrink_excluding_pinned_identity_sheets
    {A : PaperAnalyticData}
    (S : A.CollarSeparationData A.actualPuncturedCuspWitness) :
    ∃ S' : A.CollarSeparationData A.actualPuncturedCuspWitness,
      S'.orderThree.radius <
          ‖(orderThreeCayleyHomeomorph
            (A.sectionSevenAffineOrderThreeRadialBaseLift
              A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ)‖ ∧
        S'.orderFour.radius <
          ‖(orderFourCayleyHomeomorph
            (A.sectionSevenAffineOrderFourRadialBaseLift
              A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ)‖ := by
  let c₃ := ‖(orderThreeCayleyHomeomorph
    (A.sectionSevenAffineOrderThreeRadialBaseLift
      A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ)‖
  let c₄ := ‖(orderFourCayleyHomeomorph
    (A.sectionSevenAffineOrderFourRadialBaseLift
      A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ)‖
  let r₃ := min (S.orderThree.radius / 2) (c₃ / 2)
  let r₄ := min (S.orderFour.radius / 2) (c₄ / 2)
  have hc₃ : 0 < c₃ := A.sectionSevenAffineOrderThreePinnedCayley_norm_pos
  have hc₄ : 0 < c₄ := A.sectionSevenAffineOrderFourPinnedCayley_norm_pos
  have hr₃ : 0 < r₃ := lt_min (half_pos S.orderThree.radius_pos) (half_pos hc₃)
  have hr₄ : 0 < r₄ := lt_min (half_pos S.orderFour.radius_pos) (half_pos hc₄)
  let P₃ : A.OrderThreeFillingPiece :=
    { radius := r₃
      radius_pos := hr₃
      radius_lt_one := (min_le_left _ _).trans_lt
        ((half_lt_self S.orderThree.radius_pos).trans S.orderThree.radius_lt_one)
      sourceData := A.orderThreeLinearCollarSourceData_mono
        ((min_le_left _ _).trans (half_le_self S.orderThree.radius_pos.le))
        S.orderThree.sourceData }
  let P₄ : A.OrderFourFillingPiece :=
    { radius := r₄
      radius_pos := hr₄
      radius_lt_one := (min_le_left _ _).trans_lt
        ((half_lt_self S.orderFour.radius_pos).trans S.orderFour.radius_lt_one)
      sourceData := A.orderFourLinearCollarSourceData_mono
        ((min_le_left _ _).trans (half_le_self S.orderFour.radius_pos.le))
        S.orderFour.sourceData }
  let S' : A.CollarSeparationData A.actualPuncturedCuspWitness :=
    { orderThree := P₃
      orderFour := P₄
      orderThree_avoids_cusp := fun z hz ↦
        S.orderThree_avoids_cusp z
          (hz.trans_le ((min_le_left _ _).trans (half_le_self S.orderThree.radius_pos.le)))
      orderFour_avoids_cusp := fun z hz ↦
        S.orderFour_avoids_cusp z
          (hz.trans_le ((min_le_left _ _).trans (half_le_self S.orderFour.radius_pos.le)))
      orderThree_coordinate_bound := fun z hz ↦
        S.orderThree_coordinate_bound z
          (hz.trans_le ((min_le_left _ _).trans (half_le_self S.orderThree.radius_pos.le)))
      orderFour_coordinate_bound := fun z hz ↦
        S.orderFour_coordinate_bound z
          (hz.trans_le ((min_le_left _ _).trans (half_le_self S.orderFour.radius_pos.le)))
      elliptic_orbits_disjoint := fun z x hz hx g ↦
        S.elliptic_orbits_disjoint z x
          (hz.trans_le ((min_le_left _ _).trans (half_le_self S.orderThree.radius_pos.le)))
          (hx.trans_le ((min_le_left _ _).trans (half_le_self S.orderFour.radius_pos.le))) g }
  refine ⟨S', ?_, ?_⟩
  · exact (min_le_right _ _).trans_lt (half_lt_self hc₃)
  · exact (min_le_right _ _).trans_lt (half_lt_self hc₄)

/-- In particular, the selected simultaneous separation datum admits another fully valid choice
for which neither pinned identity sheet enters its elliptic collar. -/
public theorem exists_collarSeparationData_excluding_pinned_identity_sheets
    (A : PaperAnalyticData) :
    ∃ S : A.CollarSeparationData A.actualPuncturedCuspWitness,
      S.orderThree.radius <
          ‖(orderThreeCayleyHomeomorph
            (A.sectionSevenAffineOrderThreeRadialBaseLift
              A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ)‖ ∧
        S.orderFour.radius <
          ‖(orderFourCayleyHomeomorph
            (A.sectionSevenAffineOrderFourRadialBaseLift
              A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ)‖ :=
  A.starSeparation.exists_shrink_excluding_pinned_identity_sheets

end SphereSixComplex.Geometry.PaperAnalyticData

end
