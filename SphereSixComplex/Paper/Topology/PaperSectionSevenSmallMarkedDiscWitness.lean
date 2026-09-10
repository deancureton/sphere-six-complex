module
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineOverlapInterleaving
public import SphereSixComplex.Paper.Geometry.PaperCentralEndCover

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.PaperAnalyticData
open Set SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph

public theorem exists_small_discRegion_subset_orderThreeOverlap (A : PaperAnalyticData) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 3 ∧
      A.affineOrderThreeDiscRegion r ⊆
        A.orderThreeFillingImage ∩ A.affineOrderThreeCentralRegion ∧
      ∀ z : UpperHalfPlane, ‖A.modular.sourceCoordinate.coordinate z‖ < r →
        ∃ k : Delta, ‖(orderThreeCayleyHomeomorph
          (fuchsianSourceAction k • z) : ℂ)‖ < A.starSeparation.orderThree.radius / 2 := by
  obtain ⟨r₀, hr₀, hr₃, hsub⟩ := A.exists_discRegion_subset_orderThreeOverlap
  obtain ⟨δ, hδ, hcoordinate⟩ := A.exists_orderThree_coordinate_radius
    (A.starSeparation.orderThree.radius / 2) (half_pos A.starSeparation.orderThree.radius_pos)
  refine ⟨min r₀ (δ / 2), lt_min hr₀ (half_pos hδ),
    (min_le_left _ _).trans hr₃, (A.discRegion_mono (min_le_left _ _)).trans hsub, ?_⟩
  intro z hz
  apply hcoordinate z
  exact hz.trans ((min_le_right _ _).trans_lt (half_lt_self hδ))

public theorem exists_small_discRegion_subset_orderFourOverlap (A : PaperAnalyticData) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 3 ∧
      A.affineOrderFourDiscRegion r ⊆
        A.orderFourFillingImage ∩ A.affineOrderFourCentralRegion ∧
      ∀ z : UpperHalfPlane, ‖A.modular.sourceCoordinate.coordinate z - 1‖ < r →
        ∃ k : Delta, ‖(orderFourCayleyHomeomorph
          (fuchsianSourceAction k • z) : ℂ)‖ < A.starSeparation.orderFour.radius / 2 := by
  obtain ⟨r₀, hr₀, hr₃, hsub⟩ := A.exists_discRegion_subset_orderFourOverlap
  obtain ⟨δ, hδ, hcoordinate⟩ := A.exists_orderFour_coordinate_radius
    (A.starSeparation.orderFour.radius / 2) (half_pos A.starSeparation.orderFour.radius_pos)
  refine ⟨min r₀ (δ / 2), lt_min hr₀ (half_pos hδ),
    (min_le_left _ _).trans hr₃, (A.orderFourDiscRegion_mono (min_le_left _ _)).trans hsub, ?_⟩
  intro z hz
  apply hcoordinate z
  exact hz.trans ((min_le_right _ _).trans_lt (half_lt_self hδ))

end SphereSixComplex.Geometry.PaperAnalyticData
