module
public import SphereSixComplex.Elliptic.Band.OverlapInterleaving

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.AnalyticData
open Set SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph

public theorem exists_small_discRegion_subset_orderThreeOverlap (A : AnalyticData) :
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

public theorem exists_small_discRegion_subset_orderFourOverlap (A : AnalyticData) :
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

/-- A fixed small affine disc contained in the actual order-three star overlap. -/
public noncomputable def affineOrderThreeMarkedDiscRadius (A : AnalyticData) : ℝ :=
  A.exists_small_discRegion_subset_orderThreeOverlap.choose

public theorem affineOrderThreeMarkedDiscRadius_spec (A : AnalyticData) :
    0 < A.affineOrderThreeMarkedDiscRadius ∧
      A.affineOrderThreeMarkedDiscRadius ≤ 1 / 3 ∧
      A.affineOrderThreeDiscRegion
          A.affineOrderThreeMarkedDiscRadius ⊆
        A.orderThreeFillingImage ∩
          A.affineOrderThreeCentralRegion :=
  by
    have h := A.exists_small_discRegion_subset_orderThreeOverlap.choose_spec
    exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- A fixed small affine disc contained in the actual order-four star overlap. -/
public noncomputable def affineOrderFourMarkedDiscRadius (A : AnalyticData) : ℝ :=
  A.exists_small_discRegion_subset_orderFourOverlap.choose

public theorem affineOrderFourMarkedDiscRadius_spec (A : AnalyticData) :
    0 < A.affineOrderFourMarkedDiscRadius ∧
      A.affineOrderFourMarkedDiscRadius ≤ 1 / 3 ∧
      A.affineOrderFourDiscRegion
          A.affineOrderFourMarkedDiscRadius ⊆
        A.orderFourFillingImage ∩
          A.affineOrderFourCentralRegion :=
  by
    have h := A.exists_small_discRegion_subset_orderFourOverlap.choose_spec
    exact ⟨h.1, h.2.1, h.2.2.1⟩

public theorem affineOrderThreeMarkedDiscRadius_cayley (A : AnalyticData)
    (z : UpperHalfPlane)
    (hz : ‖A.modular.sourceCoordinate.coordinate z‖ < A.affineOrderThreeMarkedDiscRadius) :
    ∃ k : SphereSixComplex.TriangleGroup.Delta,
      ‖(SphereSixComplex.Geometry.EllipticCayleyHomeomorph.orderThreeCayleyHomeomorph
        (SphereSixComplex.TriangleGroup.fuchsianSourceAction k • z) : ℂ)‖ <
        A.starSeparation.orderThree.radius / 2 :=
  A.exists_small_discRegion_subset_orderThreeOverlap.choose_spec.2.2.2 z hz

public theorem affineOrderFourMarkedDiscRadius_cayley (A : AnalyticData)
    (z : UpperHalfPlane)
    (hz : ‖A.modular.sourceCoordinate.coordinate z - 1‖ < A.affineOrderFourMarkedDiscRadius) :
    ∃ k : SphereSixComplex.TriangleGroup.Delta,
      ‖(SphereSixComplex.Geometry.EllipticCayleyHomeomorph.orderFourCayleyHomeomorph
        (SphereSixComplex.TriangleGroup.fuchsianSourceAction k • z) : ℂ)‖ <
        A.starSeparation.orderFour.radius / 2 :=
  A.exists_small_discRegion_subset_orderFourOverlap.choose_spec.2.2.2 z hz

end SphereSixComplex.Geometry.AnalyticData
