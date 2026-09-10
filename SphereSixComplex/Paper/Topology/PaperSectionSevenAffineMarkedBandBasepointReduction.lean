module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineNamedSheetCompletion

/-!
# Basepoint reduction for the affine marked-band homotopies

The deck coset carrying the named radial lift into either elliptic collar is locally constant on
the connected affine strip.  Hence the remaining marked-band homotopies follow from the two
stabilizing-sheet assertions at the pinned actual-cusp crossing.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

/-- The marked affine band in its pinned strip-by-torus coordinates. -/
public noncomputable def affineMarkedBandProductHomeomorph
    (A : PaperAnalyticData) :
    A.affineMarkedBand ≃ₜ
      affineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter := by
  change
    ((A.affineCentralHeightSplit
        A.affineCentralSeparation).allocation.orderThreeSide ∩
      (A.affineCentralHeightSplit
        A.affineCentralSeparation).allocation.orderFourSide :
        Set A.ellipticInterior) ≃ₜ _
  exact
    (A.affineCentralHeightSplit A.affineCentralSeparation)
      |>.sidesIntersectionHomeomorph |>.trans
        (A.affineCentralBandMarkedProductHomeomorph
          A.affineCentralSeparation)

/-- A marked-band point over a prescribed point of the affine strip, with zero fibre
coordinate. -/
public noncomputable def affineMarkedBandPointOfStrip
    (A : PaperAnalyticData) (z : affineVerticalStrip) :
    A.affineMarkedBand :=
  A.affineMarkedBandProductHomeomorph.symm (z, 0)

@[simp]
public theorem affineBandStripCoordinate_markedBandPointOfStrip
    (A : PaperAnalyticData) (z : affineVerticalStrip) :
    A.affineBandStripCoordinate
        (A.affineMarkedBandPointOfStrip z) = z := by
  change (A.affineMarkedBandProductHomeomorph
    (A.affineMarkedBandProductHomeomorph.symm (z, 0))).1 = z
  rw [Homeomorph.apply_symm_apply]

/-- A deck element places the order-three named radial lift in the selected collar at `z`. -/
public def OrderThreeDeckEntersNamedCollarAtStrip
    (A : PaperAnalyticData) (g : Delta) (z : affineVerticalStrip) : Prop :=
  ‖(orderThreeCayleyHomeomorph
      (fuchsianSourceAction g •
        (A.affineOrderThreeRadialBaseLift z).1) : ℂ)‖ <
    A.starSeparation.orderThree.radius

/-- A deck element places the order-four named radial lift in the selected collar at `z`. -/
public def OrderFourDeckEntersNamedCollarAtStrip
    (A : PaperAnalyticData) (g : Delta) (z : affineVerticalStrip) : Prop :=
  ‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction g •
        (A.affineOrderFourRadialBaseLift z).1) : ℂ)‖ <
    A.starSeparation.orderFour.radius

/-- The quotient-overlap construction supplies an entering order-three sheet over every strip
point. -/
public theorem exists_orderThreeDeckEntersNamedCollarAtStrip
    (A : PaperAnalyticData) (z : affineVerticalStrip) :
    ∃ g : Delta, A.OrderThreeDeckEntersNamedCollarAtStrip g z := by
  obtain ⟨g, hg⟩ := A.exists_regularDeck_namedOrderThreeRadialBase_cayley_lt
    (A.affineMarkedBandPointOfStrip z)
  exact ⟨g, by simpa [OrderThreeDeckEntersNamedCollarAtStrip] using hg⟩

/-- The quotient-overlap construction supplies an entering order-four sheet over every strip
point. -/
public theorem exists_orderFourDeckEntersNamedCollarAtStrip
    (A : PaperAnalyticData) (z : affineVerticalStrip) :
    ∃ g : Delta, A.OrderFourDeckEntersNamedCollarAtStrip g z := by
  obtain ⟨g, hg⟩ := A.exists_regularDeck_namedOrderFourRadialBase_cayley_lt
    (A.affineMarkedBandPointOfStrip z)
  exact ⟨g, by simpa [OrderFourDeckEntersNamedCollarAtStrip] using hg⟩

/-- Two order-three deck elements entering at the same point differ by the order-three elliptic
factor. -/
public theorem orderThree_sameSheet_of_both_enter
    (A : PaperAnalyticData) (z : affineVerticalStrip) (g h : Delta)
    (hg : A.OrderThreeDeckEntersNamedCollarAtStrip g z)
    (hh : A.OrderThreeDeckEntersNamedCollarAtStrip h z) :
    ∃ a : CyclicThree, g * h⁻¹ = Monoid.Coprod.inl a := by
  let U := A.modular.modularParameter.toTriangleUniformization
  have hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  have D := A.starSeparation.orderThree.sourceData
  rw [OrderThreeLinearCollarSourceData.eq_def] at D
  apply D.2
    (fuchsianSourceAction g •
      (A.affineOrderThreeRadialBaseLift z).1)
    (fuchsianSourceAction h •
      (A.affineOrderThreeRadialBaseLift z).1)
    hg hh (g * h⁻¹)
  rw [hsource, map_mul, mul_smul, map_inv, inv_smul_smul]

/-- Two order-four deck elements entering at the same point differ by the order-four elliptic
factor. -/
public theorem orderFour_sameSheet_of_both_enter
    (A : PaperAnalyticData) (z : affineVerticalStrip) (g h : Delta)
    (hg : A.OrderFourDeckEntersNamedCollarAtStrip g z)
    (hh : A.OrderFourDeckEntersNamedCollarAtStrip h z) :
    ∃ a : CyclicFour, g * h⁻¹ = Monoid.Coprod.inr a := by
  let U := A.modular.modularParameter.toTriangleUniformization
  have hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  have D := A.starSeparation.orderFour.sourceData
  rw [OrderFourLinearCollarSourceData.eq_def] at D
  apply D.2
    (fuchsianSourceAction g •
      (A.affineOrderFourRadialBaseLift z).1)
    (fuchsianSourceAction h •
      (A.affineOrderFourRadialBaseLift z).1)
    hg hh (g * h⁻¹)
  rw [hsource, map_mul, mul_smul, map_inv, inv_smul_smul]

/-- Membership in one order-three elliptic deck coset transports collar entry. -/
public theorem orderThree_enter_of_sameSheet
    (A : PaperAnalyticData) (z : affineVerticalStrip) (g h : Delta)
    (hsheet : ∃ a : CyclicThree, g * h⁻¹ = Monoid.Coprod.inl a)
    (hh : A.OrderThreeDeckEntersNamedCollarAtStrip h z) :
    A.OrderThreeDeckEntersNamedCollarAtStrip g z := by
  obtain ⟨a, ha⟩ := hsheet
  have hg : g = Monoid.Coprod.inl a * h := by
    calc
      g = (g * h⁻¹) * h := by group
      _ = Monoid.Coprod.inl a * h := by rw [ha]
  rw [OrderThreeDeckEntersNamedCollarAtStrip, hg, map_mul, mul_smul]
  rw [orderThreeCayleyHomeomorph_norm_eq_of_fix_fuchsianOne]
  · exact hh
  · exact (fuchsianOneFixed_iff_mem_range_inl _).mpr ⟨a, rfl⟩

/-- Membership in one order-four elliptic deck coset transports collar entry. -/
public theorem orderFour_enter_of_sameSheet
    (A : PaperAnalyticData) (z : affineVerticalStrip) (g h : Delta)
    (hsheet : ∃ a : CyclicFour, g * h⁻¹ = Monoid.Coprod.inr a)
    (hh : A.OrderFourDeckEntersNamedCollarAtStrip h z) :
    A.OrderFourDeckEntersNamedCollarAtStrip g z := by
  obtain ⟨a, ha⟩ := hsheet
  have hg : g = Monoid.Coprod.inr a * h := by
    calc
      g = (g * h⁻¹) * h := by group
      _ = Monoid.Coprod.inr a * h := by rw [ha]
  rw [OrderFourDeckEntersNamedCollarAtStrip, hg, map_mul, mul_smul]
  rw [orderFourCayleyHomeomorph_norm_eq_of_fix_fuchsianTwo]
  · exact hh
  · exact (fuchsianTwoFixed_iff_mem_range_inr _).mpr ⟨a, rfl⟩

/-- Entry of a fixed order-three deck sheet is an open condition on the strip. -/
public theorem isOpen_orderThreeDeckEntersNamedCollarAtStrip
    (A : PaperAnalyticData) (g : Delta) :
    IsOpen {z : affineVerticalStrip |
      A.OrderThreeDeckEntersNamedCollarAtStrip g z} := by
  apply isOpen_lt
  · exact continuous_norm.comp
      (continuous_subtype_val.comp
        (orderThreeCayleyHomeomorph.continuous.comp
          ((fuchsianSourceAction_contMDiff g 0).continuous.comp
            (continuous_subtype_val.comp
              A.affineOrderThreeRadialBaseLift.continuous))))
  · exact continuous_const

/-- Entry of a fixed order-four deck sheet is an open condition on the strip. -/
public theorem isOpen_orderFourDeckEntersNamedCollarAtStrip
    (A : PaperAnalyticData) (g : Delta) :
    IsOpen {z : affineVerticalStrip |
      A.OrderFourDeckEntersNamedCollarAtStrip g z} := by
  apply isOpen_lt
  · exact continuous_norm.comp
      (continuous_subtype_val.comp
        (orderFourCayleyHomeomorph.continuous.comp
          ((fuchsianSourceAction_contMDiff g 0).continuous.comp
            (continuous_subtype_val.comp
              A.affineOrderFourRadialBaseLift.continuous))))
  · exact continuous_const

/-- The order-three entry set of each fixed deck representative is clopen. -/
public theorem isClopen_orderThreeDeckEntersNamedCollarAtStrip
    (A : PaperAnalyticData) (g : Delta) :
    IsClopen {z : affineVerticalStrip |
      A.OrderThreeDeckEntersNamedCollarAtStrip g z} := by
  refine ⟨?_, A.isOpen_orderThreeDeckEntersNamedCollarAtStrip g⟩
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨h, hh⟩ := A.exists_orderThreeDeckEntersNamedCollarAtStrip z
  apply Filter.mem_of_superset
    (A.isOpen_orderThreeDeckEntersNamedCollarAtStrip h |>.mem_nhds hh)
  intro y hyh hyg
  apply hz
  exact A.orderThree_enter_of_sameSheet z g h
    (A.orderThree_sameSheet_of_both_enter y g h hyg hyh) hh

/-- The order-four entry set of each fixed deck representative is clopen. -/
public theorem isClopen_orderFourDeckEntersNamedCollarAtStrip
    (A : PaperAnalyticData) (g : Delta) :
    IsClopen {z : affineVerticalStrip |
      A.OrderFourDeckEntersNamedCollarAtStrip g z} := by
  refine ⟨?_, A.isOpen_orderFourDeckEntersNamedCollarAtStrip g⟩
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨h, hh⟩ := A.exists_orderFourDeckEntersNamedCollarAtStrip z
  apply Filter.mem_of_superset
    (A.isOpen_orderFourDeckEntersNamedCollarAtStrip h |>.mem_nhds hh)
  intro y hyh hyg
  apply hz
  exact A.orderFour_enter_of_sameSheet z g h
    (A.orderFour_sameSheet_of_both_enter y g h hyg hyh) hh

/-- On the connected affine strip, a fixed order-three deck sheet that enters once enters
everywhere. -/
public theorem orderThreeDeckEntersNamedCollarAtStrip_of_basepoint
    (A : PaperAnalyticData) (g : Delta) (z₀ : affineVerticalStrip)
    (h₀ : A.OrderThreeDeckEntersNamedCollarAtStrip g z₀) :
    ∀ z, A.OrderThreeDeckEntersNamedCollarAtStrip g z := by
  let _ : ContractibleSpace affineVerticalStrip :=
    affineVerticalStrip_contractibleSpace
  have hset := (A.isClopen_orderThreeDeckEntersNamedCollarAtStrip g).eq_univ ⟨z₀, h₀⟩
  intro z
  have hz : z ∈ ({z : affineVerticalStrip |
      A.OrderThreeDeckEntersNamedCollarAtStrip g z} : Set _) := by
    rw [hset]
    exact mem_univ z
  exact hz

/-- On the connected affine strip, a fixed order-four deck sheet that enters once enters
everywhere. -/
public theorem orderFourDeckEntersNamedCollarAtStrip_of_basepoint
    (A : PaperAnalyticData) (g : Delta) (z₀ : affineVerticalStrip)
    (h₀ : A.OrderFourDeckEntersNamedCollarAtStrip g z₀) :
    ∀ z, A.OrderFourDeckEntersNamedCollarAtStrip g z := by
  let _ : ContractibleSpace affineVerticalStrip :=
    affineVerticalStrip_contractibleSpace
  have hset := (A.isClopen_orderFourDeckEntersNamedCollarAtStrip g).eq_univ ⟨z₀, h₀⟩
  intro z
  have hz : z ∈ ({z : affineVerticalStrip |
      A.OrderFourDeckEntersNamedCollarAtStrip g z} : Set _) := by
    rw [hset]
    exact mem_univ z
  exact hz

/-- The exact remaining sheet marking at the pinned actual-cusp crossing.  Each entering deck
representative is required only to lie in the corresponding elliptic stabilizer. -/
public structure AffineActualCuspCrossingStabilizingSheets
    (A : PaperAnalyticData) : Prop where
  orderThree : ∃ g : Delta,
    A.OrderThreeDeckEntersNamedCollarAtStrip g
        A.affineActualCuspCrossingPoint ∧
      fuchsianSourceAction g • fuchsianOneFixedPoint = fuchsianOneFixedPoint
  orderFour : ∃ g : Delta,
    A.OrderFourDeckEntersNamedCollarAtStrip g
        A.affineActualCuspCrossingPoint ∧
      fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint

/-- Stabilizing named sheets at the single pinned crossing imply both marked-band homotopies. -/
public theorem markedBandHomotopies_of_actualCuspCrossingStabilizingSheets
    (A : PaperAnalyticData)
    (H : A.AffineActualCuspCrossingStabilizingSheets) :
    A.AffineOverlapBandCompatibility := by
  apply markedBandHomotopies_of_affineNamedSheetStabilizingDecks A
  · intro x
    obtain ⟨g, hg, hfix⟩ := H.orderThree
    exact ⟨g,
      A.orderThreeDeckEntersNamedCollarAtStrip_of_basepoint g
        A.affineActualCuspCrossingPoint hg
          (A.affineBandStripCoordinate x),
      hfix⟩
  · intro x
    obtain ⟨g, hg, hfix⟩ := H.orderFour
    exact ⟨g,
      A.orderFourDeckEntersNamedCollarAtStrip_of_basepoint g
        A.affineActualCuspCrossingPoint hg
          (A.affineBandStripCoordinate x),
      hfix⟩

/-- Equivalently, it suffices to check that the named identity sheets enter the two selected
collars at the pinned crossing. -/
public theorem markedBandHomotopies_of_actualCuspCrossingCayleyBounds
    (A : PaperAnalyticData)
    (h₃ : ‖(orderThreeCayleyHomeomorph
      (A.affineOrderThreeRadialBaseLift
        A.affineActualCuspCrossingPoint).1 : ℂ)‖ <
      A.starSeparation.orderThree.radius)
    (h₄ : ‖(orderFourCayleyHomeomorph
      (A.affineOrderFourRadialBaseLift
        A.affineActualCuspCrossingPoint).1 : ℂ)‖ <
      A.starSeparation.orderFour.radius) :
    A.AffineOverlapBandCompatibility := by
  apply A.markedBandHomotopies_of_actualCuspCrossingStabilizingSheets
  constructor
  · refine ⟨1, ?_, by simp⟩
    simpa [OrderThreeDeckEntersNamedCollarAtStrip] using h₃
  · refine ⟨1, ?_, by simp⟩
    simpa [OrderFourDeckEntersNamedCollarAtStrip] using h₄

end SphereSixComplex.Geometry.PaperAnalyticData

end
