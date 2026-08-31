module

public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderThreeEndpointRealPeriodIdentityProof
public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderFourNamedSheetStabilizerReduction

/-!
# Named-sheet completion of the affine marked-band homotopies

The quotient overlap construction puts a regular-deck translate of each named radial lift in
the selected collar.  The exact additional information needed is that one such extracted deck
element belongs to the corresponding elliptic stabilizer.  This file proves that this condition
is equivalent to the two named Cayley bounds and derives the complete marked-band homotopies.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry

open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.TriangleGroup

/-- A deck transformation fixing the order-three elliptic centre preserves the order-three
Cayley norm. -/
public theorem orderThreeCayleyHomeomorph_norm_eq_of_fix_fuchsianOne
    (g : Delta) (z : UpperHalfPlane)
    (hfix : fuchsianSourceAction g • fuchsianOneFixedPoint = fuchsianOneFixedPoint) :
    ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction g • z) : ℂ)‖ =
      ‖(orderThreeCayleyHomeomorph z : ℂ)‖ := by
  obtain ⟨a, rfl⟩ := (establishedFuchsianOneStabilizerExact g).mp hfix
  exact orderThreeCayleyHomeomorph_norm_inl a z

namespace PaperAnalyticData

open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent

/-- If a deck translate and the named order-three radial lift both enter the selected collar,
collar separation forces that deck element into the order-three elliptic stabilizer. -/
public theorem fixes_fuchsianOne_of_named_and_deck_cayley_lt
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) (g : Delta)
    (hdeck : ‖(orderThreeCayleyHomeomorph
      (fuchsianSourceAction g •
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
        A.starSeparation.orderThree.radius)
    (hnamed : ‖(orderThreeCayleyHomeomorph
      (A.sectionSevenAffineOrderThreeRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderThree.radius) :
    fuchsianSourceAction g • fuchsianOneFixedPoint = fuchsianOneFixedPoint := by
  apply (establishedFuchsianOneStabilizerExact g).mpr
  let U := A.modular.modularParameter.toTriangleUniformization
  have hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  have D := A.starSeparation.orderThree.sourceData
  rw [OrderThreeLinearCollarSourceData.eq_def] at D
  exact D.2
    (fuchsianSourceAction g •
      (A.sectionSevenAffineOrderThreeRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1)
    (A.sectionSevenAffineOrderThreeRadialBaseLift
      (A.sectionSevenAffineBandStripCoordinate x)).1
    hdeck hnamed g (by rw [hsource])

/-- For a deck element already carrying the named order-three lift into the collar, fixing the
elliptic centre is equivalent to the named lift itself satisfying the collar bound. -/
public theorem fixes_fuchsianOne_iff_namedOrderThreeRadialBase_cayley_lt
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) (g : Delta)
    (hdeck : ‖(orderThreeCayleyHomeomorph
      (fuchsianSourceAction g •
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
        A.starSeparation.orderThree.radius) :
    fuchsianSourceAction g • fuchsianOneFixedPoint = fuchsianOneFixedPoint ↔
      ‖(orderThreeCayleyHomeomorph
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderThree.radius := by
  constructor
  · intro hfix
    rw [← orderThreeCayleyHomeomorph_norm_eq_of_fix_fuchsianOne g _ hfix]
    exact hdeck
  · exact fun hnamed ↦ A.fixes_fuchsianOne_of_named_and_deck_cayley_lt x g hdeck hnamed

/-- Pointwise, existence of an extracted order-three deck element in the elliptic stabilizer is
exactly the named-sheet Cayley bound. -/
public theorem exists_orderThree_stabilizingDeck_iff_namedCayley_lt
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    (∃ g : Delta,
      ‖(orderThreeCayleyHomeomorph
        (fuchsianSourceAction g •
          (A.sectionSevenAffineOrderThreeRadialBaseLift
            (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
          A.starSeparation.orderThree.radius ∧
        fuchsianSourceAction g • fuchsianOneFixedPoint = fuchsianOneFixedPoint) ↔
      ‖(orderThreeCayleyHomeomorph
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderThree.radius := by
  constructor
  · rintro ⟨g, hdeck, hfix⟩
    exact (A.fixes_fuchsianOne_iff_namedOrderThreeRadialBase_cayley_lt
      x g hdeck).mp hfix
  · intro hnamed
    obtain ⟨g, hdeck⟩ := A.exists_regularDeck_namedOrderThreeRadialBase_cayley_lt x
    exact ⟨g, hdeck,
      A.fixes_fuchsianOne_of_named_and_deck_cayley_lt x g hdeck hnamed⟩

/-- The analogous order-four stabilizing-deck condition, written without an auxiliary
predicate, is exactly the order-four named Cayley bound. -/
public theorem exists_orderFour_stabilizingDeck_iff_namedCayley_lt
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    (∃ g : Delta,
      ‖(orderFourCayleyHomeomorph
        (fuchsianSourceAction g •
          (A.sectionSevenAffineOrderFourRadialBaseLift
            (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
          A.starSeparation.orderFour.radius ∧
        fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint) ↔
      ‖(orderFourCayleyHomeomorph
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderFour.radius := by
  constructor
  · rintro ⟨g, hdeck, hfix⟩
    exact (A.fixes_fuchsianTwo_iff_namedOrderFourRadialBase_cayley_lt
      x g hdeck).mp hfix
  · intro hnamed
    obtain ⟨g, hdeck⟩ := A.exists_regularDeck_namedOrderFourRadialBase_cayley_lt x
    have hfix := (A.fixes_fuchsianTwo_iff_namedOrderFourRadialBase_cayley_lt
      x g hdeck).mpr hnamed
    exact ⟨g, hdeck, hfix⟩

/-- The paired stabilizing-deck hypothesis is precisely equivalent to the pair of named-sheet
Cayley bounds. -/
public theorem affineNamedSheetStabilizingDecks_iff_cayleyBounds
    (A : PaperAnalyticData) :
    ((∀ x : A.SectionSevenAffineMarkedBand, ∃ g : Delta,
        ‖(orderThreeCayleyHomeomorph
          (fuchsianSourceAction g •
            (A.sectionSevenAffineOrderThreeRadialBaseLift
              (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
            A.starSeparation.orderThree.radius ∧
          fuchsianSourceAction g • fuchsianOneFixedPoint = fuchsianOneFixedPoint) ∧
      (∀ x : A.SectionSevenAffineMarkedBand, ∃ g : Delta,
        ‖(orderFourCayleyHomeomorph
          (fuchsianSourceAction g •
            (A.sectionSevenAffineOrderFourRadialBaseLift
              (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
            A.starSeparation.orderFour.radius ∧
          fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint)) ↔
      ((∀ x : A.SectionSevenAffineMarkedBand,
        ‖(orderThreeCayleyHomeomorph
          (A.sectionSevenAffineOrderThreeRadialBaseLift
            (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
          A.starSeparation.orderThree.radius) ∧
       (∀ x : A.SectionSevenAffineMarkedBand,
        ‖(orderFourCayleyHomeomorph
          (A.sectionSevenAffineOrderFourRadialBaseLift
            (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
          A.starSeparation.orderFour.radius)) := by
  constructor
  · rintro ⟨h₃, h₄⟩
    exact ⟨fun x ↦ (A.exists_orderThree_stabilizingDeck_iff_namedCayley_lt x).mp (h₃ x),
      fun x ↦ (A.exists_orderFour_stabilizingDeck_iff_namedCayley_lt x).mp (h₄ x)⟩
  · rintro ⟨h₃, h₄⟩
    exact ⟨fun x ↦ (A.exists_orderThree_stabilizingDeck_iff_namedCayley_lt x).mpr (h₃ x),
      fun x ↦ (A.exists_orderFour_stabilizingDeck_iff_namedCayley_lt x).mpr (h₄ x)⟩

/-- The sharply minimal stabilizing-deck hypothesis supplies both explicit endpoint formulas
and hence the complete marked affine-band compatibility. -/
public theorem markedBandHomotopies_of_affineNamedSheetStabilizingDecks
    (A : PaperAnalyticData)
    (h₃ : ∀ x : A.SectionSevenAffineMarkedBand, ∃ g : Delta,
      ‖(orderThreeCayleyHomeomorph
        (fuchsianSourceAction g •
          (A.sectionSevenAffineOrderThreeRadialBaseLift
            (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
          A.starSeparation.orderThree.radius ∧
        fuchsianSourceAction g • fuchsianOneFixedPoint = fuchsianOneFixedPoint)
    (h₄ : ∀ x : A.SectionSevenAffineMarkedBand, ∃ g : Delta,
      ‖(orderFourCayleyHomeomorph
        (fuchsianSourceAction g •
          (A.sectionSevenAffineOrderFourRadialBaseLift
            (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
          A.starSeparation.orderFour.radius ∧
        fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint) :
    A.SectionSevenAffineOverlapBandCompatibility := by
  have hbounds := (A.affineNamedSheetStabilizingDecks_iff_cayleyBounds).mp ⟨h₃, h₄⟩
  let C₄ : A.SectionSevenAffineOrderFourNamedRadialCollarCompatibility :=
    (A.sectionSevenAffineOrderFourNamedRadialCollarCompatibility_iff).mpr hbounds.2
  apply markedBandHomotopies_of_pinnedLiftEndpointGaugeFormulas
    A A.sectionSevenAffineNamedStripLift
      A.sectionSevenAffineNamedStripLift_apply_actualCuspCrossing
      A.sectionSevenAffineOrderThreeEndpointGauge
      A.sectionSevenAffineOrderFourEndpointGauge
  constructor
  · exact A.sectionSevenAffineOrderThreeEndpointGaugeFormula
      (A.sectionSevenAffineOrderThreeEndpointRealPeriodIdentity hbounds.1)
  · exact A.sectionSevenAffineOrderFourEndpointGaugeFormula
      (A.sectionSevenAffineOrderFourEndpointRealPeriodIdentity C₄)

end PaperAnalyticData

end SphereSixComplex.Geometry

end

end
