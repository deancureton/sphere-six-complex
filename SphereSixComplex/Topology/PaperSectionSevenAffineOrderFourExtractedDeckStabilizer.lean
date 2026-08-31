module

public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderFourNamedSheetDeckInvariance

/-!
# Stabilizer criterion for the extracted order-four deck element

The deck element extracted from equality in the regular quotient carries the named radial lift
into the selected order-four collar.  The collar-separation theorem shows that this element lies
in the order-four stabilizer exactly when the named lift already lies in that collar.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.TriangleGroup

/-- The exact stabilizer condition on a deck element carrying the named radial lift into the
selected order-four collar. -/
public def IsOrderFourExtractedDeckStabilizer
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) (g : Delta) : Prop :=
  (‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction g •
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
      A.starSeparation.orderFour.radius) ∧
    ∃ a : CyclicFour, g = Monoid.Coprod.inr a

/-- If both the named radial lift and its deck translate lie in the selected order-four collar,
collar separation forces the deck element into the embedded `C₄` factor. -/
public theorem mem_orderFourFactor_of_named_and_deck_cayley_lt
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) (g : Delta)
    (hdeck : ‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction g •
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
        A.starSeparation.orderFour.radius)
    (hnamed : ‖(orderFourCayleyHomeomorph
      (A.sectionSevenAffineOrderFourRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderFour.radius) :
    ∃ a : CyclicFour, g = Monoid.Coprod.inr a := by
  let U := A.modular.modularParameter.toTriangleUniformization
  have hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  have hseparation := A.starSeparation.orderFour.sourceData
  rw [OrderFourLinearCollarSourceData.eq_def] at hseparation
  apply hseparation.2
    (fuchsianSourceAction g •
      (A.sectionSevenAffineOrderFourRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1)
    (A.sectionSevenAffineOrderFourRadialBaseLift
      (A.sectionSevenAffineBandStripCoordinate x)).1 hdeck hnamed g
  rw [hsource]

/-- For any deck element already known to carry the named radial lift into the collar, membership
in the order-four factor is equivalent to the missing named-sheet Cayley bound. -/
public theorem mem_orderFourFactor_iff_namedOrderFourRadialBase_cayley_lt
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) (g : Delta)
    (hdeck : ‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction g •
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
        A.starSeparation.orderFour.radius) :
    (∃ a : CyclicFour, g = Monoid.Coprod.inr a) ↔
      ‖(orderFourCayleyHomeomorph
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderFour.radius := by
  constructor
  · rintro ⟨a, rfl⟩
    apply A.namedOrderFourRadialBase_cayley_lt_of_deck_fixes_fuchsianTwo x _ hdeck
    exact (establishedFuchsianTwoStabilizerExact _).mpr ⟨a, rfl⟩
  · exact fun hnamed ↦ A.mem_orderFourFactor_of_named_and_deck_cayley_lt x g hdeck hnamed

/-- Equivalently, an extracted deck element fixes the order-four elliptic centre exactly when
the named radial lift satisfies the missing collar bound. -/
public theorem fixes_fuchsianTwo_iff_namedOrderFourRadialBase_cayley_lt
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) (g : Delta)
    (hdeck : ‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction g •
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
        A.starSeparation.orderFour.radius) :
    fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint ↔
      ‖(orderFourCayleyHomeomorph
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderFour.radius := by
  rw [establishedFuchsianTwoStabilizerExact]
  exact A.mem_orderFourFactor_iff_namedOrderFourRadialBase_cayley_lt x g hdeck

/-- The pointwise named-sheet Cayley bound is exactly the assertion that some extracted deck
element carrying the named lift into the collar belongs to the order-four stabilizer. -/
public theorem exists_orderFourExtractedDeckStabilizer_iff
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    (∃ g : Delta, A.IsOrderFourExtractedDeckStabilizer x g) ↔
      ‖(orderFourCayleyHomeomorph
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderFour.radius := by
  constructor
  · rintro ⟨g, hdeck, hfactor⟩
    exact (A.mem_orderFourFactor_iff_namedOrderFourRadialBase_cayley_lt x g hdeck).mp hfactor
  · intro hnamed
    obtain ⟨g, hdeck⟩ := A.exists_regularDeck_namedOrderFourRadialBase_cayley_lt x
    refine ⟨g, hdeck, ?_⟩
    exact A.mem_orderFourFactor_of_named_and_deck_cayley_lt x g hdeck hnamed

/-- Globally, the extracted-deck stabilizer statement is equivalent to the existing named radial
collar compatibility predicate. -/
public theorem sectionSevenAffineOrderFourNamedRadialCollarCompatibility_iff_extractedDeck
    (A : PaperAnalyticData) :
    A.SectionSevenAffineOrderFourNamedRadialCollarCompatibility ↔
      ∀ x : A.SectionSevenAffineMarkedBand,
        ∃ g : Delta, A.IsOrderFourExtractedDeckStabilizer x g := by
  rw [A.sectionSevenAffineOrderFourNamedRadialCollarCompatibility_iff]
  constructor
  · intro h x
    exact (A.exists_orderFourExtractedDeckStabilizer_iff x).mpr (h x)
  · intro h x
    exact (A.exists_orderFourExtractedDeckStabilizer_iff x).mp (h x)

end SphereSixComplex.Geometry.PaperAnalyticData

end
