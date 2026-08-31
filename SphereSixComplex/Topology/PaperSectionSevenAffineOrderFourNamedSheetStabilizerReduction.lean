module

public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderFourExtractedDeckStabilizer

/-!
# Exact stabilizer reduction for the order-four named sheet

The overlap construction already puts at least one regular-deck translate of the named radial
lift in the selected order-four collar.  This file isolates the remaining statement: every deck
translate that enters that collar fixes the order-four elliptic centre.  Pointwise, this is
equivalent to the named radial lift itself lying in the collar.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.TriangleGroup

/-- At a marked-band point, every regular deck transformation carrying the named radial lift
into the selected order-four collar fixes the distinguished order-four elliptic centre. -/
public def OrderFourCollarDecksFixCenterAt
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) : Prop :=
  ∀ g : Delta,
    ‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction g •
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
        A.starSeparation.orderFour.radius →
      fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint

/-- The centre-fixing statement is exactly the assertion that every deck transformation
entering the selected collar belongs to the embedded order-four factor. -/
public theorem orderFourCollarDecksFixCenterAt_iff_mem_orderFourFactor
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.OrderFourCollarDecksFixCenterAt x ↔
      ∀ g : Delta,
        ‖(orderFourCayleyHomeomorph
          (fuchsianSourceAction g •
            (A.sectionSevenAffineOrderFourRadialBaseLift
              (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
            A.starSeparation.orderFour.radius →
          ∃ a : CyclicFour, g = Monoid.Coprod.inr a := by
  constructor
  · intro h g hsmall
    exact (establishedFuchsianTwoStabilizerExact g).mp (h g hsmall)
  · intro h g hsmall
    exact (establishedFuchsianTwoStabilizerExact g).mpr (h g hsmall)

/-- Pointwise, the old named-sheet Cayley bound is equivalent to the precise centre-fixing
condition on every deck translate detected by the quotient overlap construction. -/
public theorem namedOrderFourRadialBase_cayley_lt_iff_collarDecksFixCenterAt
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    ‖(orderFourCayleyHomeomorph
      (A.sectionSevenAffineOrderFourRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderFour.radius ↔
      A.OrderFourCollarDecksFixCenterAt x := by
  constructor
  · intro hnamed g hsmall
    apply (establishedFuchsianTwoStabilizerExact g).mpr
    exact A.mem_orderFourFactor_of_named_and_deck_cayley_lt x g hsmall hnamed
  · intro h
    obtain ⟨g, hsmall⟩ := A.exists_regularDeck_namedOrderFourRadialBase_cayley_lt x
    exact (A.fixes_fuchsianTwo_iff_namedOrderFourRadialBase_cayley_lt x g hsmall).mp
      (h g hsmall)

/-- Globally, the order-four named radial collar compatibility is equivalent to the assertion
that every deck translate entering the selected collar fixes the order-four elliptic centre. -/
public theorem sectionSevenAffineOrderFourNamedRadialCollarCompatibility_iff_collarDecksFixCenter
    (A : PaperAnalyticData) :
    A.SectionSevenAffineOrderFourNamedRadialCollarCompatibility ↔
      ∀ x : A.SectionSevenAffineMarkedBand, A.OrderFourCollarDecksFixCenterAt x := by
  rw [A.sectionSevenAffineOrderFourNamedRadialCollarCompatibility_iff]
  constructor
  · intro h x
    exact (A.namedOrderFourRadialBase_cayley_lt_iff_collarDecksFixCenterAt x).mp (h x)
  · intro h x
    exact (A.namedOrderFourRadialBase_cayley_lt_iff_collarDecksFixCenterAt x).mpr (h x)

end SphereSixComplex.Geometry.PaperAnalyticData

end
