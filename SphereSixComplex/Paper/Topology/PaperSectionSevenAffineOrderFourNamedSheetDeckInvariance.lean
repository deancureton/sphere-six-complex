module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineOrderFourNamedSheetCayleyBound

/-!
# Deck invariance of the order-four Cayley radius

The order-four Cayley norm is invariant precisely under the elliptic `C₄` stabilizer.  It is not
invariant under the full regular deck group.  Thus the named-sheet residue is a stabilizer (or
sheet-identification) statement, rather than a general deck-invariance statement.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry

open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticLocalTrivialization
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FreeProductTorsion

/-- A deck transformation fixing the order-four elliptic centre preserves the order-four Cayley
norm everywhere. -/
public theorem orderFourCayleyHomeomorph_norm_eq_of_fix_fuchsianTwo
    (g : Delta) (z : UpperHalfPlane)
    (hfix : fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint) :
    ‖(orderFourCayleyHomeomorph (fuchsianSourceAction g • z) : ℂ)‖ =
      ‖(orderFourCayleyHomeomorph z : ℂ)‖ := by
  obtain ⟨a, rfl⟩ := (fuchsianTwoFixed_iff_mem_range_inr g).mp hfix
  exact orderFourCayleyHomeomorph_norm_inr a z




namespace AnalyticData

/-- If the deck element carrying the named radial lift into the selected collar belongs to the
order-four elliptic stabilizer, the named lift itself lies in that collar. -/
public theorem namedOrderFourRadialBase_cayley_lt_of_deck_fixes_fuchsianTwo
    (A : AnalyticData) (x : A.affineMarkedBand) (g : Delta)
    (hsmall : ‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction g •
        (A.affineOrderFourRadialBaseLift
          (A.affineBandStripCoordinate x)).1) : ℂ)‖ <
        A.starSeparation.orderFour.radius)
    (hfix : fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint) :
    ‖(orderFourCayleyHomeomorph
      (A.affineOrderFourRadialBaseLift
        (A.affineBandStripCoordinate x)).1 : ℂ)‖ <
      A.starSeparation.orderFour.radius := by
  apply A.namedOrderFourRadialBase_cayley_lt_of_deck_cayley_norm_eq x g hsmall
  exact orderFourCayleyHomeomorph_norm_eq_of_fix_fuchsianTwo g _ hfix


end AnalyticData

end SphereSixComplex.Geometry

end
