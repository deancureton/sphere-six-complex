module

public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderFourNamedSheetCayleyBound

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
  obtain ⟨a, rfl⟩ := (establishedFuchsianTwoStabilizerExact g).mp hfix
  exact orderFourCayleyHomeomorph_norm_inr a z

/-- Global invariance of the order-four Cayley norm is equivalent to fixing its elliptic centre. -/
public theorem orderFourCayleyHomeomorph_norm_invariant_iff_fix_fuchsianTwo (g : Delta) :
    (∀ z : UpperHalfPlane,
      ‖(orderFourCayleyHomeomorph (fuchsianSourceAction g • z) : ℂ)‖ =
        ‖(orderFourCayleyHomeomorph z : ℂ)‖) ↔
      fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint := by
  constructor
  · intro h
    have hz := h fuchsianTwoFixedPoint
    rw [orderFourCayleyHomeomorph_fixedPoint] at hz
    have hzero : (orderFourCayleyHomeomorph
        (fuchsianSourceAction g • fuchsianTwoFixedPoint) : ℂ) = 0 := by
      apply norm_eq_zero.mp
      simpa [discCenter] using hz
    apply orderFourCayleyHomeomorph.injective
    rw [orderFourCayleyHomeomorph_fixedPoint]
    exact Subtype.ext hzero
  · exact fun hfix z ↦ orderFourCayleyHomeomorph_norm_eq_of_fix_fuchsianTwo g z hfix

/-- Equivalently, the full norm-preserving deck subgroup is exactly the embedded order-four
factor. -/
public theorem orderFourCayleyHomeomorph_norm_invariant_iff_mem_orderFourFactor (g : Delta) :
    (∀ z : UpperHalfPlane,
      ‖(orderFourCayleyHomeomorph (fuchsianSourceAction g • z) : ℂ)‖ =
        ‖(orderFourCayleyHomeomorph z : ℂ)‖) ↔
      ∃ a : CyclicFour, g = Monoid.Coprod.inr a :=
  (orderFourCayleyHomeomorph_norm_invariant_iff_fix_fuchsianTwo g).trans
    (establishedFuchsianTwoStabilizerExact g)

/-- The unrestricted deck-invariance claim is false: the order-three generator moves the
order-four Cayley centre away from radius zero. -/
public theorem orderFourCayleyHomeomorph_norm_not_invariant_under_gOne :
    ‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction g₁ • fuchsianTwoFixedPoint) : ℂ)‖ ≠
      ‖(orderFourCayleyHomeomorph fuchsianTwoFixedPoint : ℂ)‖ := by
  have hmove :
      fuchsianSourceAction g₁ • fuchsianTwoFixedPoint ≠ fuchsianTwoFixedPoint := by
    intro h
    have hcent := (fuchsianSourceAction_gOne_fixed_iff fuchsianTwoFixedPoint).mp h
    have hre := congrArg (fun z : UpperHalfPlane ↦ z.re) hcent
    simp [fuchsianOneFixedPoint, fuchsianTwoFixedPoint] at hre
    have hsqrtTwoPos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsqrtThreePos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  have hleft : (orderFourCayleyHomeomorph
      (fuchsianSourceAction g₁ • fuchsianTwoFixedPoint) : ℂ) ≠ 0 := by
    intro hzero
    have heq : fuchsianSourceAction g₁ • fuchsianTwoFixedPoint =
        fuchsianTwoFixedPoint := by
      apply orderFourCayleyHomeomorph.injective
      rw [orderFourCayleyHomeomorph_fixedPoint]
      exact Subtype.ext hzero
    exact hmove heq
  rw [orderFourCayleyHomeomorph_fixedPoint]
  simpa [discCenter] using norm_ne_zero_iff.mpr hleft

namespace PaperAnalyticData

/-- If the deck element carrying the named radial lift into the selected collar belongs to the
order-four elliptic stabilizer, the named lift itself lies in that collar. -/
public theorem namedOrderFourRadialBase_cayley_lt_of_deck_fixes_fuchsianTwo
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) (g : Delta)
    (hsmall : ‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction g •
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
        A.starSeparation.orderFour.radius)
    (hfix : fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint) :
    ‖(orderFourCayleyHomeomorph
      (A.sectionSevenAffineOrderFourRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
      A.starSeparation.orderFour.radius := by
  apply A.namedOrderFourRadialBase_cayley_lt_of_deck_cayley_norm_eq x g hsmall
  exact orderFourCayleyHomeomorph_norm_eq_of_fix_fuchsianTwo g _ hfix

/-- A nonidentity element of the order-four factor preserves the Cayley radius but does not fix
the regular named radial point.  Thus literal fixed-sheet equality is unnecessarily strong. -/
public theorem namedOrderFourRadialBase_ne_deck_smul_of_nontrivial_orderFourFactor
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand)
    (a : CyclicFour) (ha : a ≠ 1) :
    fuchsianSourceAction (Monoid.Coprod.inr a) •
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 ≠
      (A.sectionSevenAffineOrderFourRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1 := by
  intro hfixed
  have hcenter := (fuchsianSourceAction_inr_fixed_iff a ha _).mp hfixed
  have hpos := A.orderFourFamilyRadius_namedCollarTotalPoint_pos x
  rw [A.orderFourFamilyRadius_namedCollarTotalPoint x] at hpos
  have hzero : (orderFourCayleyHomeomorph
      (A.sectionSevenAffineOrderFourRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ) = 0 := by
    rw [hcenter, orderFourCayleyHomeomorph_fixedPoint]
    rfl
  exact (norm_pos_iff.mp hpos) hzero

end PaperAnalyticData

end SphereSixComplex.Geometry

end
