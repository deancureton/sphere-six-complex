module

public import SphereSixComplex.Topology.PaperSectionSevenAffineRegularLiftCompletionAssembly

/-!
# Marked central-band squares for the affine completion

The established affine-band trivialization is unpacked into its actual product homeomorphism and
the resulting fibre-coordinate map.  This makes both canonical finite-cover projections explicit
and isolates the remaining compatibility as two named geometric squares.
-/

@[expose] public section

noncomputable section

open Set
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

variable {A : PaperAnalyticData}

/-- The named product homeomorphism of the actual central torus bundle over the affine strip.

This is the *marked* trivialization at `sectionSevenAffineNamedStripLift`, not an `Exists.choose`
of the unmarked triviality statement: the unmarked statement pins the base coordinate only, so its
chosen witness leaves the fibre coordinate free (see
`exists_productTrivialization_fiberCoordinate_comp`) and every downstream square built on it would
be false as stated. -/
public noncomputable def sectionSevenAffineCentralBandProductHomeomorph
    (S : A.SectionSevenAffineCentralSeparation) :
    centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper ≃ₜ
      sectionSevenAffineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter :=
  A.sectionSevenAffineCentralBandMarkedProductHomeomorph S

/-- The fibre coordinate of the selected actual central-band product trivialization. -/
public noncomputable def sectionSevenAffineCentralBandFiberCoordinate
    (S : A.SectionSevenAffineCentralSeparation) :
    C(centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper,
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :=
  ⟨fun x ↦ (A.sectionSevenAffineCentralBandProductHomeomorph S x).2,
    continuous_snd.comp
      (A.sectionSevenAffineCentralBandProductHomeomorph S).continuous⟩

/-- The homotopy equivalence used by the completion has exactly the selected product
trivialization's fibre coordinate as its forward map. -/
public theorem sectionSevenAffineCentralBandHomotopyEquiv_toFun
    (S : A.SectionSevenAffineCentralSeparation) :
    (A.sectionSevenAffineCentralBandHomotopyEquiv S).toFun =
      A.sectionSevenAffineCentralBandFiberCoordinate S := by
  rfl

/-- The named map from the actual affine band to its selected common torus coordinate. -/
public noncomputable def sectionSevenAffineBandFiberCoordinate (A : PaperAnalyticData) :
    C((A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior),
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :=
  (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph.toHomotopyEquiv.trans
    (A.sectionSevenAffineCentralBandHomotopyEquiv
      A.sectionSevenAffineCentralSeparation)).toFun

/-- Pointwise, the named band coordinate is the selected product trivialization's fibre
coordinate after the canonical central-band homeomorphism. -/
public theorem sectionSevenAffineBandFiberCoordinate_apply
    (A : PaperAnalyticData)
    (x : (A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
      A.sectionSevenActualAffineSplit.allocation.orderFourSide :
        Set A.SectionSevenEllipticInterior)) :
    sectionSevenAffineBandFiberCoordinate A x =
      A.sectionSevenAffineCentralBandFiberCoordinate
        A.sectionSevenAffineCentralSeparation
          (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph x) := by
  rfl

/-- The order-three canonical marked projection, factored through the named band fibre
coordinate and the actual finite quotient map. -/
public noncomputable def sectionSevenAffineBandOrderThreeMarkedProjection
    (A : PaperAnalyticData) :
    C((A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior),
      OrderThreeReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
      A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩).comp
        (sectionSevenAffineBandFiberCoordinate A)

/-- The order-four canonical marked projection, factored through the named band fibre
coordinate and the actual finite quotient map. -/
public noncomputable def sectionSevenAffineBandOrderFourMarkedProjection
    (A : PaperAnalyticData) :
    C((A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior),
      OrderFourReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
      A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩).comp
        (sectionSevenAffineBandFiberCoordinate A)

/-- The named order-three marked projection is exactly the fixed cover map used by the radial
completion. -/
public theorem sectionSevenAffineBandOrderThreeMarkedProjection_eq_coverMap
    (A : PaperAnalyticData) :
    sectionSevenAffineBandOrderThreeMarkedProjection A =
      sectionSevenAffineBandOrderThreeCoverMap A := by
  rfl

/-- The named order-four marked projection is exactly the fixed cover map used by the radial
completion. -/
public theorem sectionSevenAffineBandOrderFourMarkedProjection_eq_coverMap
    (A : PaperAnalyticData) :
    sectionSevenAffineBandOrderFourMarkedProjection A =
      sectionSevenAffineBandOrderFourCoverMap A := by
  rfl

/-- The two explicit geometric squares left after naming the actual band fibre coordinate and
the finite quotient maps. -/
public structure SectionSevenAffineRegularLiftMarkedProjectionSquares
    (orderThreeRegularLift : A.SectionSevenAffineOrderThreeRegularLiftInput)
    (orderFourRegularLift : A.SectionSevenAffineOrderFourRegularLiftInput) where
  orderThreeSquare : orderThreeRegularLift.bandToReducedFiber.Homotopic
    (sectionSevenAffineBandOrderThreeMarkedProjection A)
  orderFourSquare : orderFourRegularLift.bandToReducedFiber.Homotopic
    (sectionSevenAffineBandOrderFourMarkedProjection A)

namespace SectionSevenAffineRegularLiftMarkedProjectionSquares

/-- The explicit marked-projection squares imply the prior compatibility interface. -/
public theorem toBandCompatibility
    {orderThreeRegularLift : A.SectionSevenAffineOrderThreeRegularLiftInput}
    {orderFourRegularLift : A.SectionSevenAffineOrderFourRegularLiftInput}
    (H : A.SectionSevenAffineRegularLiftMarkedProjectionSquares
      orderThreeRegularLift orderFourRegularLift) :
    A.SectionSevenAffineRegularLiftBandCompatibilityInput
      orderThreeRegularLift orderFourRegularLift where
  orderThreeCompatibility := by
    rw [← sectionSevenAffineBandOrderThreeMarkedProjection_eq_coverMap A]
    exact H.orderThreeSquare
  orderFourCompatibility := by
    rw [← sectionSevenAffineBandOrderFourMarkedProjection_eq_coverMap A]
    exact H.orderFourSquare

end SectionSevenAffineRegularLiftMarkedProjectionSquares

end SphereSixComplex.Geometry.PaperAnalyticData

end
