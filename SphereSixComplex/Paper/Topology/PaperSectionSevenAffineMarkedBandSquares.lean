module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineRegularLiftCompletionAssembly

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

This is the *marked* trivialization at `affineNamedStripLift`, the unique strip lift
through the selected actual cusp crossing and its explicit regular-base representative, not an
`Exists.choose` of the unmarked triviality statement: the unmarked statement pins the base
coordinate only, so its chosen witness leaves the fibre coordinate free (see
`exists_productTrivialization_fiberCoordinate_comp`) and every downstream square built on it would
be false as stated. -/
public noncomputable def affineCentralBandProductHomeomorph
    (S : A.AffineCentralSeparation) :
    centralHeightBand
        (A.affineCentralHeightSplit S).height
        (A.affineCentralHeightSplit S).lower
        (A.affineCentralHeightSplit S).upper ≃ₜ
      affineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter :=
  A.affineCentralBandMarkedProductHomeomorph S

/-- The fibre coordinate of the selected actual central-band product trivialization. -/
public noncomputable def affineCentralBandFiberCoordinate
    (S : A.AffineCentralSeparation) :
    C(centralHeightBand
        (A.affineCentralHeightSplit S).height
        (A.affineCentralHeightSplit S).lower
        (A.affineCentralHeightSplit S).upper,
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :=
  ⟨fun x ↦ (A.affineCentralBandProductHomeomorph S x).2,
    continuous_snd.comp
      (A.affineCentralBandProductHomeomorph S).continuous⟩

/-- The homotopy equivalence used by the completion has exactly the selected product
trivialization's fibre coordinate as its forward map. -/
public theorem affineCentralBandHomotopyEquiv_toFun
    (S : A.AffineCentralSeparation) :
    (A.affineCentralBandHomotopyEquiv S).toFun =
      A.affineCentralBandFiberCoordinate S := by
  rfl

/-- The named map from the actual affine band to its selected common torus coordinate. -/
public noncomputable def affineBandFiberCoordinate (A : PaperAnalyticData) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :=
  (A.actualAffineHeightSplit.sidesIntersectionHomeomorph.toHomotopyEquiv.trans
    (A.affineCentralBandHomotopyEquiv
      A.affineCentralSeparation)).toFun

/-- Pointwise, the named band coordinate is the selected product trivialization's fibre
coordinate after the canonical central-band homeomorphism. -/
public theorem affineBandFiberCoordinate_apply
    (A : PaperAnalyticData)
    (x : (A.actualAffineHeightSplit.allocation.orderThreeSide ∩
      A.actualAffineHeightSplit.allocation.orderFourSide :
        Set A.ellipticInterior)) :
    affineBandFiberCoordinate A x =
      A.affineCentralBandFiberCoordinate
        A.affineCentralSeparation
          (A.actualAffineHeightSplit.sidesIntersectionHomeomorph x) := by
  rfl

/-- The order-three canonical marked projection, factored through the named band fibre
coordinate and the actual finite quotient map. -/
public noncomputable def affineBandOrderThreeMarkedProjection
    (A : PaperAnalyticData) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      OrderThreeReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
      A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩).comp
        (affineBandFiberCoordinate A)

/-- The order-four canonical marked projection, factored through the named band fibre
coordinate and the actual finite quotient map. -/
public noncomputable def affineBandOrderFourMarkedProjection
    (A : PaperAnalyticData) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      OrderFourReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
      A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩).comp
        (affineBandFiberCoordinate A)

/-- The named order-three marked projection is exactly the fixed cover map used by the radial
completion. -/
public theorem affineBandOrderThreeMarkedProjection_eq_coverMap
    (A : PaperAnalyticData) :
    affineBandOrderThreeMarkedProjection A =
      affineBandOrderThreeCoverMap A := by
  rfl

/-- The named order-four marked projection is exactly the fixed cover map used by the radial
completion. -/
public theorem affineBandOrderFourMarkedProjection_eq_coverMap
    (A : PaperAnalyticData) :
    affineBandOrderFourMarkedProjection A =
      affineBandOrderFourCoverMap A := by
  rfl

/-- The two explicit geometric squares left after naming the actual band fibre coordinate and
the finite quotient maps. -/
public structure AffineRegularLiftMarkedProjectionSquares
    (orderThreeRegularLift : A.AffineOrderThreeRegularLiftInput)
    (orderFourRegularLift : A.AffineOrderFourRegularLiftInput) where
  orderThreeSquare : orderThreeRegularLift.bandToReducedFiber.Homotopic
    (affineBandOrderThreeMarkedProjection A)
  orderFourSquare : orderFourRegularLift.bandToReducedFiber.Homotopic
    (affineBandOrderFourMarkedProjection A)

namespace AffineRegularLiftMarkedProjectionSquares

/-- The explicit marked-projection squares imply the prior compatibility interface. -/
public theorem toBandCompatibility
    {orderThreeRegularLift : A.AffineOrderThreeRegularLiftInput}
    {orderFourRegularLift : A.AffineOrderFourRegularLiftInput}
    (H : A.AffineRegularLiftMarkedProjectionSquares
      orderThreeRegularLift orderFourRegularLift) :
    A.AffineRegularLiftBandCompatibilityInput
      orderThreeRegularLift orderFourRegularLift where
  orderThreeCompatibility := by
    rw [← affineBandOrderThreeMarkedProjection_eq_coverMap A]
    exact H.orderThreeSquare
  orderFourCompatibility := by
    rw [← affineBandOrderFourMarkedProjection_eq_coverMap A]
    exact H.orderFourSquare

end AffineRegularLiftMarkedProjectionSquares

end SphereSixComplex.Geometry.PaperAnalyticData

end
