module

public import SphereSixComplex.Topology.PaperSectionSevenAffineCompletionAssembly
public import SphereSixComplex.Topology.PaperSectionSevenAffineRegularLiftCarriers

/-!
# Affine completion from the genuine regular-cover quotient models

The lifted affine regions carry the actual `Delta` deck action of the regular torus family.
The quotient models therefore retain the family monodromy.  This file discharges the ambient
separation hypotheses, constructs the two side equivalences, and isolates the remaining geometry
as the two marked compatibility homotopies on the central band.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

variable {A : PaperAnalyticData}

namespace SectionSevenAffineOrderThreeRegularLiftInput

/-- The genuine order-three regular-cover quotient model constructs the actual filling-to-side
homotopy equivalence, with normality and paracompactness supplied by the analytic star. -/
public theorem actualHomotopyEquivalenceInclusion
    (R : A.SectionSevenAffineOrderThreeRegularLiftInput) :
    IsHomotopyEquivalenceInclusion
      A.sectionSevenActualAffineSplit.orderThreeFillingSubspace := by
  have hopen : IsOpen (A.sectionSevenOrderThreeFillingImage ∪
      A.sectionSevenAffineOrderThreeCentralRegion) :=
    A.sectionSevenOrderThreeFillingImage_isOpen.union
      A.sectionSevenActualAffineSplit.centralHeightLowerRegion_isOpen
  let _ : ParacompactSpace ↑(A.sectionSevenOrderThreeFillingImage ∪
      A.sectionSevenAffineOrderThreeCentralRegion) :=
    A.sectionSevenOpenSubspace_paracompact _ hopen
  let _ : NormalSpace ↑(A.sectionSevenOrderThreeFillingImage ∪
      A.sectionSevenAffineOrderThreeCentralRegion) :=
    A.sectionSevenOpenSubspace_normal _ hopen
  exact R.homotopyEquivalenceInclusion

end SectionSevenAffineOrderThreeRegularLiftInput

namespace SectionSevenAffineOrderFourRegularLiftInput

/-- The genuine order-four regular-cover quotient model constructs the actual filling-to-side
homotopy equivalence, with normality and paracompactness supplied by the analytic star. -/
public theorem actualHomotopyEquivalenceInclusion
    (R : A.SectionSevenAffineOrderFourRegularLiftInput) :
    IsHomotopyEquivalenceInclusion
      A.sectionSevenActualAffineSplit.orderFourFillingSubspace := by
  have hopen : IsOpen (A.sectionSevenOrderFourFillingImage ∪
      A.sectionSevenAffineOrderFourCentralRegion) :=
    A.sectionSevenOrderFourFillingImage_isOpen.union
      A.sectionSevenActualAffineSplit.centralHeightUpperRegion_isOpen
  let _ : ParacompactSpace ↑(A.sectionSevenOrderFourFillingImage ∪
      A.sectionSevenAffineOrderFourCentralRegion) :=
    A.sectionSevenOpenSubspace_paracompact _ hopen
  let _ : NormalSpace ↑(A.sectionSevenOrderFourFillingImage ∪
      A.sectionSevenAffineOrderFourCentralRegion) :=
    A.sectionSevenOpenSubspace_normal _ hopen
  exact R.homotopyEquivalenceInclusion

end SectionSevenAffineOrderFourRegularLiftInput

/-- The band-to-fibre map induced by the actual order-three regular-cover contraction. -/
public noncomputable def SectionSevenAffineOrderThreeRegularLiftInput.bandToReducedFiber
    (R : A.SectionSevenAffineOrderThreeRegularLiftInput) :
    C((A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior),
      OrderThreeReducedCentralFiber A.periods) :=
  (A.sectionSevenOrderThreeFillingImageHomotopyEquiv.toFun.comp
    (R.actualHomotopyEquivalenceInclusion.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph A.sectionSevenActualAffineSplit.allocation.orderThreeSide
        A.sectionSevenOrderThreeFillingImage
        A.sectionSevenActualAffineSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToLeft
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide)

/-- The band-to-fibre map induced by the actual order-four regular-cover contraction. -/
public noncomputable def SectionSevenAffineOrderFourRegularLiftInput.bandToReducedFiber
    (R : A.SectionSevenAffineOrderFourRegularLiftInput) :
    C((A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior),
      OrderFourReducedCentralFiber A.periods) :=
  (A.sectionSevenOrderFourFillingImageHomotopyEquiv.toFun.comp
    (R.actualHomotopyEquivalenceInclusion.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph A.sectionSevenActualAffineSplit.allocation.orderFourSide
        A.sectionSevenOrderFourFillingImage
        A.sectionSevenActualAffineSplit.orderFourFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToRight
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide)

/-- Exact residual affine geometry on the genuine regular cover.  The two side equivalences are
derived from explicit `Delta`-equivariant quotient models; only compatibility of those derived
contractions with the two fixed marked finite-cover projections remains as proof data. -/
public structure SectionSevenAffineRegularLiftCompletionInput where
  orderThreeRegularLift : A.SectionSevenAffineOrderThreeRegularLiftInput
  orderFourRegularLift : A.SectionSevenAffineOrderFourRegularLiftInput
  orderThreeCompatibility : orderThreeRegularLift.bandToReducedFiber.Homotopic
    (sectionSevenAffineBandOrderThreeCoverMap A)
  orderFourCompatibility : orderFourRegularLift.bandToReducedFiber.Homotopic
    (sectionSevenAffineBandOrderFourCoverMap A)

/-- The genuinely homotopy-only residual marking data after the two regular-cover quotient
models have been fixed.  This structure contains no radii, actions, quotient coordinates, or
side-equivalence assumptions. -/
public structure SectionSevenAffineRegularLiftBandCompatibilityInput
    (orderThreeRegularLift : A.SectionSevenAffineOrderThreeRegularLiftInput)
    (orderFourRegularLift : A.SectionSevenAffineOrderFourRegularLiftInput) where
  orderThreeCompatibility : orderThreeRegularLift.bandToReducedFiber.Homotopic
    (sectionSevenAffineBandOrderThreeCoverMap A)
  orderFourCompatibility : orderFourRegularLift.bandToReducedFiber.Homotopic
    (sectionSevenAffineBandOrderFourCoverMap A)

namespace SectionSevenAffineRegularLiftBandCompatibilityInput

/-- Combine fixed regular-cover quotient geometry with its two marked band homotopies. -/
public def toCompletionInput
    {orderThreeRegularLift : A.SectionSevenAffineOrderThreeRegularLiftInput}
    {orderFourRegularLift : A.SectionSevenAffineOrderFourRegularLiftInput}
    (H : A.SectionSevenAffineRegularLiftBandCompatibilityInput
      orderThreeRegularLift orderFourRegularLift) :
    A.SectionSevenAffineRegularLiftCompletionInput where
  orderThreeRegularLift := orderThreeRegularLift
  orderFourRegularLift := orderFourRegularLift
  orderThreeCompatibility := H.orderThreeCompatibility
  orderFourCompatibility := H.orderFourCompatibility

end SectionSevenAffineRegularLiftBandCompatibilityInput

namespace SectionSevenAffineRegularLiftCompletionInput

/-- Assemble the original affine radial input from the genuine regular-cover quotient models. -/
public theorem toRadialCompletion
    (R : A.SectionSevenAffineRegularLiftCompletionInput) :
    A.SectionSevenAffineRadialCompletionInput where
  orderThreeHomotopyEquivalence :=
    R.orderThreeRegularLift.actualHomotopyEquivalenceInclusion
  orderFourHomotopyEquivalence :=
    R.orderFourRegularLift.actualHomotopyEquivalenceInclusion
  orderThree_inclusion_compatibility := R.orderThreeCompatibility
  orderFour_inclusion_compatibility := R.orderFourCompatibility

end SectionSevenAffineRegularLiftCompletionInput

end SphereSixComplex.Geometry.PaperAnalyticData

end
