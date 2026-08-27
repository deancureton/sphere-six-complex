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


/-! ### Proposition-level overlap inputs

Both `actualHomotopyEquivalenceInclusion` and `bandToReducedFiber` read their regular-lift
argument only through the *proposition* `IsHomotopyEquivalenceInclusion`.  Definitional proof
irrelevance therefore makes the band map independent of the regular-lift structure, and the whole
completion package can be rebuilt from the two overlap homotopy equivalences alone.  This is what
lets the affine completion be assembled without ever exhibiting an overlap quotient model. -/

/-- The order-three overlap homotopy equivalence already gives the actual filling-to-side
inclusion equivalence; no quotient model of the overlap is needed. -/
public theorem orderThreeOverlapIsHomotopyEquivalence_inclusion
    (h : IsHomotopyEquivalence (SphereSixComplex.OpenUnionHomotopy.interToRight
      A.sectionSevenOrderThreeFillingImage
      A.sectionSevenAffineOrderThreeCentralRegion).hom) :
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
  change IsHomotopyEquivalenceInclusion
    (Subtype.val ⁻¹' A.sectionSevenOrderThreeFillingImage :
      Set ↥(A.sectionSevenOrderThreeFillingImage ∪
        A.sectionSevenAffineOrderThreeCentralRegion))
  exact SphereSixComplex.isHomotopyEquivalenceInclusion_of_leftToUnion _ _
    (SphereSixComplex.OpenUnionHomotopy.leftToUnion_isHomotopyEquivalence_of_normal_paracompact
      _ _ A.sectionSevenOrderThreeFillingImage_isOpen
      A.sectionSevenActualAffineSplit.centralHeightLowerRegion_isOpen h)

/-- The order-four overlap homotopy equivalence already gives the actual filling-to-side
inclusion equivalence; no quotient model of the overlap is needed. -/
public theorem orderFourOverlapIsHomotopyEquivalence_inclusion
    (h : IsHomotopyEquivalence (SphereSixComplex.OpenUnionHomotopy.interToRight
      A.sectionSevenOrderFourFillingImage
      A.sectionSevenAffineOrderFourCentralRegion).hom) :
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
  change IsHomotopyEquivalenceInclusion
    (Subtype.val ⁻¹' A.sectionSevenOrderFourFillingImage :
      Set ↥(A.sectionSevenOrderFourFillingImage ∪
        A.sectionSevenAffineOrderFourCentralRegion))
  exact SphereSixComplex.isHomotopyEquivalenceInclusion_of_leftToUnion _ _
    (SphereSixComplex.OpenUnionHomotopy.leftToUnion_isHomotopyEquivalence_of_normal_paracompact
      _ _ A.sectionSevenOrderFourFillingImage_isOpen
      A.sectionSevenActualAffineSplit.centralHeightUpperRegion_isOpen h)

/-- The order-three band-to-fibre map built from a bare filling-to-side inclusion equivalence. -/
public noncomputable def sectionSevenAffineOrderThreeBandToReducedFiber
    (E : IsHomotopyEquivalenceInclusion
      A.sectionSevenActualAffineSplit.orderThreeFillingSubspace) :
    C((A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior),
      OrderThreeReducedCentralFiber A.periods) :=
  (A.sectionSevenOrderThreeFillingImageHomotopyEquiv.toFun.comp
    (E.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph A.sectionSevenActualAffineSplit.allocation.orderThreeSide
        A.sectionSevenOrderThreeFillingImage
        A.sectionSevenActualAffineSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToLeft
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide)

/-- The order-four band-to-fibre map built from a bare filling-to-side inclusion equivalence. -/
public noncomputable def sectionSevenAffineOrderFourBandToReducedFiber
    (E : IsHomotopyEquivalenceInclusion
      A.sectionSevenActualAffineSplit.orderFourFillingSubspace) :
    C((A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior),
      OrderFourReducedCentralFiber A.periods) :=
  (A.sectionSevenOrderFourFillingImageHomotopyEquiv.toFun.comp
    (E.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph A.sectionSevenActualAffineSplit.allocation.orderFourSide
        A.sectionSevenOrderFourFillingImage
        A.sectionSevenActualAffineSplit.orderFourFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToRight
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide)

/-- The regular-lift band map is literally the proposition-level band map. -/
public theorem SectionSevenAffineOrderThreeRegularLiftInput.bandToReducedFiber_eq
    (R : A.SectionSevenAffineOrderThreeRegularLiftInput) :
    R.bandToReducedFiber =
      sectionSevenAffineOrderThreeBandToReducedFiber R.actualHomotopyEquivalenceInclusion :=
  rfl

/-- The regular-lift band map is literally the proposition-level band map. -/
public theorem SectionSevenAffineOrderFourRegularLiftInput.bandToReducedFiber_eq
    (R : A.SectionSevenAffineOrderFourRegularLiftInput) :
    R.bandToReducedFiber =
      sectionSevenAffineOrderFourBandToReducedFiber R.actualHomotopyEquivalenceInclusion :=
  rfl

/-- Exact residual affine data once the overlap geometry is a bare pair of homotopy
equivalences: the two overlap equivalences and the two marked band homotopies. -/
public structure SectionSevenAffineOverlapCompletionInput where
  orderThreeOverlap : IsHomotopyEquivalence (SphereSixComplex.OpenUnionHomotopy.interToRight
    A.sectionSevenOrderThreeFillingImage A.sectionSevenAffineOrderThreeCentralRegion).hom
  orderFourOverlap : IsHomotopyEquivalence (SphereSixComplex.OpenUnionHomotopy.interToRight
    A.sectionSevenOrderFourFillingImage A.sectionSevenAffineOrderFourCentralRegion).hom
  orderThreeCompatibility :
    (sectionSevenAffineOrderThreeBandToReducedFiber
      (orderThreeOverlapIsHomotopyEquivalence_inclusion orderThreeOverlap)).Homotopic
      (sectionSevenAffineBandOrderThreeCoverMap A)
  orderFourCompatibility :
    (sectionSevenAffineOrderFourBandToReducedFiber
      (orderFourOverlapIsHomotopyEquivalence_inclusion orderFourOverlap)).Homotopic
      (sectionSevenAffineBandOrderFourCoverMap A)

namespace SectionSevenAffineOverlapCompletionInput

/-- Assemble the original affine radial input from the two bare overlap homotopy equivalences. -/
public theorem toRadialCompletion
    (R : A.SectionSevenAffineOverlapCompletionInput) :
    A.SectionSevenAffineRadialCompletionInput where
  orderThreeHomotopyEquivalence :=
    orderThreeOverlapIsHomotopyEquivalence_inclusion R.orderThreeOverlap
  orderFourHomotopyEquivalence :=
    orderFourOverlapIsHomotopyEquivalence_inclusion R.orderFourOverlap
  orderThree_inclusion_compatibility := R.orderThreeCompatibility
  orderFour_inclusion_compatibility := R.orderFourCompatibility

end SectionSevenAffineOverlapCompletionInput

end SphereSixComplex.Geometry.PaperAnalyticData

end
