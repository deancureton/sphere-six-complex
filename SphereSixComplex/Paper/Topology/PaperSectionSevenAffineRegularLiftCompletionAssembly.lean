module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCompletionAssembly
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineRegularLiftCarriers

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

namespace AffineOrderThreeRegularLiftInput

/-- The genuine order-three regular-cover quotient model constructs the actual filling-to-side
homotopy equivalence, with normality and paracompactness supplied by the analytic star. -/
public theorem actualHomotopyEquivalenceInclusion
    (R : A.AffineOrderThreeRegularLiftInput) :
    IsHomotopyEquivalenceInclusion
      A.actualAffineHeightSplit.orderThreeFillingSubspace := by
  have hopen : IsOpen (A.orderThreeFillingImage ∪
      A.affineOrderThreeCentralRegion) :=
    A.orderThreeFillingImage_isOpen.union
      A.actualAffineHeightSplit.centralHeightLowerRegion_isOpen
  let _ : ParacompactSpace ↑(A.orderThreeFillingImage ∪
      A.affineOrderThreeCentralRegion) :=
    A.ellipticInteriorOpenSubspace_paracompact _ hopen
  let _ : NormalSpace ↑(A.orderThreeFillingImage ∪
      A.affineOrderThreeCentralRegion) :=
    A.ellipticInteriorOpenSubspace_normal _ hopen
  exact R.homotopyEquivalenceInclusion

end AffineOrderThreeRegularLiftInput

namespace AffineOrderFourRegularLiftInput

/-- The genuine order-four regular-cover quotient model constructs the actual filling-to-side
homotopy equivalence, with normality and paracompactness supplied by the analytic star. -/
public theorem actualHomotopyEquivalenceInclusion
    (R : A.AffineOrderFourRegularLiftInput) :
    IsHomotopyEquivalenceInclusion
      A.actualAffineHeightSplit.orderFourFillingSubspace := by
  have hopen : IsOpen (A.orderFourFillingImage ∪
      A.affineOrderFourCentralRegion) :=
    A.orderFourFillingImage_isOpen.union
      A.actualAffineHeightSplit.centralHeightUpperRegion_isOpen
  let _ : ParacompactSpace ↑(A.orderFourFillingImage ∪
      A.affineOrderFourCentralRegion) :=
    A.ellipticInteriorOpenSubspace_paracompact _ hopen
  let _ : NormalSpace ↑(A.orderFourFillingImage ∪
      A.affineOrderFourCentralRegion) :=
    A.ellipticInteriorOpenSubspace_normal _ hopen
  exact R.homotopyEquivalenceInclusion

end AffineOrderFourRegularLiftInput

/-- The band-to-fibre map induced by the actual order-three regular-cover contraction. -/
public noncomputable def AffineOrderThreeRegularLiftInput.bandToReducedFiber
    (R : A.AffineOrderThreeRegularLiftInput) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      OrderThreeReducedCentralFiber A.periods) :=
  (A.orderThreeFillingImageHomotopyEquiv.toFun.comp
    (R.actualHomotopyEquivalenceInclusion.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderThreeSide
        A.orderThreeFillingImage
        A.actualAffineHeightSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToLeft
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide)

/-- The band-to-fibre map induced by the actual order-four regular-cover contraction. -/
public noncomputable def AffineOrderFourRegularLiftInput.bandToReducedFiber
    (R : A.AffineOrderFourRegularLiftInput) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      OrderFourReducedCentralFiber A.periods) :=
  (A.orderFourFillingImageHomotopyEquiv.toFun.comp
    (R.actualHomotopyEquivalenceInclusion.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderFourSide
        A.orderFourFillingImage
        A.actualAffineHeightSplit.orderFourFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToRight
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide)

/-- Exact residual affine geometry on the genuine regular cover.  The two side equivalences are
derived from explicit `Delta`-equivariant quotient models; only compatibility of those derived
contractions with the two fixed marked finite-cover projections remains as proof data. -/
public structure AffineRegularLiftCompletionInput where
  orderThreeRegularLift : A.AffineOrderThreeRegularLiftInput
  orderFourRegularLift : A.AffineOrderFourRegularLiftInput
  orderThreeCompatibility : orderThreeRegularLift.bandToReducedFiber.Homotopic
    (affineBandOrderThreeCoverMap A)
  orderFourCompatibility : orderFourRegularLift.bandToReducedFiber.Homotopic
    (affineBandOrderFourCoverMap A)

/-- The genuinely homotopy-only residual marking data after the two regular-cover quotient
models have been fixed.  This structure contains no radii, actions, quotient coordinates, or
side-equivalence assumptions. -/
public structure AffineRegularLiftBandCompatibilityInput
    (orderThreeRegularLift : A.AffineOrderThreeRegularLiftInput)
    (orderFourRegularLift : A.AffineOrderFourRegularLiftInput) where
  orderThreeCompatibility : orderThreeRegularLift.bandToReducedFiber.Homotopic
    (affineBandOrderThreeCoverMap A)
  orderFourCompatibility : orderFourRegularLift.bandToReducedFiber.Homotopic
    (affineBandOrderFourCoverMap A)

namespace AffineRegularLiftBandCompatibilityInput

/-- Combine fixed regular-cover quotient geometry with its two marked band homotopies. -/
public def toCompletionInput
    {orderThreeRegularLift : A.AffineOrderThreeRegularLiftInput}
    {orderFourRegularLift : A.AffineOrderFourRegularLiftInput}
    (H : A.AffineRegularLiftBandCompatibilityInput
      orderThreeRegularLift orderFourRegularLift) :
    A.AffineRegularLiftCompletionInput where
  orderThreeRegularLift := orderThreeRegularLift
  orderFourRegularLift := orderFourRegularLift
  orderThreeCompatibility := H.orderThreeCompatibility
  orderFourCompatibility := H.orderFourCompatibility

end AffineRegularLiftBandCompatibilityInput

namespace AffineRegularLiftCompletionInput

/-- Assemble the original affine radial input from the genuine regular-cover quotient models. -/
public theorem toRadialCompletion
    (R : A.AffineRegularLiftCompletionInput) :
    A.AffineRadialCompletionInput where
  orderThreeHomotopyEquivalence :=
    R.orderThreeRegularLift.actualHomotopyEquivalenceInclusion
  orderFourHomotopyEquivalence :=
    R.orderFourRegularLift.actualHomotopyEquivalenceInclusion
  orderThree_inclusion_compatibility := R.orderThreeCompatibility
  orderFour_inclusion_compatibility := R.orderFourCompatibility

end AffineRegularLiftCompletionInput


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
      A.orderThreeFillingImage
      A.affineOrderThreeCentralRegion).hom) :
    IsHomotopyEquivalenceInclusion
      A.actualAffineHeightSplit.orderThreeFillingSubspace := by
  have hopen : IsOpen (A.orderThreeFillingImage ∪
      A.affineOrderThreeCentralRegion) :=
    A.orderThreeFillingImage_isOpen.union
      A.actualAffineHeightSplit.centralHeightLowerRegion_isOpen
  let _ : ParacompactSpace ↑(A.orderThreeFillingImage ∪
      A.affineOrderThreeCentralRegion) :=
    A.ellipticInteriorOpenSubspace_paracompact _ hopen
  let _ : NormalSpace ↑(A.orderThreeFillingImage ∪
      A.affineOrderThreeCentralRegion) :=
    A.ellipticInteriorOpenSubspace_normal _ hopen
  change IsHomotopyEquivalenceInclusion
    (Subtype.val ⁻¹' A.orderThreeFillingImage :
      Set ↥(A.orderThreeFillingImage ∪
        A.affineOrderThreeCentralRegion))
  exact SphereSixComplex.isHomotopyEquivalenceInclusion_of_leftToUnion _ _
    (SphereSixComplex.OpenUnionHomotopy.leftToUnion_isHomotopyEquivalence_of_normal_paracompact
      _ _ A.orderThreeFillingImage_isOpen
      A.actualAffineHeightSplit.centralHeightLowerRegion_isOpen h)

/-- The order-four overlap homotopy equivalence already gives the actual filling-to-side
inclusion equivalence; no quotient model of the overlap is needed. -/
public theorem orderFourOverlapIsHomotopyEquivalence_inclusion
    (h : IsHomotopyEquivalence (SphereSixComplex.OpenUnionHomotopy.interToRight
      A.orderFourFillingImage
      A.affineOrderFourCentralRegion).hom) :
    IsHomotopyEquivalenceInclusion
      A.actualAffineHeightSplit.orderFourFillingSubspace := by
  have hopen : IsOpen (A.orderFourFillingImage ∪
      A.affineOrderFourCentralRegion) :=
    A.orderFourFillingImage_isOpen.union
      A.actualAffineHeightSplit.centralHeightUpperRegion_isOpen
  let _ : ParacompactSpace ↑(A.orderFourFillingImage ∪
      A.affineOrderFourCentralRegion) :=
    A.ellipticInteriorOpenSubspace_paracompact _ hopen
  let _ : NormalSpace ↑(A.orderFourFillingImage ∪
      A.affineOrderFourCentralRegion) :=
    A.ellipticInteriorOpenSubspace_normal _ hopen
  change IsHomotopyEquivalenceInclusion
    (Subtype.val ⁻¹' A.orderFourFillingImage :
      Set ↥(A.orderFourFillingImage ∪
        A.affineOrderFourCentralRegion))
  exact SphereSixComplex.isHomotopyEquivalenceInclusion_of_leftToUnion _ _
    (SphereSixComplex.OpenUnionHomotopy.leftToUnion_isHomotopyEquivalence_of_normal_paracompact
      _ _ A.orderFourFillingImage_isOpen
      A.actualAffineHeightSplit.centralHeightUpperRegion_isOpen h)

/-- The order-three band-to-fibre map built from a bare filling-to-side inclusion equivalence. -/
public noncomputable def affineOrderThreeBandToReducedFiber
    (E : IsHomotopyEquivalenceInclusion
      A.actualAffineHeightSplit.orderThreeFillingSubspace) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      OrderThreeReducedCentralFiber A.periods) :=
  (A.orderThreeFillingImageHomotopyEquiv.toFun.comp
    (E.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderThreeSide
        A.orderThreeFillingImage
        A.actualAffineHeightSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToLeft
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide)

/-- The order-four band-to-fibre map built from a bare filling-to-side inclusion equivalence. -/
public noncomputable def affineOrderFourBandToReducedFiber
    (E : IsHomotopyEquivalenceInclusion
      A.actualAffineHeightSplit.orderFourFillingSubspace) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      OrderFourReducedCentralFiber A.periods) :=
  (A.orderFourFillingImageHomotopyEquiv.toFun.comp
    (E.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderFourSide
        A.orderFourFillingImage
        A.actualAffineHeightSplit.orderFourFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToRight
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide)

/-- The regular-lift band map is literally the proposition-level band map. -/
public theorem AffineOrderThreeRegularLiftInput.bandToReducedFiber_eq
    (R : A.AffineOrderThreeRegularLiftInput) :
    R.bandToReducedFiber =
      affineOrderThreeBandToReducedFiber R.actualHomotopyEquivalenceInclusion :=
  rfl

/-- The regular-lift band map is literally the proposition-level band map. -/
public theorem AffineOrderFourRegularLiftInput.bandToReducedFiber_eq
    (R : A.AffineOrderFourRegularLiftInput) :
    R.bandToReducedFiber =
      affineOrderFourBandToReducedFiber R.actualHomotopyEquivalenceInclusion :=
  rfl

/-- Exact residual affine data once the overlap geometry is a bare pair of homotopy
equivalences: the two overlap equivalences and the two marked band homotopies. -/
public structure AffineOverlapCompletionInput where
  orderThreeOverlap : IsHomotopyEquivalence (SphereSixComplex.OpenUnionHomotopy.interToRight
    A.orderThreeFillingImage A.affineOrderThreeCentralRegion).hom
  orderFourOverlap : IsHomotopyEquivalence (SphereSixComplex.OpenUnionHomotopy.interToRight
    A.orderFourFillingImage A.affineOrderFourCentralRegion).hom
  orderThreeCompatibility :
    (affineOrderThreeBandToReducedFiber
      (orderThreeOverlapIsHomotopyEquivalence_inclusion orderThreeOverlap)).Homotopic
      (affineBandOrderThreeCoverMap A)
  orderFourCompatibility :
    (affineOrderFourBandToReducedFiber
      (orderFourOverlapIsHomotopyEquivalence_inclusion orderFourOverlap)).Homotopic
      (affineBandOrderFourCoverMap A)

namespace AffineOverlapCompletionInput

/-- Assemble the original affine radial input from the two bare overlap homotopy equivalences. -/
public theorem toRadialCompletion
    (R : A.AffineOverlapCompletionInput) :
    A.AffineRadialCompletionInput where
  orderThreeHomotopyEquivalence :=
    orderThreeOverlapIsHomotopyEquivalence_inclusion R.orderThreeOverlap
  orderFourHomotopyEquivalence :=
    orderFourOverlapIsHomotopyEquivalence_inclusion R.orderFourOverlap
  orderThree_inclusion_compatibility := R.orderThreeCompatibility
  orderFour_inclusion_compatibility := R.orderFourCompatibility

end AffineOverlapCompletionInput

end SphereSixComplex.Geometry.PaperAnalyticData

end
