module

public import SphereSixComplex.Topology.PaperSectionSevenCuspEllipticMarkedCoordinateCalculationProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspFiberBandTopologicalSquare
public import SphereSixComplex.Topology.PaperCuspGeometricSpecializationProof

/-!
# Cusp-to-elliptic marked coordinates from the existing fibre geometry

The four fibre-coinvariant coordinates in the remaining Section 7 cusp calculation are not
independent scalar inputs.  They are determined by the topological square identifying the
mapping-torus fibre with the canonically marked elliptic band, together with the already proved
finite-cover homology calculation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.LatticeData
open SphereSixComplex.LatticeWangAlgebra
open SphereSixComplex.Topology.PaperCuspSpecializationAlgebra
open SectionSevenEllipticInteriorMarkedCycleData
open SectionSevenEllipticTwoDiscHomologyCoordinates
open SectionSevenEllipticTwoDiscCoverData

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

namespace SectionSevenEllipticTwoDiscCoverData

private theorem geometricWangSplitting_coinvariantsToTotal
    {HighRelations High Total LowRelations Low : Type*}
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low]
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (x : P.Coinvariants) :
    P.totalLinearEquivCoinvariantsProdInvariantsOfSection S (P.coinvariantsToTotal x) =
      (x, 0) := by
  apply (P.totalLinearEquivCoinvariantsProdInvariantsOfSection S).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change P.coinvariantsToTotal x = P.coinvariantsToTotal x + S.lift 0
  rw [map_zero, add_zero]

private theorem mZeroCoinvariantsEquivIntSquared_mk (x : Lattice) :
    mZeroCoinvariantsEquivIntSquared (Submodule.Quotient.mk x) =
      headCoordinateProjection x := by
  rfl

private theorem degreeOneCoinvariantEquiv_mk
    (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)
    (z : IntegralSingularHomology 1 D.orderThreeSide ×
      IntegralSingularHomology 1 D.orderFourSide) :
    B.degreeOneCoinvariantEquiv (Submodule.Quotient.mk z) =
      ellipticActualHOneCokernelFunctional (B.sidesOne z) := by
  rfl

private theorem degreeTwoCoinvariantEquiv_mk
    (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)
    (z : IntegralSingularHomology 2 D.orderThreeSide ×
      IntegralSingularHomology 2 D.orderFourSide) :
    B.degreeTwoCoinvariantEquiv (Submodule.Quotient.mk z) =
      alphaTwoFunctional (B.sidesTwo z) := by
  rfl

/-- Include the elliptic band into the literal union through the order-three side. -/
public def canonicalBandToEllipticUnionMap :
    C((D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior),
      (D.orderThreeSide ∪ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :=
  (IntegralMayerVietoris.leftToUnion D.orderThreeSide D.orderFourSide).comp
    (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide)

public def canonicalBandToEllipticInteriorInclusionMap :
    C((D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior),
      A.SectionSevenEllipticInterior) :=
  ⟨Subtype.val, continuous_subtype_val⟩

public theorem ellipticInteriorEquiv_symm_bandInclusion
    (k : ℕ)
    (x : IntegralSingularHomology k
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    (integralSingularHomologyEquiv k
      (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
        (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)).symm
        (integralSingularHomologyMap k
          (canonicalBandToEllipticInteriorInclusionMap D) x) =
      integralSingularHomologyMap k (canonicalBandToEllipticUnionMap D) x := by
  let eTop := integralSingularHomologyEquiv k
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  apply eTop.injective
  rw [eTop.apply_symm_apply]
  change integralSingularHomologyMap k
      (canonicalBandToEllipticInteriorInclusionMap D) x =
    integralSingularHomologyMap k
      ⟨topologicalSubsetHomeomorphOfEqUniv
        (TopCat.of A.SectionSevenEllipticInterior)
        (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover,
        (topologicalSubsetHomeomorphOfEqUniv
          (TopCat.of A.SectionSevenEllipticInterior)
          (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover).continuous⟩
      (integralSingularHomologyMap k (canonicalBandToEllipticUnionMap D) x)
  rw [integralSingularHomologyMap_comp_wang]
  congr 2

public theorem canonicalBandToEllipticUnionHomologyOne_eq_coinvariants
    (x : IntegralSingularHomology 1
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    integralSingularHomologyMap 1 (canonicalBandToEllipticUnionMap D) x =
      (presentationOne (D := D)).coinvariantsToTotal
        (Submodule.Quotient.mk
          (integralSingularHomologyMap 1
            (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0)) := by
  unfold canonicalBandToEllipticUnionMap
  rw [← integralSingularHomologyMap_comp_wang]
  rw [WangHomologyPresentation.coinvariantsToTotal, Submodule.liftQ_apply]
  change _ = IntegralMayerVietoris.sumMap D.orderThreeSide D.orderFourSide 1 (_, 0)
  simp [IntegralMayerVietoris.sumMap]

public theorem canonicalBandToEllipticUnionHomologyTwo_eq_coinvariants
    (x : IntegralSingularHomology 2
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    integralSingularHomologyMap 2 (canonicalBandToEllipticUnionMap D) x =
      (presentationTwo (D := D)).coinvariantsToTotal
        (Submodule.Quotient.mk
          (integralSingularHomologyMap 2
            (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0)) := by
  unfold canonicalBandToEllipticUnionMap
  rw [← integralSingularHomologyMap_comp_wang]
  rw [WangHomologyPresentation.coinvariantsToTotal, Submodule.liftQ_apply]
  change _ = IntegralMayerVietoris.sumMap D.orderThreeSide D.orderFourSide 2 (_, 0)
  simp [IntegralMayerVietoris.sumMap]

public theorem normalizedUnionHomologyOneEquiv_canonicalBand
    (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)
    (x : IntegralSingularHomology 1
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    B.normalizedUnionHomologyOneEquiv
        (integralSingularHomologyMap 1 (canonicalBandToEllipticUnionMap D) x) 0 =
      ellipticActualHOneCokernelFunctional
        (B.sidesOne
          (integralSingularHomologyMap 1
            (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0)) := by
  rw [canonicalBandToEllipticUnionHomologyOne_eq_coinvariants]
  rw [B.normalizedUnionHomologyOneEquiv_coinvariantsToTotal]
  exact degreeOneCoinvariantEquiv_mk D B _

public theorem normalizedUnionHomologyTwoEquiv_canonicalBand
    (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (x : IntegralSingularHomology 2
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    B.normalizedUnionHomologyTwoEquiv S
        (integralSingularHomologyMap 2 (canonicalBandToEllipticUnionMap D) x) 0 =
      alphaTwoFunctional
        (B.sidesTwo
          (integralSingularHomologyMap 2
            (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0)) := by
  rw [canonicalBandToEllipticUnionHomologyTwo_eq_coinvariants]
  let c : (presentationTwo (D := D)).Coinvariants :=
    Submodule.Quotient.mk
      (integralSingularHomologyMap 2
        (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0)
  have h := congrFun (B.normalizedUnionHomologyTwoEquiv_add S c 0) (0 : Fin 2)
  simp only [map_zero, add_zero] at h
  rw [h]
  exact degreeTwoCoinvariantEquiv_mk D B _

/-- The degree-two homology map induced by the canonical geometric cusp-fibre-to-band map. -/
public noncomputable def canonicalCuspFiberToBandHomologyTwo :
    (let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 2 G.Fiber) →+
      IntegralSingularHomology 2
        (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact integralSingularHomologyMap 2 D.canonicalCuspFiberToBandMap

/-- Applying the band equivalence cancels its inverse in the canonical fibre map in degree two. -/
public theorem bandHomologyEquiv_canonicalCuspFiberToBandHomologyTwo
    (x : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 2 G.Fiber) :
    D.bandHomologyEquiv 2 (D.canonicalCuspFiberToBandHomologyTwo x) =
      (let G := A.actualCuspRadialClutchingData
       let _ := G.fiberTopology
       integralSingularHomologyMap 2 D.canonicalCuspFiberToBandTorusHomeomorph x) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [show D.canonicalCuspFiberToBandHomologyTwo x =
      integralSingularHomologyMap 2 D.canonicalCuspFiberToBandMap x by rfl]
  rw [show integralSingularHomologyMap 2 D.canonicalCuspFiberToBandMap =
      (integralSingularHomologyMap 2 D.bandHomotopyEquiv.invFun).comp
        (integralSingularHomologyMap 2
          D.canonicalCuspFiberToBandTorusHomeomorph) by
    exact integralSingularHomologyMap_comp 2 _ _]
  exact (integralSingularHomologyEquivOfHomotopyEquiv 2
    D.bandHomotopyEquiv).apply_symm_apply _

/-- The canonical fibre-to-band map preserves the complete degree-two period marking. -/
public theorem canonicalCuspFiberToBand_degreeTwoPeriodMarking
    (x : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 2 G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (EstablishedTorusHomology.additiveTorusHomologyBasis
      D.bandParameter D.bandFullRank).degreeTwo
        (integralSingularHomologyMap 2 D.canonicalCuspFiberToBandTorusHomeomorph x) =
      G.monodromyCoordinates.degreeTwo x := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let y := integralSingularHomologyMap 2
    ⟨G.fiberHomeomorph, G.fiberHomeomorph.continuous⟩ x
  let e := fullRankAdditiveTorusHomeomorph
    G.fiberParameter D.bandParameter G.fiberFullRank D.bandFullRank
  have hNatural :=
    (EstablishedTorusHomology.fullRankAdditiveTorusHomeomorph_naturality
      G.fiberParameter D.bandParameter G.fiberFullRank D.bandFullRank).2 y
  have hComposite :
      integralSingularHomologyMap 2 D.canonicalCuspFiberToBandTorusHomeomorph x =
        integralSingularHomologyMap 2 ⟨e, e.continuous⟩ y := by
    change integralSingularHomologyMap 2
        ⟨G.fiberHomeomorph.trans e, (G.fiberHomeomorph.trans e).continuous⟩ x = _
    exact DFunLike.congr_fun (integralSingularHomologyMap_comp 2
      ⟨G.fiberHomeomorph, G.fiberHomeomorph.continuous⟩ ⟨e, e.continuous⟩) x
  rw [hComposite]
  exact hNatural.trans (G.fiberMarkingCompatibilityTwo x)

/-- The canonical fibre-to-band map preserves the complete degree-one period marking. -/
public theorem canonicalCuspFiberToBand_degreeOnePeriodMarking
    (x : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (EstablishedTorusHomology.additiveTorusHomologyBasis
      D.bandParameter D.bandFullRank).degreeOne
        (D.canonicalCuspFiberToBandTorusHomologyOne x) =
      G.monodromyCoordinates.degreeOne x := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let y := integralSingularHomologyMap 1
    ⟨G.fiberHomeomorph, G.fiberHomeomorph.continuous⟩ x
  let e := fullRankAdditiveTorusHomeomorph
    G.fiberParameter D.bandParameter G.fiberFullRank D.bandFullRank
  have hNatural :=
    (EstablishedTorusHomology.fullRankAdditiveTorusHomeomorph_naturality
      G.fiberParameter D.bandParameter G.fiberFullRank D.bandFullRank).1 y
  have hComposite :
      D.canonicalCuspFiberToBandTorusHomologyOne x =
        integralSingularHomologyMap 1 ⟨e, e.continuous⟩ y := by
    change integralSingularHomologyMap 1
        ⟨G.fiberHomeomorph.trans e, (G.fiberHomeomorph.trans e).continuous⟩ x = _
    exact DFunLike.congr_fun (integralSingularHomologyMap_comp 1
      ⟨G.fiberHomeomorph, G.fiberHomeomorph.continuous⟩ ⟨e, e.continuous⟩) x
  rw [hComposite]
  exact hNatural.trans (G.fiberMarkingCompatibility x)

/-- A fibre class representing the `i`-th degree-one coinvariant basis vector in the geometric
Wang coordinates. -/
public noncomputable def actualCuspFiberCoinvariantHomologyOneBasis
    (A : PaperAnalyticData) (i : Fin 2) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1 G.Fiber := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let q : Fin 2 → ℤ := Pi.single i 1
  exact G.monodromyCoordinates.degreeOne.symm ![q 0, q 1, 0, 0]

/-- The selected degree-one fibre classes are the first two geometric Wang basis vectors. -/
public theorem actualCuspFiberCoinvariantHomologyOneBasis_inclusion
    (A : PaperAnalyticData) (i : Fin 2) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.geometricWangSections.circleMappingTorusHOneAddEquiv
        (integralSingularHomologyMap 1
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
          (actualCuspFiberCoinvariantHomologyOneBasis A i)) =
      Pi.single (Fin.castAdd 1 i) 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let P := circleMappingTorusHOnePresentation G.clutching
  have hCoordinates :
      G.monodromyCoordinates.degreeOne
          (actualCuspFiberCoinvariantHomologyOneBasis A i) =
        ![(Pi.single i 1 : Fin 2 → ℤ) 0,
          (Pi.single i 1 : Fin 2 → ℤ) 1, 0, 0] := by
    change G.monodromyCoordinates.degreeOne
        (G.monodromyCoordinates.degreeOne.symm _) = _
    exact G.monodromyCoordinates.degreeOne.apply_symm_apply _
  have hCoinvariant :
      honeCoinv G.monodromyCoordinates
          (Submodule.Quotient.mk
            (actualCuspFiberCoinvariantHomologyOneBasis A i)) =
        Pi.single i 1 := by
    change mZeroCoinvariantsEquivIntSquared
        (Submodule.Quotient.mk
          (G.monodromyCoordinates.degreeOne
            (actualCuspFiberCoinvariantHomologyOneBasis A i))) = _
    rw [mZeroCoinvariantsEquivIntSquared_mk, hCoordinates]
    simp [headCoordinateProjection]
    funext j
    fin_cases i <;> fin_cases j <;> rfl
  change G.geometricWangSections.circleMappingTorusHOneAddEquiv
      (integralSingularHomologyMap 1
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
        (actualCuspFiberCoinvariantHomologyOneBasis A i)) = _
  rw [circleMappingTorusHOneAddEquiv_apply]
  have hFiber :
      integralSingularHomologyMap 1
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
          (actualCuspFiberCoinvariantHomologyOneBasis A i) =
        P.coinvariantsToTotal
          (Submodule.Quotient.mk (actualCuspFiberCoinvariantHomologyOneBasis A i)) := by
    rfl
  rw [hFiber]
  rw [show honeSplit G.geometricWangSections.degreeOne =
      P.totalLinearEquivCoinvariantsProdInvariantsOfSection
        G.geometricWangSections.degreeOne by rfl]
  rw [geometricWangSplitting_coinvariantsToTotal]
  rw [hCoinvariant]
  rw [map_zero]
  funext j
  fin_cases i <;> fin_cases j <;> rfl

/-- A fibre class representing the `i`-th degree-two coinvariant basis vector in the geometric
Wang coordinates. -/
public noncomputable def actualCuspFiberCoinvariantHomologyTwoBasis
    (A : PaperAnalyticData) (i : Fin 4) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 2 G.Fiber := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let q : Fin 4 → ℤ := Pi.single i 1
  exact G.monodromyCoordinates.degreeTwo.symm ![q 0, q 3, q 1, q 2, 0, 0]

/-- The selected fibre classes are the first four geometric Wang basis vectors. -/
public theorem actualCuspFiberCoinvariantHomologyTwoBasis_inclusion
    (A : PaperAnalyticData) (i : Fin 4) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.geometricWangSections.circleMappingTorusHTwoAddEquiv
        (integralSingularHomologyMap 2
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
          (actualCuspFiberCoinvariantHomologyTwoBasis A i)) =
      Pi.single (Fin.castAdd 2 i) 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let P := circleMappingTorusHTwoPresentation G.clutching
  have hCoordinates :
      G.monodromyCoordinates.degreeTwo
          (actualCuspFiberCoinvariantHomologyTwoBasis A i) =
        ![(Pi.single i 1 : Fin 4 → ℤ) 0,
          (Pi.single i 1 : Fin 4 → ℤ) 3,
          (Pi.single i 1 : Fin 4 → ℤ) 1,
          (Pi.single i 1 : Fin 4 → ℤ) 2, 0, 0] := by
    change G.monodromyCoordinates.degreeTwo
        (G.monodromyCoordinates.degreeTwo.symm _) = _
    exact G.monodromyCoordinates.degreeTwo.apply_symm_apply _
  have hCoinvariant :
      htwoCoinv G.monodromyCoordinates
          (Submodule.Quotient.mk
            (actualCuspFiberCoinvariantHomologyTwoBasis A i)) =
        Pi.single i 1 := by
    change mZeroExteriorTwoCoinvariantsEquivIntFourth
        (Submodule.Quotient.mk
          (G.monodromyCoordinates.degreeTwo
            (actualCuspFiberCoinvariantHomologyTwoBasis A i))) = _
    rw [mZeroExteriorTwoCoinvariantsEquivIntFourth_mk]
    rw [hCoordinates]
    simp [mZeroExteriorTwoProjection]
    funext j
    fin_cases i <;> fin_cases j <;> rfl
  change G.geometricWangSections.circleMappingTorusHTwoAddEquiv
      (integralSingularHomologyMap 2
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
        (actualCuspFiberCoinvariantHomologyTwoBasis A i)) = _
  rw [circleMappingTorusHTwoAddEquiv_apply]
  have hFiber :
      integralSingularHomologyMap 2
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))
          (actualCuspFiberCoinvariantHomologyTwoBasis A i) =
        P.coinvariantsToTotal
          (Submodule.Quotient.mk (actualCuspFiberCoinvariantHomologyTwoBasis A i)) := by
    rfl
  rw [hFiber]
  rw [show htwoSplit G.geometricWangSections.degreeTwo =
      P.totalLinearEquivCoinvariantsProdInvariantsOfSection
        G.geometricWangSections.degreeTwo by rfl]
  rw [geometricWangSplitting_coinvariantsToTotal]
  rw [hCoinvariant]
  rw [map_zero]
  funext j
  fin_cases i <;> fin_cases j <;> rfl

/-- Assuming exactly the space-level cusp-fibre-to-band square, the first two degree-one Wang
basis classes map to the canonical marked band classes. -/
public theorem actualCuspDegreeOneFiberBasis_eq_canonicalBand
    (hTop : D.CanonicalCuspFiberBandTopologicalCompatibility) (i : Fin 2) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap 1 D.cuspMappingTorusToEllipticInteriorMap
        (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
          (Pi.single (Fin.castAdd 1 i) 1)) =
      integralSingularHomologyMap 1 D.canonicalCuspFiberToEllipticInteriorMap
        (actualCuspFiberCoinvariantHomologyOneBasis A i) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let x := actualCuspFiberCoinvariantHomologyOneBasis A i
  have hClass :
      G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
          (Pi.single (Fin.castAdd 1 i) 1) =
        integralSingularHomologyMap 1
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) x := by
    apply G.geometricWangSections.circleMappingTorusHOneAddEquiv.injective
    rw [G.geometricWangSections.circleMappingTorusHOneAddEquiv.apply_symm_apply]
    exact (actualCuspFiberCoinvariantHomologyOneBasis_inclusion A i).symm
  change integralSingularHomologyMap 1 D.cuspMappingTorusToEllipticInteriorMap
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
        (Pi.single (Fin.castAdd 1 i) 1)) =
    integralSingularHomologyMap 1 D.canonicalCuspFiberToEllipticInteriorMap x
  rw [hClass]
  rw [integralSingularHomologyMap_comp_wang]
  exact DFunLike.congr_fun (D.canonicalCuspFiberBand_homology_naturality hTop 1) x

/-- Assuming the same space-level square, the first four degree-two Wang basis classes map to
the canonical marked band classes. -/
public theorem actualCuspDegreeTwoFiberBasis_eq_canonicalBand
    (hTop : D.CanonicalCuspFiberBandTopologicalCompatibility) (i : Fin 4) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap 2 D.cuspMappingTorusToEllipticInteriorMap
        (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
          (Pi.single (Fin.castAdd 2 i) 1)) =
      integralSingularHomologyMap 2 D.canonicalCuspFiberToEllipticInteriorMap
        (actualCuspFiberCoinvariantHomologyTwoBasis A i) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let x := actualCuspFiberCoinvariantHomologyTwoBasis A i
  have hClass :
      G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
          (Pi.single (Fin.castAdd 2 i) 1) =
        integralSingularHomologyMap 2
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) x := by
    apply G.geometricWangSections.circleMappingTorusHTwoAddEquiv.injective
    rw [G.geometricWangSections.circleMappingTorusHTwoAddEquiv.apply_symm_apply]
    exact (actualCuspFiberCoinvariantHomologyTwoBasis_inclusion A i).symm
  change integralSingularHomologyMap 2 D.cuspMappingTorusToEllipticInteriorMap
      (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
        (Pi.single (Fin.castAdd 2 i) 1)) =
    integralSingularHomologyMap 2 D.canonicalCuspFiberToEllipticInteriorMap x
  rw [hClass]
  rw [integralSingularHomologyMap_comp_wang]
  exact DFunLike.congr_fun (D.canonicalCuspFiberBand_homology_naturality hTop 2) x

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end
