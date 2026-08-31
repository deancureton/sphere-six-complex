module

public import SphereSixComplex.Topology.PaperSectionSevenAffineCuspFiberPeriodMarking
public import
  SphereSixComplex.Topology.PaperSectionSevenCuspEllipticMarkedCoordinateFromExistingGeometry

/-!
# Actual cusp coordinate scalars from the existing geometry

The order-three side of the elliptic two-disc cover gives the literal scalar fibre coordinates.
For the actual affine cover, its period marking then evaluates the selected cusp fibre bases.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Matrix Set
open scoped ContinuousMap

namespace SphereSixComplex

open SphereSixComplex.Geometry SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open Topology.PaperEllipticFillingRadialRetraction
open Topology.FiniteCoverPerfectPairing
open Topology.PaperEllipticReducedCentralFiberCoverModels

private theorem orderThreeCoverSourceDegreeTwo_symm_aux
    {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U)
    (z : IntegralSingularHomology 2 (AdditiveTorus (parameterMap F U.zOne).1)) :
    (orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo
        (integralSingularHomologyMap 2
          (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
            (orderThreeRadialActionData F)).symm z) =
      (orderThreeTorusHomologyBasis F).degreeTwo z := by
  let e := RadialEllipticActionData.centralFiberCoverSourceHomeomorph
    (orderThreeRadialActionData F)
  have h : integralSingularHomologyEquiv 2 e
      (integralSingularHomologyMap 2 e.symm z) = z :=
    (integralSingularHomologyEquiv 2 e).apply_symm_apply z
  exact congrArg (orderThreeTorusHomologyBasis F).degreeTwo h

namespace Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData
open SphereSixComplex.Topology.PaperLemmaSevenThirteenAlgebra
open SectionSevenEllipticTwoDiscHomologyCoordinates

variable {A : PaperAnalyticData} {D : A.SectionSevenEllipticTwoDiscCoverData}

private theorem affineTwoDiscCover_degreeTwoBasis_aux
    (R : A.SectionSevenAffineRadialCompletionInput)
    (z : IntegralSingularHomology 2 (AdditiveTorus R.twoDiscCover.bandParameter)) :
    (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo
        (integralSingularHomologyMap 2 R.twoDiscCover.bandToOrderThreeCoverSource z) =
      (EstablishedTorusHomology.additiveTorusHomologyBasis
        R.twoDiscCover.bandParameter R.twoDiscCover.bandFullRank).degreeTwo z :=
  orderThreeCoverSourceDegreeTwo_symm_aux A.periods z

namespace SectionSevenEllipticTwoDiscCoverData

private theorem sideHomologyEquiv_interToLeft_aux (k : ℕ)
    (x : IntegralSingularHomology k
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    D.sideHomologyEquiv k
        (integralSingularHomologyMap k
          (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0) =
      (integralSingularHomologyMap k D.orderThreeBandProjection
          (D.bandHomologyEquiv k x), 0) := by
  have hMap : integralSingularHomologyMap k
      (D.orderThreeSideHomotopyEquiv.toFun.comp
        (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide)) =
      integralSingularHomologyMap k
        (D.orderThreeBandProjection.comp D.bandHomotopyEquiv.toFun) := by
    ext y
    change ConcreteCategory.hom
        (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
          (TopCat.ofHom (D.orderThreeSideHomotopyEquiv.toFun.comp
            (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide)))) y =
      ConcreteCategory.hom
        (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
          (TopCat.ofHom (D.orderThreeBandProjection.comp D.bandHomotopyEquiv.toFun))) y
    rw [SphereSixComplex.integralSingularHomologyMap_eq_of_homotopic
      D.orderThree_inclusion_compatibility k]
    rfl
  apply Prod.ext
  · change integralSingularHomologyMap k D.orderThreeSideHomotopyEquiv.toFun
        (integralSingularHomologyMap k
          (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x) =
      integralSingularHomologyMap k D.orderThreeBandProjection
        (integralSingularHomologyMap k D.bandHomotopyEquiv.toFun x)
    calc
      _ = integralSingularHomologyMap k
          (D.orderThreeSideHomotopyEquiv.toFun.comp
            (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide)) x :=
        SphereSixComplex.integralSingularHomologyMap_comp_wang _ _ _ _
      _ = integralSingularHomologyMap k
          (D.orderThreeBandProjection.comp D.bandHomotopyEquiv.toFun) x :=
        DFunLike.congr_fun hMap x
      _ = _ := (SphereSixComplex.integralSingularHomologyMap_comp_wang _ _ _ _).symm
  · change integralSingularHomologyMap k D.orderFourSideHomotopyEquiv.toFun 0 = 0
    exact map_zero _

/-- The order-three inclusion has its literal four side coordinates in degree one. -/
public theorem actualHomologyCoordinates_sidesOne_interToLeft
    (N : A.EllipticBandHomologyAlignment D)
    (x : IntegralSingularHomology 1
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    N.actualHomologyCoordinates.sidesOne
        (integralSingularHomologyMap 1
          (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0) =
      ![3 * gamma (N.actualHomologyCoordinates.bandOne x),
        psiOne (N.actualHomologyCoordinates.bandOne x), 0, 0] := by
  let R := ellipticFiniteCoverHomologyRealization A.periods
    (establishedActualEllipticDegreeTwoHomologyBasisFiniteData A)
  change EllipticBandHomologyAlignment.sidesOne (D := D) R
      (integralSingularHomologyMap 1
        (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0) =
    ![3 * gamma (EllipticBandHomologyAlignment.bandOne (D := D) x),
      psiOne (EllipticBandHomologyAlignment.bandOne (D := D) x), 0, 0]
  unfold EllipticBandHomologyAlignment.sidesOne
  simp only [AddEquiv.trans_apply]
  rw [sideHomologyEquiv_interToLeft_aux]
  change ![
      R.orderThreeOneBasis A.periods
        (integralSingularHomologyMap 1 D.orderThreeBandProjection
          (D.bandHomologyEquiv 1 x)) 0,
      R.orderThreeOneBasis A.periods
        (integralSingularHomologyMap 1 D.orderThreeBandProjection
          (D.bandHomologyEquiv 1 x)) 1,
      R.orderFourOneBasis A.periods 0 0, R.orderFourOneBasis A.periods 0 1] = _
  rw [map_zero, EllipticBandHomologyAlignment.orderThreeOne_projection_bandOne]
  rfl

/-- The order-three inclusion has its literal four side coordinates in degree two. -/
public theorem actualHomologyCoordinates_sidesTwo_interToLeft
    (N : A.EllipticBandHomologyAlignment D)
    (x : IntegralSingularHomology 2
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    N.actualHomologyCoordinates.sidesTwo
        (integralSingularHomologyMap 2
          (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0) =
      ![(alphaTwoMatrix *ᵥ N.actualHomologyCoordinates.bandTwo x) 0,
        (alphaTwoMatrix *ᵥ N.actualHomologyCoordinates.bandTwo x) 1, 0, 0] := by
  let R := ellipticFiniteCoverHomologyRealization A.periods
    (establishedActualEllipticDegreeTwoHomologyBasisFiniteData A)
  change EllipticBandHomologyAlignment.sidesTwo (D := D) R
      (integralSingularHomologyMap 2
        (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0) =
    ![(alphaTwoMatrix *ᵥ EllipticBandHomologyAlignment.bandTwo (D := D) x) 0,
      (alphaTwoMatrix *ᵥ EllipticBandHomologyAlignment.bandTwo (D := D) x) 1, 0, 0]
  unfold EllipticBandHomologyAlignment.sidesTwo
  simp only [AddEquiv.trans_apply]
  rw [sideHomologyEquiv_interToLeft_aux]
  change ![
      R.orderThreeTwoBasis A.periods
        (integralSingularHomologyMap 2 D.orderThreeBandProjection
          (D.bandHomologyEquiv 2 x)) 0,
      R.orderThreeTwoBasis A.periods
        (integralSingularHomologyMap 2 D.orderThreeBandProjection
          (D.bandHomologyEquiv 2 x)) 1,
      R.orderFourTwoBasis A.periods 0 0, R.orderFourTwoBasis A.periods 0 1] = _
  rw [map_zero, EllipticBandHomologyAlignment.orderThreeTwo_projection_bandTwo]
  rfl

/-- The order-three one-sided inclusion has scalar coordinate `12 q₀` in degree one. -/
public theorem actualHomologyCoordinates_normalizedUnionHomologyOneEquiv_canonicalBand_zero
    (N : A.EllipticBandHomologyAlignment D)
    (x : IntegralSingularHomology 1
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
        (integralSingularHomologyMap 1 D.canonicalBandToEllipticUnionMap x) 0 =
      12 * N.actualHomologyCoordinates.bandOne x 0 := by
  rw [D.normalizedUnionHomologyOneEquiv_canonicalBand]
  rw [D.actualHomologyCoordinates_sidesOne_interToLeft]
  simp [ellipticActualHOneCokernelFunctional, gamma]
  ring

/-- The order-three one-sided inclusion has scalar coordinate `12 q₂ + 2 q₃` in degree two. -/
public theorem actualHomologyCoordinates_normalizedUnionHomologyTwoEquiv_canonicalBand_zero
    (N : A.EllipticBandHomologyAlignment D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (x : IntegralSingularHomology 2
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv S
        (integralSingularHomologyMap 2 D.canonicalBandToEllipticUnionMap x) 0 =
      12 * N.actualHomologyCoordinates.bandTwo x 2 +
        2 * N.actualHomologyCoordinates.bandTwo x 3 := by
  rw [D.normalizedUnionHomologyTwoEquiv_canonicalBand]
  rw [D.actualHomologyCoordinates_sidesTwo_interToLeft]
  simp [alphaTwoFunctional, alphaTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The actual affine band marking agrees with the cusp marking in degree one. -/
public theorem affineActualHomologyCoordinates_bandOne_canonicalCuspFiber
    (R : A.SectionSevenAffineRadialCompletionInput)
    (x : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber) :
    R.homologyAlignment.actualHomologyCoordinates.bandOne
        (R.twoDiscCover.canonicalCuspFiberToBandHomologyOne x) =
      (let G := A.actualCuspRadialClutchingData
       let _ := G.fiberTopology
       G.monodromyCoordinates.degreeOne x) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  have hMarking := R.twoDiscCover.canonicalCuspFiberBandPeriodMarking_of_orderThree
    R.homologyAlignment
    (R.canonicalCuspFiberOrderThreePeriodMarking
      (actualCuspFiberPeriodMarkingCompatibility A))
  exact DFunLike.congr_fun hMarking x

/-- The actual affine band marking agrees with the cusp marking in degree two. -/
public theorem affineActualHomologyCoordinates_bandTwo_canonicalCuspFiber
    (R : A.SectionSevenAffineRadialCompletionInput)
    (x : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 2 G.Fiber) :
    R.homologyAlignment.actualHomologyCoordinates.bandTwo
        (R.twoDiscCover.canonicalCuspFiberToBandHomologyTwo x) =
      (let G := A.actualCuspRadialClutchingData
       let _ := G.fiberTopology
       G.monodromyCoordinates.degreeTwo x) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change EllipticBandHomologyAlignment.bandTwo (D := R.twoDiscCover)
      (R.twoDiscCover.canonicalCuspFiberToBandHomologyTwo x) =
    G.monodromyCoordinates.degreeTwo x
  rw [EllipticBandHomologyAlignment.bandTwo_apply]
  rw [R.twoDiscCover.bandHomologyEquiv_canonicalCuspFiberToBandHomologyTwo]
  calc
    _ = (EstablishedTorusHomology.additiveTorusHomologyBasis
          R.twoDiscCover.bandParameter R.twoDiscCover.bandFullRank).degreeTwo
        (integralSingularHomologyMap 2
          R.twoDiscCover.canonicalCuspFiberToBandTorusHomeomorph x) :=
      affineTwoDiscCover_degreeTwoBasis_aux R _
    _ = _ := R.twoDiscCover.canonicalCuspFiberToBand_degreeTwoPeriodMarking x

/-- The canonical actual cusp fibre has scalar coordinate `12 q₀` in degree one. -/
public theorem affineNormalizedEllipticInteriorHomologyOne_canonicalCuspFiber_zero
    (R : A.SectionSevenAffineRadialCompletionInput)
    (x : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyOneEquiv
        (integralSingularHomologyMap 1
          R.twoDiscCover.canonicalCuspFiberToEllipticInteriorMap x) 0 =
      12 * G.monodromyCoordinates.degreeOne x 0 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let D := R.twoDiscCover
  let B := R.homologyAlignment.actualHomologyCoordinates
  let y := D.canonicalCuspFiberToBandHomologyOne x
  let eTop := integralSingularHomologyEquiv 1
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  change B.normalizedUnionHomologyOneEquiv
      (eTop.symm (integralSingularHomologyMap 1
        D.canonicalCuspFiberToEllipticInteriorMap x)) 0 =
    12 * G.monodromyCoordinates.degreeOne x 0
  have hMap : integralSingularHomologyMap 1 D.canonicalCuspFiberToEllipticInteriorMap x =
      integralSingularHomologyMap 1 D.canonicalBandToEllipticInteriorInclusionMap y := by
    change integralSingularHomologyMap 1
        (D.canonicalBandToEllipticInteriorInclusionMap.comp
          D.canonicalCuspFiberToBandMap) x =
      integralSingularHomologyMap 1 D.canonicalBandToEllipticInteriorInclusionMap
        (integralSingularHomologyMap 1 D.canonicalCuspFiberToBandMap x)
    exact (SphereSixComplex.integralSingularHomologyMap_comp_wang _ _ _ _).symm
  rw [hMap, D.ellipticInteriorEquiv_symm_bandInclusion]
  rw [D.actualHomologyCoordinates_normalizedUnionHomologyOneEquiv_canonicalBand_zero]
  rw [affineActualHomologyCoordinates_bandOne_canonicalCuspFiber R x]

/-- The canonical actual cusp fibre has scalar coordinate `12 q₂ + 2 q₃` in degree two. -/
public theorem affineNormalizedEllipticInteriorHomologyTwo_canonicalCuspFiber_zero
    (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting
      (presentationTwo (D := R.twoDiscCover)))
    (x : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 2 G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv S
        (integralSingularHomologyMap 2
          R.twoDiscCover.canonicalCuspFiberToEllipticInteriorMap x) 0 =
      12 * G.monodromyCoordinates.degreeTwo x 2 +
        2 * G.monodromyCoordinates.degreeTwo x 3 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let D := R.twoDiscCover
  let B := R.homologyAlignment.actualHomologyCoordinates
  let y := D.canonicalCuspFiberToBandHomologyTwo x
  let eTop := integralSingularHomologyEquiv 2
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  change B.normalizedUnionHomologyTwoEquiv S
      (eTop.symm (integralSingularHomologyMap 2
        D.canonicalCuspFiberToEllipticInteriorMap x)) 0 =
    12 * G.monodromyCoordinates.degreeTwo x 2 + 2 * G.monodromyCoordinates.degreeTwo x 3
  have hMap : integralSingularHomologyMap 2 D.canonicalCuspFiberToEllipticInteriorMap x =
      integralSingularHomologyMap 2 D.canonicalBandToEllipticInteriorInclusionMap y := by
    change integralSingularHomologyMap 2
        (D.canonicalBandToEllipticInteriorInclusionMap.comp
          D.canonicalCuspFiberToBandMap) x =
      integralSingularHomologyMap 2 D.canonicalBandToEllipticInteriorInclusionMap
        (integralSingularHomologyMap 2 D.canonicalCuspFiberToBandMap x)
    exact (SphereSixComplex.integralSingularHomologyMap_comp_wang _ _ _ _).symm
  rw [hMap, D.ellipticInteriorEquiv_symm_bandInclusion]
  rw [D.actualHomologyCoordinates_normalizedUnionHomologyTwoEquiv_canonicalBand_zero]
  rw [affineActualHomologyCoordinates_bandTwo_canonicalCuspFiber R x]

/-- The two selected degree-one fibre classes have scalar values `[12, 0]`. -/
public theorem affineCanonicalCuspFiberCoinvariantHomologyOneBasis_scalarValues
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (fun i : Fin 2 ↦
      R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyOneEquiv
        (integralSingularHomologyMap 1
          R.twoDiscCover.canonicalCuspFiberToEllipticInteriorMap
          (actualCuspFiberCoinvariantHomologyOneBasis A i)) 0) = ![12, 0] := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  funext i
  rw [affineNormalizedEllipticInteriorHomologyOne_canonicalCuspFiber_zero]
  change 12 * G.monodromyCoordinates.degreeOne
      (G.monodromyCoordinates.degreeOne.symm
        ![(Pi.single i 1 : Fin 2 → ℤ) 0, (Pi.single i 1 : Fin 2 → ℤ) 1, 0, 0]) 0 = _
  rw [G.monodromyCoordinates.degreeOne.apply_symm_apply]
  fin_cases i <;> rfl

/-- The four selected degree-two fibre classes have scalar values `[0, 12, 2, 0]`. -/
public theorem affineCanonicalCuspFiberCoinvariantHomologyTwoBasis_scalarValues
    (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting
      (presentationTwo (D := R.twoDiscCover))) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (fun i : Fin 4 ↦
      R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv S
        (integralSingularHomologyMap 2
          R.twoDiscCover.canonicalCuspFiberToEllipticInteriorMap
          (actualCuspFiberCoinvariantHomologyTwoBasis A i)) 0) = ![0, 12, 2, 0] := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  funext i
  rw [affineNormalizedEllipticInteriorHomologyTwo_canonicalCuspFiber_zero]
  change 12 * G.monodromyCoordinates.degreeTwo
      (G.monodromyCoordinates.degreeTwo.symm
        ![(Pi.single i 1 : Fin 4 → ℤ) 0, (Pi.single i 1 : Fin 4 → ℤ) 3,
          (Pi.single i 1 : Fin 4 → ℤ) 1, (Pi.single i 1 : Fin 4 → ℤ) 2, 0, 0]) 2 +
    2 * G.monodromyCoordinates.degreeTwo
      (G.monodromyCoordinates.degreeTwo.symm
        ![(Pi.single i 1 : Fin 4 → ℤ) 0, (Pi.single i 1 : Fin 4 → ℤ) 3,
          (Pi.single i 1 : Fin 4 → ℤ) 1, (Pi.single i 1 : Fin 4 → ℤ) 2, 0, 0]) 3 = _
  rw [G.monodromyCoordinates.degreeTwo.apply_symm_apply]
  fin_cases i <;> rfl

/-- Under the topological cusp--band square, the first two Wang fibre values are `[12, 0]`. -/
public theorem affineActualCuspDegreeOneFiberBasis_scalarValues
    (R : A.SectionSevenAffineRadialCompletionInput)
    (hTop : R.twoDiscCover.CanonicalCuspFiberBandTopologicalCompatibility) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (fun i : Fin 2 ↦
      R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyOneEquiv
        (integralSingularHomologyMap 1 R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single (Fin.castAdd 1 i) 1))) 0) = ![12, 0] := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  funext i
  rw [R.twoDiscCover.actualCuspDegreeOneFiberBasis_eq_canonicalBand hTop i]
  exact congrFun (affineCanonicalCuspFiberCoinvariantHomologyOneBasis_scalarValues R) i

/-- Under the same square, the first four Wang fibre values are `[0, 12, 2, 0]`. -/
public theorem affineActualCuspDegreeTwoFiberBasis_scalarValues
    (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting
      (presentationTwo (D := R.twoDiscCover)))
    (hTop : R.twoDiscCover.CanonicalCuspFiberBandTopologicalCompatibility) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (fun i : Fin 4 ↦
      R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv S
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap
          (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
            (Pi.single (Fin.castAdd 2 i) 1))) 0) = ![0, 12, 2, 0] := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  funext i
  rw [R.twoDiscCover.actualCuspDegreeTwoFiberBasis_eq_canonicalBand hTop i]
  exact congrFun (affineCanonicalCuspFiberCoinvariantHomologyTwoBasis_scalarValues R S) i

end SectionSevenEllipticTwoDiscCoverData

end Geometry.PaperAnalyticData

end SphereSixComplex

end
