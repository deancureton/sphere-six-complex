module

public import SphereSixComplex.Topology.CuspCorrectedBoundaryCoordinate
public import SphereSixComplex.Topology.CuspFourthSweepFiberParity

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SectionSevenEllipticTwoDiscCoverData SectionSevenEllipticTwoDiscHomologyCoordinates
open SectionSevenEllipticInteriorMarkedCycleData

public theorem cuspBoundaryCoordinate_rawFour {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    R.homologyAlignment.actualHomologyCoordinates.degreeTwoInvariantEquiv
      ((presentationTwo (D := R.twoDiscCover)).totalToInvariants
        (cuspToEllipticUnionHomology R.twoDiscCover 2 x)) =
      A.actualCuspRawHomologyTwoEquiv x 4 := by
  have h := DFunLike.congr_fun (cuspPulledBackBoundaryCoordinateHom_eq_rawFour R) x
  rw [R.twoDiscCover.cuspPulledBackBoundaryCoordinateHom_eq_cuspDegreeTwoBoundaryCoordinateHom]
    at h
  exact h

public theorem cuspRawFour_positiveBoundary {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    (presentationTwo (D := R.twoDiscCover)).totalToInvariants
      (cuspToEllipticUnionHomology R.twoDiscCover 2
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) =
      R.homologyAlignment.actualHomologyCoordinates.degreeTwoInvariantEquiv.symm 1 := by
  apply R.homologyAlignment.actualHomologyCoordinates.degreeTwoInvariantEquiv.injective
  rw [cuspBoundaryCoordinate_rawFour, LinearEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  simp

public def correctedCuspDegreeTwoSplitting {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover)) :=
  R.homologyAlignment.actualHomologyCoordinates.degreeTwoSplittingOfGenerator
    (cuspToEllipticUnionHomology R.twoDiscCover 2
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)))
    (cuspRawFour_positiveBoundary R)

public theorem correctedCuspDegreeTwoSplitting_rawFour {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.homologyAlignment.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
      (correctedCuspDegreeTwoSplitting R)
      (cuspToEllipticUnionHomology R.twoDiscCover 2
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = ![0, 1] := by
  let B := R.homologyAlignment.actualHomologyCoordinates
  let S := correctedCuspDegreeTwoSplitting R
  have h := B.normalizedUnionHomologyTwoEquiv_add S 0 (B.degreeTwoInvariantEquiv.symm 1)
  have hs : S.sweptSection (B.degreeTwoInvariantEquiv.symm 1) =
      cuspToEllipticUnionHomology R.twoDiscCover 2
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) := by
    change B.degreeTwoInvariantEquiv (B.degreeTwoInvariantEquiv.symm 1) •
      cuspToEllipticUnionHomology R.twoDiscCover 2
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) = _
    rw [LinearEquiv.apply_symm_apply, one_smul]
  rw [map_zero, zero_add, hs, LinearEquiv.apply_symm_apply] at h
  simpa only [map_zero] using h

public theorem correctedCuspDegreeTwoSplitting_boundary {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    R.homologyAlignment.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
      (correctedCuspDegreeTwoSplitting R)
      (cuspToEllipticUnionHomology R.twoDiscCover 2 x) 1 =
      A.actualCuspRawHomologyTwoEquiv x 4 :=
  cuspBoundaryCoordinate_rawFour R x

public theorem cuspEllipticFiberCoordinate_eq_union {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover)))
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    A.cuspEllipticFiberCoordinate R S x =
      R.homologyAlignment.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv S
        (cuspToEllipticUnionHomology R.twoDiscCover 2 x) 0 := by
  change R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv S
    (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom x) 0 = _
  rw [R.twoDiscCover.cuspToEllipticInteriorMap_homology]
  exact congrFun (congrArg
    (R.homologyAlignment.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv S)
    (AddEquiv.symm_apply_apply _ _)) 0

public theorem correctedCuspDegreeTwoSplitting_rawFour_fiber {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    A.cuspEllipticFiberCoordinate R (correctedCuspDegreeTwoSplitting R)
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) = 0 := by
  rw [cuspEllipticFiberCoordinate_eq_union, correctedCuspDegreeTwoSplitting_rawFour]
  rfl

public theorem correctedCuspFiberCoordinate_of_rawFive {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput)
    (hfive : A.cuspEllipticFiberCoordinate R (correctedCuspDegreeTwoSplitting R)
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) = 1) :
    A.cuspEllipticFiberCoordinate R (correctedCuspDegreeTwoSplitting R) =
      12 • coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 1 +
      2 • coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 2 +
      coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 5 := by
  apply SphereSixComplex.addMonoidHom_ext_of_equiv_pi_single_one A.actualCuspRawHomologyTwoEquiv
  intro i
  by_cases hi : i.val < 4
  · let j : Fin 4 := ⟨i.val, hi⟩
    have hij : Fin.castAdd 2 j = i := Fin.ext rfl
    rw [← hij, cuspEllipticFiberCoordinate_raw_fiber]
    have hk (k : Fin 4) : (![0, 12, 2, 0] : Fin 4 → ℤ) k =
        (12 • coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 1 +
          2 • coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 2 +
          coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 5)
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (Fin.castAdd 2 k) 1)) := by
      fin_cases k <;> simp [coordinateAfterAddEquiv_apply]
    exact hk j
  · have hi45 : i = 4 ∨ i = 5 := by omega
    rcases hi45 with rfl | rfl
    · rw [correctedCuspDegreeTwoSplitting_rawFour_fiber]
      simp [coordinateAfterAddEquiv_apply]
    · rw [hfive]
      simp [coordinateAfterAddEquiv_apply]

public theorem correctedCuspHomologyTwoCoordinates_of_rawFive {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput)
    (hfive : A.cuspEllipticFiberCoordinate R (correctedCuspDegreeTwoSplitting R)
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) = 1)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    R.homologyAlignment.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
      (correctedCuspDegreeTwoSplitting R)
      (cuspToEllipticUnionHomology R.twoDiscCover 2 x) =
        ![12 * A.actualCuspRawHomologyTwoEquiv x 1 +
          2 * A.actualCuspRawHomologyTwoEquiv x 2 + A.actualCuspRawHomologyTwoEquiv x 5,
          A.actualCuspRawHomologyTwoEquiv x 4] := by
  funext i
  fin_cases i
  · have h := DFunLike.congr_fun (correctedCuspFiberCoordinate_of_rawFive R hfive) x
    rw [cuspEllipticFiberCoordinate_eq_union] at h
    simpa [coordinateAfterAddEquiv_apply] using h
  · exact correctedCuspDegreeTwoSplitting_boundary R x

end SphereSixComplex.Geometry.PaperAnalyticData
