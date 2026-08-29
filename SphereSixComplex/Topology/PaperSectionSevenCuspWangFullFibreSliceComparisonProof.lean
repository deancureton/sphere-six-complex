module

public import SphereSixComplex.Topology.PaperSectionSevenCuspWangFullFibreSlice
public import SphereSixComplex.Topology.PaperCuspGeometricSpecializationProof

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeWangAlgebra
open SphereSixComplex.CircleMappingTorusHomologyBases

namespace SectionSevenEllipticTwoDiscCoverData

private theorem circleMappingTorusBoundary_coordinates
    {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}
    (B : CuspMonodromyCoordinates phi) (S : CuspGeometricWangSections B)
    (y : IntegralSingularHomology 2 (CircleMappingTorus phi)) :
    B.degreeOne ((circleMappingTorusHTwoPresentation phi).boundary y) =
      ![0, 0, S.circleMappingTorusHTwoAddEquiv y 4,
        S.circleMappingTorusHTwoAddEquiv y 5] := by
  funext i
  fin_cases i
  · simp
    have hb : (circleMonodromyDifference phi 1).toIntLinearMap
        ((circleMappingTorusHTwoPresentation phi).boundary y) = 0 :=
      (circleMappingTorusHTwoPresentation phi).lowDifference_boundary y
    have h := DFunLike.congr_fun B.degreeOneDifference_conjugacy
      ((circleMappingTorusHTwoPresentation phi).boundary y)
    simp only [LinearMap.comp_apply, hb, map_zero] at h
    have hz := (mem_ker_mZeroDifference_iff _).mp (LinearMap.mem_ker.mpr h.symm)
    exact hz.1
  · simp
    have hb : (circleMonodromyDifference phi 1).toIntLinearMap
        ((circleMappingTorusHTwoPresentation phi).boundary y) = 0 :=
      (circleMappingTorusHTwoPresentation phi).lowDifference_boundary y
    have h := DFunLike.congr_fun B.degreeOneDifference_conjugacy
      ((circleMappingTorusHTwoPresentation phi).boundary y)
    simp only [LinearMap.comp_apply, hb, map_zero] at h
    have hz := (mem_ker_mZeroDifference_iff _).mp (LinearMap.mem_ker.mpr h.symm)
    exact hz.2
  · simp
    rw [circleMappingTorusHTwoAddEquiv_apply]
    rfl
  · simp
    rw [circleMappingTorusHTwoAddEquiv_apply]
    rfl

public theorem actualCuspWangBoundaryHom_rawCoordinates
    (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.monodromyCoordinates.degreeOne (actualCuspWangBoundaryHom A x) =
      ![0, 0, (A.actualCuspRawHomologyTwoEquiv x) 4,
        (A.actualCuspRawHomologyTwoEquiv x) 5] := by
  dsimp
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  exact circleMappingTorusBoundary_coordinates
    A.actualCuspRadialClutchingData.monodromyCoordinates
    A.actualCuspRadialClutchingData.geometricWangSections
    (integralSingularHomologyMap 2
      A.actualCuspRadialClutchingData.totalHomotopyEquiv.toFun x)

/-- The marked first-homology coordinates of the Wang boundary on a raw degree-two basis
vector. -/
public def actualCuspWangBoundaryRawBasisCoordinates (i : Fin 6) : Fin 4 → ℤ :=
  ![0, 0, (Pi.single i 1 : Fin 6 → ℤ) 4, (Pi.single i 1 : Fin 6 → ℤ) 5]

/-- The actual Wang boundary on each raw basis vector, expressed as an explicit element of the
marked first homology of the fibre. -/
public theorem actualCuspWangBoundaryHom_rawBasis (A : PaperAnalyticData) (i : Fin 6) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspWangBoundaryHom A
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)) =
      G.monodromyCoordinates.degreeOne.symm
        (actualCuspWangBoundaryRawBasisCoordinates i) := by
  dsimp
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  apply A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne.injective
  rw [actualCuspWangBoundaryHom_rawCoordinates]
  simp [actualCuspWangBoundaryRawBasisCoordinates]

@[simp]
public theorem actualCuspWangBoundaryRawBasisCoordinates_castAdd (i : Fin 4) :
    actualCuspWangBoundaryRawBasisCoordinates (Fin.castAdd 2 i) = 0 := by
  fin_cases i <;> simp [actualCuspWangBoundaryRawBasisCoordinates]

@[simp]
public theorem actualCuspWangBoundaryRawBasisCoordinates_four :
    actualCuspWangBoundaryRawBasisCoordinates (4 : Fin 6) = ![0, 0, 1, 0] := by
  rfl

@[simp]
public theorem actualCuspWangBoundaryRawBasisCoordinates_five :
    actualCuspWangBoundaryRawBasisCoordinates (5 : Fin 6) = ![0, 0, 0, 1] := by
  rfl

/-- The explicit value occurring for the first four raw basis vectors maps to zero in the
cover intersection. -/
public theorem actualCuspWangFibreToCuspCoverIntersectionHomologyOne_rawZero
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
        (G.monodromyCoordinates.degreeOne.symm 0) = 0 := by
  dsimp
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  simp only [map_zero]

/-- The remaining comparison after evaluating the Wang boundary on all six raw basis vectors.
It involves only the explicit full-fibre images of two invariant generators and four zeros. -/
public def ActualCuspWangFullFibreSliceExplicitFiniteResidual
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  (∀ i : Fin 4,
    R.twoDiscCover.cuspOpenCoverConnectingHom
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (Fin.castAdd 2 i) 1)) = 0) ∧
    actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
        (G.monodromyCoordinates.degreeOne.symm
          ![0, 0, 1, 0]) =
      R.twoDiscCover.cuspOpenCoverConnectingHom
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) ∧
    actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R
        (G.monodromyCoordinates.degreeOne.symm
          ![0, 0, 0, 1]) =
      R.twoDiscCover.cuspOpenCoverConnectingHom
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))

/-- The original six basis comparisons are equivalent to the finite residual in which the Wang
boundary has been completely evaluated. -/
public theorem wangBoundaryBasisComparison_iff_explicitFiniteResidual
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) :
    (let G := A.actualCuspRadialClutchingData
     let _ := G.fiberTopology
     ∀ i : Fin 6,
       ((actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R).comp
           (actualCuspWangBoundaryHom A))
             (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)) =
         R.twoDiscCover.cuspOpenCoverConnectingHom
           (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) ↔
      ActualCuspWangFullFibreSliceExplicitFiniteResidual R := by
  dsimp [ActualCuspWangFullFibreSliceExplicitFiniteResidual]
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  simp only [actualCuspWangBoundaryHom_rawBasis]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hi := (h (Fin.castAdd 2 i)).symm
      rw [actualCuspWangBoundaryRawBasisCoordinates_castAdd] at hi
      exact hi.trans
        (actualCuspWangFibreToCuspCoverIntersectionHomologyOne_rawZero R)
    · simpa only [actualCuspWangBoundaryRawBasisCoordinates_four] using h 4
    · simpa only [actualCuspWangBoundaryRawBasisCoordinates_five] using h 5
  · rintro ⟨hzero, hfour, hfive⟩ i
    by_cases hi : i.val < 4
    · let j : Fin 4 := ⟨i.val, hi⟩
      have hij : Fin.castAdd 2 j = i := Fin.ext rfl
      rw [← hij, actualCuspWangBoundaryRawBasisCoordinates_castAdd,
        actualCuspWangFibreToCuspCoverIntersectionHomologyOne_rawZero, hzero j]
    · have hi45 : i = 4 ∨ i = 5 := by omega
      rcases hi45 with rfl | rfl
      · exact hfour
      · exact hfive

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
