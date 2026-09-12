module

public import SphereSixComplex.Prerequisites.Topology.AddMonoidHomSurjectivity
public import SphereSixComplex.Paper.Topology.CuspFourthFiberUnit

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.AnalyticData
open CuspCollar EllipticTwoDiscCoverData EllipticTwoDiscHomologyCoordinates
open EllipticInteriorMarkedCycleData

public theorem cuspAttachment_differenceMap_two_surjective {A : AnalyticData}
    (R : A.AffineRadialCompletionInput) :
    Function.Surjective (IntegralMayerVietoris.differenceMap
      (A.openEmbeddingStarData.sectionSevenMayerVietorisCover.stage (2 : Fin 4))
      (A.openEmbeddingStarData.sectionSevenMayerVietorisCover.piece 3) 2) := by
  let p :
      IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+ (Fin 4 → ℤ) :=
    (A.actualCuspFillingHomologyTwoEquiv.toAddMonoidHom).comp
      (integralSingularHomologyMap 2
        ⟨puncturedLocalCuspToFilling A.starCuspWitness,
          puncturedLocalCuspToFilling_continuous A.starCuspWitness⟩)

  let q :
      IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+ (Fin 2 → ℤ) := {
    toFun x := R.homologyAlignment.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
      (correctedCuspDegreeTwoSplitting R) (cuspToEllipticUnionHomology R.twoDiscCover 2 x)
    map_zero' := by simp [cuspToEllipticUnionHomology]
    map_add' x y := by simp [cuspToEllipticUnionHomology] }

  have hp (x) :
      p x = fun i ↦ A.cuspRawHomologyTwoEquiv x (Fin.castAdd 2 i) :=
    CuspSpecialization.degreeTwo A x

  have hpSurj :
      Function.Surjective p := by
    intro y
    refine ⟨A.cuspRawHomologyTwoEquiv.symm (Fin.append y (0 : Fin 2 → ℤ)), ?_⟩
    rw [hp, AddEquiv.apply_symm_apply]
    ext i
    simp

  have hqFive :
      q
        (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) = ![1, 0] := by
    ext i
    fin_cases i
    · exact (A.cuspEllipticFiberCoordinate_eq_union
        R (correctedCuspDegreeTwoSplitting R) _).symm.trans
        (A.cuspEllipticFiberCoordinate_rawFive R (correctedCuspDegreeTwoSplitting R))
    · change R.homologyAlignment.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
        (correctedCuspDegreeTwoSplitting R) _ 1 = 0
      have h := DFunLike.congr_fun
        (R.twoDiscCover.cuspPulledBackBoundaryCoordinateHom_eq_cuspDegreeTwoBoundaryCoordinateHom
          R.homologyAlignment)
        (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))
      apply h.symm.trans
      rw [R.twoDiscCover.cuspPulledBackBoundaryCoordinateHom_apply_eq_bandCoordinate]
      change R.homologyAlignment.actualHomologyCoordinates.bandOne
        (R.twoDiscCover.cuspPulledBackBoundaryHom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))) 3 = 0
      rw [cuspRawFive_pulled_back_boundary_zero, map_zero]
      rfl

  have hker (y : Fin 2 → ℤ) :
      ∃ x, p x = 0 ∧ q x = y := by
    let x4 := A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)
    let x5 := A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)
    have hp4 : p x4 = 0 := by
      rw [hp]
      simp only [x4, AddEquiv.apply_symm_apply]
      ext i
      have hi : Fin.castAdd 2 i ≠ (4 : Fin 6) := by fin_cases i <;> decide
      simp [Ne.symm hi]
    have hp5 : p x5 = 0 := by
      rw [hp]
      simp only [x5, AddEquiv.apply_symm_apply]
      ext i
      have hi : Fin.castAdd 2 i ≠ (5 : Fin 6) := by fin_cases i <;> decide
      simp [Ne.symm hi]
    have hq4 : q x4 = ![0, 1] :=
      correctedCuspDegreeTwoSplitting_rawFour R
    have hq5 : q x5 = ![1, 0] :=
      hqFive
    refine ⟨y 0 • x5 + y 1 • x4, ?_, ?_⟩
    · simp [hp4, hp5]
    · simp only [map_add, map_zsmul, hq4, hq5]
      ext i
      fin_cases i <;> simp

  have hsurj :
      Function.Surjective (fun x ↦
        (q x, p x)) :=
    AddMonoidHom.prod_surjective_of_surjective_of_ker _ _
      hpSurj hker
  let e := integralSingularHomologyEquiv 2 A.cuspCollarToSectionSevenFinalOverlapHomeomorph
  let f := integralSingularHomologyEquiv 2
    (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)
  let eLeft :=
    R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
      (correctedCuspDegreeTwoSplitting R)
  rintro ⟨a, b⟩
  obtain ⟨x, hx⟩ := hsurj
    (eLeft a, A.actualCuspFillingHomologyTwoEquiv (f.symm (-b)))
  refine ⟨e x, Prod.ext ?_ ?_⟩
  · apply eLeft.injective
    have h := congrArg Prod.fst hx
    exact h
  · change -(integralSingularHomologyMap 2 _ (e x)) = b
    have h := congrArg Prod.snd hx
    have hc := A.cuspFinalRightHomologyMap_conjugacy 2 (e x)
    change f.symm (integralSingularHomologyMap 2 _ (e x)) = _ at hc
    rw [AddEquiv.symm_apply_apply] at hc
    have ht : integralSingularHomologyMap 2
        (A.openEmbeddingStarData.toFilling 0).hom x = f.symm (-b) :=
      A.actualCuspFillingHomologyTwoEquiv.injective h
    rw [ht] at hc
    have hh := f.symm.injective hc
    exact (congrArg Neg.neg hh).trans (neg_neg b)


end SphereSixComplex.Geometry.AnalyticData
