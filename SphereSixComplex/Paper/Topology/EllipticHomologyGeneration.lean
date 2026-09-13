module

public import SphereSixComplex.Paper.Topology.EllipticHomologyOne
public import SphereSixComplex.Paper.Topology.CuspNormalizedBandMarking
public import SphereSixComplex.Paper.Topology.StarFirstHomology
public import SphereSixComplex.Prerequisites.Topology.ExactGeneration

@[expose] public section
noncomputable section
open AlgebraicTopology

namespace SphereSixComplex.Geometry.AnalyticData
open EllipticTwoDiscCoverData EllipticTwoDiscHomologyCoordinates

public def ellipticUnionInclusion {A : AnalyticData} (D : A.EllipticTwoDiscCoverData) :
    C((D.orderThreeSide ∪ D.orderFourSide : Set A.ellipticInterior), A.VanKampenSpace) :=
  ⟨fun x ↦ x.val.val, by fun_prop⟩

public theorem cuspRawFour_ellipticUnionInclusion {A : AnalyticData}
    (D : A.EllipticTwoDiscCoverData) :
    integralSingularHomologyMap 2 (ellipticUnionInclusion D)
      (cuspToEllipticUnionHomology D 2
        (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 0 := by
  let x := A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)
  let U := A.openEmbeddingStarData.sectionSevenMayerVietorisCover.stage 2
  let V := A.openEmbeddingStarData.sectionSevenMayerVietorisCover.piece 3
  let eS := integralSingularHomologyEquiv 2 A.cuspCollarToSectionSevenFinalOverlapHomeomorph
  let eT := integralSingularHomologyEquiv 2
    (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)
  have hFilling : integralSingularHomologyMap 2
      (A.openEmbeddingStarData.toFilling 0).hom x = 0 := by
    apply A.actualCuspFillingHomologyTwoEquiv.injective
    rw [map_zero]
    have h := CuspSpecialization.degreeTwo A x
    change A.actualCuspFillingHomologyTwoEquiv
      (integralSingularHomologyMap 2 (A.openEmbeddingStarData.toFilling 0).hom x) =
        fun i ↦ A.cuspRawHomologyTwoEquiv x (Fin.castAdd 2 i) at h
    rw [h]
    ext i
    change A.cuspRawHomologyTwoEquiv (A.cuspRawHomologyTwoEquiv.symm _) _ = 0
    rw [AddEquiv.apply_symm_apply]
    have hi : Fin.castAdd 2 i ≠ (4 : Fin 6) := by fin_cases i <;> decide
    simp [Ne.symm hi]
  have hRight : integralSingularHomologyMap 2
      (IntegralMayerVietoris.interToRight U V) (eS x) = 0 := by
    apply eT.symm.injective
    calc
      _ = integralSingularHomologyMap 2 (A.openEmbeddingStarData.toFilling 0).hom x := by
        simpa only [eS, AddEquiv.symm_apply_apply] using
          A.cuspFinalRightHomologyMap_conjugacy 2 (eS x)
      _ = 0 := hFilling
      _ = eT.symm 0 := (map_zero eT.symm).symm
  change integralSingularHomologyMap 2 (ellipticUnionInclusion D)
    ((integralSingularHomologyEquiv 2
      (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.ellipticInterior)
        (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)).symm
      (integralSingularHomologyMap 2 (IntegralMayerVietoris.interToLeft U V) (eS x))) = 0
  change integralSingularHomologyMap 2 (ellipticUnionInclusion D)
    (integralSingularHomologyMap 2 _
      (integralSingularHomologyMap 2 (IntegralMayerVietoris.interToLeft U V) (eS x))) = 0
  rw [integralSingularHomologyMap_comp_wang]
  change integralSingularHomologyMap 2 A.ellipticInteriorInclusion
    (integralSingularHomologyMap 2 (IntegralMayerVietoris.interToLeft U V) (eS x)) = 0
  rw [integralSingularHomologyMap_comp_wang]
  change integralSingularHomologyMap 2
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(V, A.VanKampenSpace)).comp
      (IntegralMayerVietoris.interToRight U V)) (eS x) = 0
  rw [← integralSingularHomologyMap_comp_wang, hRight, map_zero]

public theorem ellipticHomologyTwo_hom_eq_zero_of_sides
    {A : AnalyticData} (R : A.AffineRadialCompletionInput)
    {G : Type*} [AddCommGroup G]
    (f : IntegralSingularHomology 2
      (R.twoDiscCover.orderThreeSide ∪ R.twoDiscCover.orderFourSide :
        Set A.ellipticInterior) →+ G)
    (hSides : ∀ x, f ((presentationTwo (D := R.twoDiscCover)).inclusion x) = 0)
    (hCusp : f (cuspToEllipticUnionHomology R.twoDiscCover 2
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 0) :
    f = 0 := by
  let P := presentationTwo (D := R.twoDiscCover)
  let z := cuspToEllipticUnionHomology R.twoDiscCover 2
    (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))
  have hz : EllipticHomologyOne.bandOne (D := R.twoDiscCover) (P.boundary z) =
      alphaOneKernelGenerator := by
    change EllipticBandHomologyAlignment.bandOne (D := R.twoDiscCover)
      (canonicalBoundary R.twoDiscCover 1 z) = _
    rw [R.twoDiscCover.canonicalBoundary_cuspToEllipticUnionHomology]
    exact cuspRawFour_pulled_back_primitive R
  apply AddMonoidHom.eq_zero_of_exact_of_boundary_generator
    P.inclusion P.boundary P.lowDifference f P.exact_inclusion_boundary
    P.exact_boundary_lowDifference hSides z hCusp
  intro c hc
  obtain ⟨n, hn⟩ :=
    (EllipticHomologyOne.kernel_iff R.homologyAlignment.degreeOne c).mp hc
  refine ⟨n, (EllipticHomologyOne.bandOne (D := R.twoDiscCover)).injective ?_⟩
  rw [map_zsmul, hz]
  exact hn

public theorem ellipticInterior_homologyTwo_eq_zero_of_sides
    {A : AnalyticData} (R : A.AffineRadialCompletionInput)
    (hSides : ∀ x, integralSingularHomologyMap 2 (ellipticUnionInclusion R.twoDiscCover)
      ((presentationTwo (D := R.twoDiscCover)).inclusion x) = 0) :
    integralSingularHomologyMap 2 A.ellipticInteriorInclusion = 0 := by
  have h := ellipticHomologyTwo_hom_eq_zero_of_sides R
    (integralSingularHomologyMap 2 (ellipticUnionInclusion R.twoDiscCover))
    hSides (cuspRawFour_ellipticUnionInclusion R.twoDiscCover)
  let e := integralSingularHomologyEquiv 2
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.ellipticInterior)
      (R.twoDiscCover.orderThreeSide ∪ R.twoDiscCover.orderFourSide) R.twoDiscCover.sides_cover)
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  change integralSingularHomologyMap 2 A.ellipticInteriorInclusion
    (integralSingularHomologyMap 2 _ y) = 0
  rw [integralSingularHomologyMap_comp_wang]
  exact DFunLike.congr_fun h y

end SphereSixComplex.Geometry.AnalyticData
