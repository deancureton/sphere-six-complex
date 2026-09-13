module

public import SphereSixComplex.Paper.Topology.EllipticHomologyOne
public import SphereSixComplex.Paper.Topology.StarFirstHomology
public import SphereSixComplex.Paper.Topology.CuspAttachmentHomology
public import SphereSixComplex.Paper.Topology.PaperCuspFinalInclusionAdapter
public import SphereSixComplex.Prerequisites.Topology.MayerVietorisFiniteRank
public import Mathlib.LinearAlgebra.Pi

@[expose] public section
noncomputable section
open AlgebraicTopology

namespace SphereSixComplex.Geometry.AnalyticData

public theorem star_homologyTwo_subsingleton_of_interior
    {A : AnalyticData} (R : A.AffineRadialCompletionInput)
    (hInterior : integralSingularHomologyMap 2 A.ellipticInteriorInclusion = 0) :
    Subsingleton (IntegralSingularHomology 2 A.VanKampenSpace) := by
  let U := A.openEmbeddingStarData.sectionSevenMayerVietorisCover.stage 2
  let V := A.openEmbeddingStarData.sectionSevenMayerVietorisCover.piece 3
  let e := integralSingularHomologyEquiv 2
    (OpenEmbeddingStarData.cuspAttachmentUnionHomeomorph
      (A := A.openEmbeddingStarData))
  have hLeft (x : IntegralSingularHomology 2 U) :
      integralSingularHomologyMap 2 (IntegralMayerVietoris.leftToUnion U V) x = 0 := by
    apply e.injective
    rw [map_zero]
    change integralSingularHomologyMap 2 _
      (integralSingularHomologyMap 2 _ x) = 0
    rw [integralSingularHomologyMap_comp_wang]
    exact DFunLike.congr_fun hInterior x
  have hRightSurj : Function.Surjective
      (integralSingularHomologyMap 2 (IntegralMayerVietoris.interToRight U V)) := by
    let eS := integralSingularHomologyEquiv 2
      A.cuspCollarToSectionSevenFinalOverlapHomeomorph
    let eT := integralSingularHomologyEquiv 2
      (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)
    intro y
    obtain ⟨x, hx⟩ := A.cuspToFilling_homologyTwo_surjective (eT.symm y)
    refine ⟨eS x, eT.symm.injective ?_⟩
    rw [A.cuspFinalRightHomologyMap_conjugacy]
    simpa only [eS, AddEquiv.symm_apply_apply] using hx
  have hRight (x : IntegralSingularHomology 2 V) :
      integralSingularHomologyMap 2 (IntegralMayerVietoris.rightToUnion U V) x = 0 := by
    obtain ⟨y, rfl⟩ := hRightSurj x
    rw [integralSingularHomologyMap_comp_wang]
    change integralSingularHomologyMap 2
      ((IntegralMayerVietoris.leftToUnion U V).comp
        (IntegralMayerVietoris.interToLeft U V)) y = 0
    rw [← integralSingularHomologyMap_comp_wang]
    exact hLeft _
  have hSum (x) : IntegralMayerVietoris.sumMap U V 2 x = 0 := by
    change integralSingularHomologyMap 2 (IntegralMayerVietoris.leftToUnion U V) x.1 +
      integralSingularHomologyMap 2 (IntegralMayerVietoris.rightToUnion U V) x.2 = 0
    rw [hLeft, hRight, add_zero]
  have hExact := FourPieceOpenCover.mayerVietoris_exact
    A.openEmbeddingStarData.sectionSevenMayerVietorisCover 2
  have hTwo : Function.Surjective (IntegralMayerVietoris.differenceMap U V 2) := by
    obtain ⟨boundary, h⟩ := hExact
    intro x
    exact ((h 2).2.2 x).mp (hSum x)
  let eS := (integralSingularHomologyEquiv 1
    A.cuspCollarToSectionSevenFinalOverlapHomeomorph).symm.trans A.cuspRawHomologyOneEquiv
  let eT :=
    ((EllipticHomologyOne.normalizedEllipticInteriorHomologyOneEquiv
      R.homologyAlignment.degreeOne).prodCongr
      ((integralSingularHomologyEquiv 1
        (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)).symm.trans
        A.cuspFillingHomologyOneEquiv)).trans
      ((LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin 2) ℤ ℤ).symm.trans
        (LinearEquiv.piCongrLeft ℤ (fun _ : Fin 3 ↦ ℤ) finSumFinEquiv)).toAddEquiv
  let eOne := integralSingularHomologyEquiv 1
    (OpenEmbeddingStarData.cuspAttachmentUnionHomeomorph
      (A := A.openEmbeddingStarData))
  have hUnion : Subsingleton (IntegralSingularHomology 1 (U ∪ V : Set A.VanKampenSpace)) :=
    ⟨fun x y ↦ eOne.injective (A.star_homologyOne_subsingleton.elim _ _)⟩
  have h := IntegralMayerVietoris.subsingleton_homology_succ U V hExact 1 3 eS eT hUnion hTwo
  exact ⟨fun x y ↦ e.symm.injective (h.elim _ _)⟩

end SphereSixComplex.Geometry.AnalyticData
