module

public import SphereSixComplex.Paper.Topology.CuspFundamentalGroup
public import SphereSixComplex.Prerequisites.Topology.SixSphereHomology
public import SphereSixComplex.Paper.Topology.EstablishedPaperSectionSevenAffineCompletion
public import SphereSixComplex.Paper.Topology.CuspAttachmentHomology
public import SphereSixComplex.Paper.Topology.StarFirstHomology
public import SphereSixComplex.Paper.Geometry.StarHomology
public import SphereSixComplex.Prerequisites.Topology.MayerVietorisFiniteRank
public import Mathlib.LinearAlgebra.Pi

/-!
# Topology of the glued analytic threefold

The fundamental group and homology computations concern the same geometric glued carrier.
-/

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.AnalyticData

variable (P : AnalyticData)

/-- The degree-two difference map is onto, and the preceding map is between rank-three groups. -/
public theorem star_homologyTwo_subsingleton :
    Subsingleton (IntegralSingularHomology 2 P.VanKampenSpace) := by
  let R := P.affineRadialCompletionInput
  let U := P.openEmbeddingStarData.sectionSevenMayerVietorisCover.stage 2
  let V := P.openEmbeddingStarData.sectionSevenMayerVietorisCover.piece 3
  let eS := (integralSingularHomologyEquiv 1
    P.cuspCollarToSectionSevenFinalOverlapHomeomorph).symm.trans P.cuspRawHomologyOneEquiv
  let eT :=
    (R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyOneEquiv
      |>.prodCongr
      ((integralSingularHomologyEquiv 1
        (P.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)).symm.trans
        P.cuspFillingHomologyOneEquiv)).trans
      ((LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin 2) ℤ ℤ).symm.trans
        (LinearEquiv.piCongrLeft ℤ (fun _ : Fin 3 ↦ ℤ) finSumFinEquiv)).toAddEquiv
  let eOne := integralSingularHomologyEquiv 1
    (OpenEmbeddingStarData.cuspAttachmentUnionHomeomorph
      (A := P.openEmbeddingStarData))
  have hUnion : Subsingleton (IntegralSingularHomology 1 (U ∪ V : Set P.VanKampenSpace)) :=
    ⟨fun x y ↦ eOne.injective (P.star_homologyOne_subsingleton.elim _ _)⟩
  have h := IntegralMayerVietoris.subsingleton_homology_succ U V
    (FourPieceOpenCover.mayerVietoris_exact
      P.openEmbeddingStarData.sectionSevenMayerVietorisCover 2)
    1 3 eS eT hUnion (cuspAttachment_differenceMap_two_surjective R)
  let e := integralSingularHomologyEquiv 2
    (OpenEmbeddingStarData.cuspAttachmentUnionHomeomorph
      (A := P.openEmbeddingStarData))
  exact ⟨fun x y ↦ e.symm.injective (h.elim _ _)⟩

/-- Low-degree vanishing and the Euler calculation give the integral homology of the six-sphere. -/
public theorem star_nonempty_homologyEquiv_sixSphere :
    ∀ k, Nonempty
      (IntegralSingularHomology k
        (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) ≃+
      IntegralSingularHomology k SixSphere) :=
  P.star_nonempty_homologyEquiv_sixSphere_of_lowDegrees
    P.star_homologyOne_subsingleton P.star_homologyTwo_subsingleton

/-- The cusp relations make the fundamental group abelian, and vanishing first homology kills it. -/
public theorem star_simplyConnectedSpace :
    SimplyConnectedSpace
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) := by
  let _ := P.star_homologyOne_subsingleton
  exact P.star_simplyConnectedSpace_of_homologyOne_subsingleton P.cuspCentralNaturality

end SphereSixComplex.Geometry.AnalyticData
