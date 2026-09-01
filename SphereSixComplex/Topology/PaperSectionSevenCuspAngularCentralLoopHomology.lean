module

public import SphereSixComplex.Topology.PaperSectionSevenCuspWangFullFibreSlice
public import SphereSixComplex.Topology.PaperActualCuspCentralLoopRelation
public import SphereSixComplex.Topology.StandardCircleHomologyLiftDegree

/-!
# The actual angular cusp loop inside the elliptic central image

The literal angular path in the additive cusp cover projects to a loop in the actual cusp
collar.  Its image in the cusp-free elliptic interior stays in the central piece, where the
central-image homeomorphism identifies it pointwise with the previously constructed actual cusp
central loop.  The final two statements record this identification directly in first integral
homology.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open SphereSixComplex.StandardCircleHomologyLiftDegree

variable {A : PaperAnalyticData}

/-- The literal angular path, projected from the additive cusp cover to the actual collar. -/
public noncomputable def actualCuspAngularCollarLoop :
    let x := A.actualCuspAngularCollarPoint 0
    Path x x := by
  let x := A.actualCuspAngularCollarPoint 0
  refine
    { toFun := A.actualCuspAngularCollarPoint
      continuous_toFun := ?_
      source' := rfl
      target' := ?_ }
  · unfold actualCuspAngularCollarPoint
    exact (additiveCuspBoundaryProjection A.starCuspWitness).continuous.comp
      A.actualCuspAngularLiftPath.continuous
  · apply A.cuspCollarToStarOverlapHomeomorph.injective
    change A.actualCuspBoundaryProjection (A.actualCuspAngularLiftPoint 1) =
      A.actualCuspBoundaryProjection (A.actualCuspAngularLiftPoint 0)
    exact A.actualCuspAngularProjectedLoop.target.trans
      A.actualCuspAngularProjectedLoop.source.symm

namespace SectionSevenEllipticTwoDiscCoverData

variable (D : A.SectionSevenEllipticTwoDiscCoverData)

/-- On every additive cusp-cover point, the full central-family point underlying the elliptic
inclusion is the literal cusp-overlap chart point. -/
public theorem
    sectionSevenEllipticCentralPoint_cuspToEllipticInteriorMap_additivePoint
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.sectionSevenEllipticCentralImageHomeomorph
      ⟨D.cuspToEllipticInteriorMap
          (additiveCuspBoundaryProjection A.starCuspWitness p),
        D.cuspToEllipticInteriorMap_mem_centralImage
          (additiveCuspBoundaryProjection A.starCuspWitness p)⟩ =
      A.actualCuspOverlapToCentral (A.actualCuspBoundaryProjection p) := by
  apply A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.injective
  apply Subtype.ext
  rw [A.centralToSectionSevenEulerPiece_centralImage,
    A.actualCuspOverlapToCentral_boundaryProjection]
  have hglobal :
      additiveCuspCoverToGlobal A.starCuspWitness p =
        A.starToCentral 0 (additiveCuspBoundaryProjection A.starCuspWitness p) := by
    change additiveCuspCoverToGlobal A.starCuspWitness p =
      puncturedLocalCuspQuotientMap A.starCuspWitness
        (additiveCuspBoundaryProjection A.starCuspWitness p)
    exact (puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection
      A.starCuspWitness p).symm
  calc
    ↑↑(⟨D.cuspToEllipticInteriorMap
        (additiveCuspBoundaryProjection A.starCuspWitness p),
      D.cuspToEllipticInteriorMap_mem_centralImage
        (additiveCuspBoundaryProjection A.starCuspWitness p)⟩ :
          A.sectionSevenEllipticCentralImage) =
        A.openEmbeddingStarData.collarSourceToGlued 0
          (additiveCuspBoundaryProjection A.starCuspWitness p) := rfl
    _ = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.starToCentral 0
          (additiveCuspBoundaryProjection A.starCuspWitness p))).1 :=
      (A.centralToSectionSevenEulerPiece_starToCentral 0 _).symm
    _ = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (additiveCuspCoverToGlobal A.starCuspWitness p)).1 := by rw [hglobal]

/-- Along the angular path, the full central-family point is the actual cusp central loop. -/
public theorem
    sectionSevenEllipticCentralPoint_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint
    (t : unitInterval) :
    A.sectionSevenEllipticCentralImageHomeomorph
      ⟨D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t),
        D.cuspToEllipticInteriorMap_mem_centralImage
          (A.actualCuspAngularCollarPoint t)⟩ =
      A.actualCuspAngularCentralLoop t := by
  rw [actualCuspAngularCollarPoint,
    D.sectionSevenEllipticCentralPoint_cuspToEllipticInteriorMap_additivePoint]
  rfl

/-- The image of the actual angular collar loop, retained as a loop in the elliptic central
image rather than merely in the whole elliptic interior. -/
public noncomputable def actualCuspAngularEllipticCentralImageLoop :
    let x : A.sectionSevenEllipticCentralImage :=
      ⟨D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint 0),
        D.cuspToEllipticInteriorMap_mem_centralImage
          (A.actualCuspAngularCollarPoint 0)⟩
    Path x x := by
  let x : A.sectionSevenEllipticCentralImage :=
    ⟨D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint 0),
      D.cuspToEllipticInteriorMap_mem_centralImage
        (A.actualCuspAngularCollarPoint 0)⟩
  let f : unitInterval → A.sectionSevenEllipticCentralImage := fun t ↦
    ⟨D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t),
      D.cuspToEllipticInteriorMap_mem_centralImage
        (A.actualCuspAngularCollarPoint t)⟩
  refine
    { toFun := f
      continuous_toFun := ?_
      source' := rfl
      target' := ?_ }
  · unfold f actualCuspAngularCollarPoint
    apply Continuous.subtype_mk
    exact D.cuspToEllipticInteriorMap.hom.continuous.comp
      ((additiveCuspBoundaryProjection A.starCuspWitness).continuous.comp
        A.actualCuspAngularLiftPath.continuous)
  · apply Subtype.ext
    change D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint 1) =
      D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint 0)
    exact congrArg D.cuspToEllipticInteriorMap A.actualCuspAngularCollarLoop.target

/-- Forgetting the central-image membership recovers the direct image of the angular collar
loop in the elliptic interior. -/
public theorem actualCuspAngularEllipticCentralImageLoop_inclusion :
    D.actualCuspAngularEllipticCentralImageLoop.map continuous_subtype_val =
      A.actualCuspAngularCollarLoop.map D.cuspToEllipticInteriorMap.hom.continuous := by
  apply Path.ext
  funext t
  rfl

/-- The central-image homeomorphism sends the elliptic image loop to the actual cusp central
loop, including its based-loop endpoint normalization. -/
public theorem actualCuspAngularEllipticCentralImageLoop_map :
    ((D.actualCuspAngularEllipticCentralImageLoop.map
      A.sectionSevenEllipticCentralImageHomeomorph.continuous).cast
        ((D.sectionSevenEllipticCentralPoint_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint
          0).trans A.actualCuspAngularCentralLoop.source).symm
        ((D.sectionSevenEllipticCentralPoint_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint
          0).trans A.actualCuspAngularCentralLoop.source).symm) =
      A.actualCuspAngularCentralLoop := by
  apply Path.ext
  funext t
  exact
    D.sectionSevenEllipticCentralPoint_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint t

/-- First Hurewicz carries the central-image loop to the homology class of the actual cusp
central loop. -/
public theorem actualCuspAngularEllipticCentralImageLoop_homology :
    integralSingularHomologyMap 1
      (⟨A.sectionSevenEllipticCentralImageHomeomorph,
        A.sectionSevenEllipticCentralImageHomeomorph.continuous⟩ :
          C(A.sectionSevenEllipticCentralImage, A.CentralFamily))
      (loopHomologyClass D.actualCuspAngularEllipticCentralImageLoop) =
        loopHomologyClass A.actualCuspAngularCentralLoop := by
  rw [integralSingularHomologyMap_loopHomologyClass]
  rw [← loopHomologyClass_cast
    (D.actualCuspAngularEllipticCentralImageLoop.map
      A.sectionSevenEllipticCentralImageHomeomorph.continuous)
    ((D.sectionSevenEllipticCentralPoint_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint
      0).trans A.actualCuspAngularCentralLoop.source).symm]
  rw [D.actualCuspAngularEllipticCentralImageLoop_map]

/-- The target homology class of the explicit angular collar loop is the inclusion of its
central-image loop class. -/
public theorem actualCuspAngularCollarLoop_homology_image :
    integralSingularHomologyMap 1 D.cuspToEllipticInteriorMap.hom
        (loopHomologyClass A.actualCuspAngularCollarLoop) =
      integralSingularHomologyMap 1
        (⟨(fun x : A.sectionSevenEllipticCentralImage ↦ x.1),
          continuous_subtype_val⟩ : C(_, A.SectionSevenEllipticInterior))
        (loopHomologyClass D.actualCuspAngularEllipticCentralImageLoop) := by
  rw [integralSingularHomologyMap_loopHomologyClass,
    integralSingularHomologyMap_loopHomologyClass]
  exact congrArg loopHomologyClass
    D.actualCuspAngularEllipticCentralImageLoop_inclusion.symm

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end
