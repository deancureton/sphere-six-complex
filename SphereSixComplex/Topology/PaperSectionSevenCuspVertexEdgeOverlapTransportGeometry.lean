module

public import SphereSixComplex.Topology.PaperSectionSevenCuspFiberBandTopologicalSquare

/-!
# Geometry of both vertex--edge overlap legs in the actual cusp collar

The explicit mapping-torus cover has lower and upper overlap fibres.  Radial normalization
transports the entire overlap to the actual cusp collar, and hence to the elliptic interior.
This file constructs the upper leg, complements the existing lower-leg construction, and proves
that the two legs induce the same map after forgetting any proposed corestriction to the affine
band overlap.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

namespace SectionSevenEllipticTwoDiscCoverData

/-- Transport the whole vertex--edge overlap of the standard mapping-torus cover into the
actual cusp collar. -/
public noncomputable def actualCuspVertexEdgeOverlapToCollarMap (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C((vertexPiece (fun _ : Unit ↦ G.clutching) ∩
        edgePiece (fun _ : Unit ↦ G.clutching) :
          Set (CircleMappingTorus G.clutching)),
      A.openEmbeddingStarData.collarSource 0) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact G.totalHomotopyEquiv.invFun.comp
    ⟨Subtype.val, continuous_subtype_val⟩

/-- Transport the whole vertex--edge overlap through the cusp collar to the elliptic interior. -/
public noncomputable def actualCuspVertexEdgeOverlapToEllipticInteriorMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C((vertexPiece (fun _ : Unit ↦ G.clutching) ∩
        edgePiece (fun _ : Unit ↦ G.clutching) :
          Set (CircleMappingTorus G.clutching)),
      A.SectionSevenEllipticInterior) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact D.cuspToEllipticInteriorMap.hom.comp
    (actualCuspVertexEdgeOverlapToCollarMap A)

/-- The upper overlap fibre in the explicit vertex--edge cover of the actual cusp mapping
torus. -/
public noncomputable def actualCuspMappingTorusHighOverlapFiberMap (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber, (vertexPiece (fun _ : Unit ↦ G.clutching) ∩
      edgePiece (fun _ : Unit ↦ G.clutching) :
        Set (CircleMappingTorus G.clutching))) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact overlapPt (fun _ : Unit ↦ G.clutching) uThreeQuarters_mem_overlapBand ()

/-- The upper overlap fibre transported through the actual cusp collar to the elliptic
interior. -/
public noncomputable def actualCuspMappingTorusHighOverlapFiberToEllipticInteriorMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber, A.SectionSevenEllipticInterior) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact D.actualCuspVertexEdgeOverlapToEllipticInteriorMap.comp
    (actualCuspMappingTorusHighOverlapFiberMap A)

/-- The lower overlap construction factors through transport of the whole vertex--edge
overlap. -/
public theorem actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap_factor :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap =
      D.cuspToEllipticInteriorMap.hom.comp
        ((actualCuspVertexEdgeOverlapToCollarMap A).comp
          (actualCuspMappingTorusLowOverlapFiberMap A)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rfl

/-- After forgetting the overlap witness, the upper fibre is the mapping-torus slice at the
three-quarter point. -/
public theorem actualCuspMappingTorusHighOverlapFiberToEllipticInteriorMap_eq :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    D.actualCuspMappingTorusHighOverlapFiberToEllipticInteriorMap =
      D.cuspToEllipticInteriorMap.hom.comp
        (G.totalHomotopyEquiv.invFun.comp
          (torusPt (fun _ : Unit ↦ G.clutching) () uThreeQuarters)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply ContinuousMap.ext
  intro x
  rfl

/-- Moving the mapping-torus fibre from the vertex to the oriented upper overlap gives a
homotopic map into the elliptic interior. -/
public theorem actualCuspMappingTorusFiberToEllipticInteriorMap_homotopic_highOverlap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ContinuousMap.Homotopic
      D.actualCuspMappingTorusFiberToEllipticInteriorMap
      D.actualCuspMappingTorusHighOverlapFiberToEllipticInteriorMap := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [D.actualCuspMappingTorusHighOverlapFiberToEllipticInteriorMap_eq]
  exact ContinuousMap.Homotopic.comp
    (.refl D.cuspToEllipticInteriorMap.hom)
    (ContinuousMap.Homotopic.comp
      (.refl G.totalHomotopyEquiv.invFun)
      ⟨(torusPtHomotopy (fun _ : Unit ↦ G.clutching) () uThreeQuarters).symm⟩)

/-- The low and high overlap fibres are homotopic after transport to the elliptic interior. -/
public theorem actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap_homotopic_highOverlap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ContinuousMap.Homotopic
      D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap
      D.actualCuspMappingTorusHighOverlapFiberToEllipticInteriorMap := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact D.actualCuspMappingTorusFiberToEllipticInteriorMap_homotopic_lowOverlap.symm.trans
    D.actualCuspMappingTorusFiberToEllipticInteriorMap_homotopic_highOverlap

/-- Consequently the two overlap legs induce the same map on integral singular homology after
forgetting a band corestriction. -/
public theorem actualCuspMappingTorusLowOverlapFiber_homology_eq_highOverlap (k : ℕ) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap k
        D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap =
      integralSingularHomologyMap k
        D.actualCuspMappingTorusHighOverlapFiberToEllipticInteriorMap := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  ext x
  change ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap)) x =
    ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom D.actualCuspMappingTorusHighOverlapFiberToEllipticInteriorMap)) x
  rw [integralSingularHomologyMap_eq_of_homotopic
    D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap_homotopic_highOverlap k]

/-- In the explicit two-leg coordinates, transport of the whole overlap to the elliptic
interior is the sum of the transported lower and upper fibre maps. -/
public theorem actualCuspVertexEdgeOverlapToEllipticInteriorMap_overlapEquiv
    (k : ℕ)
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      (Unit → IntegralSingularHomology k G.Fiber) ×
        (Unit → IntegralSingularHomology k G.Fiber)) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap k
        D.actualCuspVertexEdgeOverlapToEllipticInteriorMap
        (overlapEquiv (fun _ : Unit ↦ G.clutching) k p) =
      integralSingularHomologyMap k
          D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap (p.1 ()) +
        integralSingularHomologyMap k
          D.actualCuspMappingTorusHighOverlapFiberToEllipticInteriorMap (p.2 ()) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change integralSingularHomologyMap k
      D.actualCuspVertexEdgeOverlapToEllipticInteriorMap
      (overlapLegSum (fun _ : Unit ↦ G.clutching) k p) = _
  rw [overlapLegSum_apply]
  simp only [Fintype.sum_unique, map_add]
  congr 1
  · calc
      _ = integralSingularHomologyMap k
          (D.actualCuspVertexEdgeOverlapToEllipticInteriorMap.comp
            (overlapPt (fun _ : Unit ↦ G.clutching)
              uQuarter_mem_overlapBand ())) (p.1 ()) :=
        (DFunLike.congr_fun (integralSingularHomologyMap_comp k _ _) (p.1 ())).symm
      _ = _ := by rfl
  · calc
      _ = integralSingularHomologyMap k
          (D.actualCuspVertexEdgeOverlapToEllipticInteriorMap.comp
            (overlapPt (fun _ : Unit ↦ G.clutching)
              uThreeQuarters_mem_overlapBand ())) (p.2 ()) :=
        (DFunLike.congr_fun (integralSingularHomologyMap_comp k _ _) (p.2 ())).symm
      _ = _ := by rfl

/-- Since the two transported fibre slices are homotopic, the entire overlap transport forgets
the separation of the two legs and depends only on their sum. -/
public theorem actualCuspVertexEdgeOverlapToEllipticInteriorMap_overlapEquiv_eq_sum
    (k : ℕ)
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      (Unit → IntegralSingularHomology k G.Fiber) ×
        (Unit → IntegralSingularHomology k G.Fiber)) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap k
        D.actualCuspVertexEdgeOverlapToEllipticInteriorMap
        (overlapEquiv (fun _ : Unit ↦ G.clutching) k p) =
      integralSingularHomologyMap k
        D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap
        (p.1 () + p.2 ()) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  calc
    _ = integralSingularHomologyMap k
          D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap (p.1 ()) +
        integralSingularHomologyMap k
          D.actualCuspMappingTorusHighOverlapFiberToEllipticInteriorMap (p.2 ()) :=
      D.actualCuspVertexEdgeOverlapToEllipticInteriorMap_overlapEquiv k p
    _ = integralSingularHomologyMap k
          D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap (p.1 ()) +
        integralSingularHomologyMap k
          D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap (p.2 ()) := by
      rw [DFunLike.congr_fun
        (D.actualCuspMappingTorusLowOverlapFiber_homology_eq_highOverlap k) (p.2 ())]
    _ = _ := (map_add _ _ _).symm

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
