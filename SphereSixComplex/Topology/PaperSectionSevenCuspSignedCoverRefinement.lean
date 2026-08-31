module

public import SphereSixComplex.Topology.BinaryOpenCoverOrientedRefinementNaturality
public import SphereSixComplex.Topology.CanonicalProductWangBoundaryNaturality
public import SphereSixComplex.Topology.PaperSectionSevenCuspTwoLegCoverChainResidual
public import SphereSixComplex.Topology.PaperSectionSevenCuspVertexEdgeOverlapTransportGeometry

/-!
# Signed refinement of the cusp mapping-torus cover

The vertex/edge cover and the pulled-back cusp cover already have canonical generated-chain
Mayer--Vietoris sequences.  The missing geometric datum is an oriented refinement: the vertex
open must enter the order-three open and the edge open the order-four open.  This file constructs
the resulting overlap transport and proves its connecting-map naturality from the existing
short-complex naturality theorem.  The remaining marked datum is one signed fourth-coordinate
identity for this concrete transport.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticInteriorMarkedCycleData
open SphereSixComplex.Topology.CanonicalProductWangBoundaryNaturality

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- The radial mapping-torus equivalence, directed from the mapping torus to the actual cusp
collar. -/
public noncomputable def actualCuspMappingTorusToCollarTopCatMap (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    TopCat.of (CircleMappingTorus G.clutching) ⟶
      TopCat.of (A.openEmbeddingStarData.collarSource 0) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact TopCat.ofHom G.totalHomotopyEquiv.invFun

/-- The pullback of the order-three cusp open to the radial mapping torus. -/
public abbrev actualCuspMappingTorusOrderThreeOpen
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    Opens (TopCat.of (CircleMappingTorus G.clutching)) :=
  Opens.map (actualCuspMappingTorusToCollarTopCatMap A) |>.obj
    R.twoDiscCover.cuspOrderThreeOpen

/-- The pullback of the order-four cusp open to the radial mapping torus. -/
public abbrev actualCuspMappingTorusOrderFourOpen
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    Opens (TopCat.of (CircleMappingTorus G.clutching)) :=
  Opens.map (actualCuspMappingTorusToCollarTopCatMap A) |>.obj
    R.twoDiscCover.cuspOrderFourOpen

/-- Pullback of the cusp cover still covers the mapping torus. -/
public theorem actualCuspMappingTorusPulledBackOpenCover
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspMappingTorusOrderThreeOpen R ⊔
      actualCuspMappingTorusOrderFourOpen R = ⊤ := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change (Opens.map (actualCuspMappingTorusToCollarTopCatMap A)).obj
    (R.twoDiscCover.cuspOrderThreeOpen ⊔ R.twoDiscCover.cuspOrderFourOpen) = ⊤
  rw [R.twoDiscCover.cuspOpenCover]
  rfl

/-- The canonical homology comparison for the pulled-back cusp cover on the mapping torus. -/
public noncomputable def actualCuspMappingTorusPulledBackHomologyComparison
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    SphereSixComplex.BinaryOpenCover.OpenCoverHomologyComparison
      (actualCuspMappingTorusOrderThreeOpen R)
      (actualCuspMappingTorusOrderFourOpen R) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact SphereSixComplex.BinaryOpenCover.openCoverHomologyComparisonOfCover
    (actualCuspMappingTorusPulledBackOpenCover R)

/-- The exact geometric chain-refinement datum missing from the current cusp APIs.  The first
two fields orient the refinement.  The last field says that the canonical ordinary-homology
comparisons are induced by the resulting morphism of generated cover-chain short complexes. -/
public structure ActualCuspOrientedCoverRefinement
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop where
  vertex_le :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    mappingTorusVertexOpen G.clutching ≤ actualCuspMappingTorusOrderThreeOpen R
  edge_le :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    mappingTorusEdgeOpen G.clutching ≤ actualCuspMappingTorusOrderFourOpen R
  comparison_naturality :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (mappingTorusOpenCoverHomologyComparison G.clutching).RefinementNaturality
      vertex_le edge_le (actualCuspMappingTorusPulledBackHomologyComparison R)

/-- The map from the full two-component vertex/edge overlap to the pulled-back cusp-cover
intersection induced by an oriented refinement and the radial mapping-torus equivalence. -/
public noncomputable def actualCuspSignedRefinementOverlapTransport
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspOrientedCoverRefinement R) :
    ActualCuspVertexEdgeOverlapHomologyOne A →+
      CuspCoverIntersectionHomologyOne R := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact ConcreteCategory.hom
    ((SphereSixComplex.BinaryOpenCover.opensIntersectionHomologyIso
        (mappingTorusVertexOpen G.clutching)
        (mappingTorusEdgeOpen G.clutching) 1).hom ≫
      SphereSixComplex.BinaryOpenCover.openIntersectionRefinementHomologyMap
        C.vertex_le C.edge_le 1 ≫
      SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyMap
        (actualCuspMappingTorusToCollarTopCatMap A)
        R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen 1)

/-- At the canonical comparison level, the signed connecting morphism is natural under the
oriented refinement.  Its sign is fixed by the order `vertex → order-three`,
`edge → order-four`; swapping the two fields would negate the Mayer--Vietoris boundary. -/
public theorem actualCuspSignedRefinement_boundary_naturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspOrientedCoverRefinement R) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫
        SphereSixComplex.BinaryOpenCover.openIntersectionRefinementHomologyMap
          C.vertex_le C.edge_le 1 ≫
        SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyMap
          (actualCuspMappingTorusToCollarTopCatMap A)
          R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen 1 =
      (SphereSixComplex.BinaryOpenCover.integralHomologyFunctor 2).map
          (actualCuspMappingTorusToCollarTopCatMap A) ≫
        R.twoDiscCover.cuspOpenCoverHomologyComparison.boundary 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact SphereSixComplex.BinaryOpenCover.OpenCoverHomologyComparison.boundary_refinement_pullback_naturality
      (actualCuspMappingTorusToCollarTopCatMap A)
      R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen
      C.vertex_le C.edge_le
      (mappingTorusOpenCoverHomologyComparison G.clutching)
      (actualCuspMappingTorusPulledBackHomologyComparison R)
      R.twoDiscCover.cuspOpenCoverHomologyComparison
      C.comparison_naturality
      (SphereSixComplex.BinaryOpenCover.openCoverHomologyComparisonOfCover_pullbackNaturality
          (actualCuspMappingTorusToCollarTopCatMap A)
          R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen
          (actualCuspMappingTorusPulledBackOpenCover R)
          R.twoDiscCover.cuspOpenCover) 1

private theorem mappingTorusOpensUnionHomologyIso_hom_apply
    (A : PaperAnalyticData)
    (x : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 2
        (vertexPiece (fun _ : Unit ↦ G.clutching) ∪
          edgePiece (fun _ : Unit ↦ G.clutching) : Set (CircleMappingTorus G.clutching))) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ConcreteCategory.hom
        (SphereSixComplex.BinaryOpenCover.opensUnionHomologyIso
          (mappingTorusVertexOpen G.clutching) (mappingTorusEdgeOpen G.clutching)
          (mappingTorusOpenCover G.clutching) 2).hom x =
      SphereSixComplex.unionEquiv (fun _ : Unit ↦ G.clutching) 2 x := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  have htop :
      (TopCat.isoOfHomeo (SphereSixComplex.BinaryOpenCover.opensUnionHomeomorph
        (mappingTorusVertexOpen G.clutching) (mappingTorusEdgeOpen G.clutching)
        (mappingTorusOpenCover G.clutching))).hom =
        TopCat.ofHom (coverUnionCM (fun _ : Unit ↦ G.clutching)) := by
    ext y
    rfl
  have hmap := congrArg
    (SphereSixComplex.BinaryOpenCover.integralHomologyFunctor 2).map htop
  exact DFunLike.congr_fun (congrArg ConcreteCategory.hom hmap) x

/-- The categorical refinement square supplies the legacy two-leg connecting naturality. -/
public theorem actualCuspSignedRefinement_connectingNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspOrientedCoverRefinement R) :
    ActualCuspTwoLegConnectingNaturality R
      (actualCuspSignedRefinementOverlapTransport R C) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [ActualCuspTwoLegConnectingNaturality]
  apply AddMonoidHom.ext
  intro x
  let U := SphereSixComplex.BinaryOpenCover.opensUnionHomologyIso
    (mappingTorusVertexOpen G.clutching) (mappingTorusEdgeOpen G.clutching)
    (mappingTorusOpenCover G.clutching) 2
  let I := SphereSixComplex.BinaryOpenCover.opensIntersectionHomologyIso
    (mappingTorusVertexOpen G.clutching) (mappingTorusEdgeOpen G.clutching) 1
  let refine := SphereSixComplex.BinaryOpenCover.openIntersectionRefinementHomologyMap
    C.vertex_le C.edge_le 1
  let pullback := SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyMap
    (actualCuspMappingTorusToCollarTopCatMap A)
    R.twoDiscCover.cuspOrderThreeOpen R.twoDiscCover.cuspOrderFourOpen 1
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  let xUnion := (SphereSixComplex.unionEquiv
    (fun _ : Unit ↦ G.clutching) 2).symm (e x)
  have hcat :
      U.hom ≫ (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫
          refine ≫ pullback =
        U.hom ≫
          (SphereSixComplex.BinaryOpenCover.integralHomologyFunctor 2).map
            (actualCuspMappingTorusToCollarTopCatMap A) ≫
          R.twoDiscCover.cuspOpenCoverHomologyComparison.boundary 1 := by
    simpa only [U, refine, pullback, Category.assoc] using
      congrArg (fun q ↦ U.hom ≫ q)
        (actualCuspSignedRefinement_boundary_naturality R C)
  have happly := DFunLike.congr_fun (congrArg ConcreteCategory.hom hcat) xUnion
  have hUnion : ConcreteCategory.hom U.hom xUnion = e x := by
    change ConcreteCategory.hom U.hom
        ((SphereSixComplex.unionEquiv (fun _ : Unit ↦ G.clutching) 2).symm (e x)) = e x
    rw [mappingTorusOpensUnionHomologyIso_hom_apply A, AddEquiv.apply_symm_apply]
  have hcancel : ConcreteCategory.hom
      ((SphereSixComplex.BinaryOpenCover.integralHomologyFunctor 2).map
        (actualCuspMappingTorusToCollarTopCatMap A)) (e x) = x := by
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  change ConcreteCategory.hom
      ((mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫
        refine ≫ pullback) (ConcreteCategory.hom U.hom xUnion) =
    ConcreteCategory.hom (R.twoDiscCover.cuspOpenCoverHomologyComparison.boundary 1)
      (ConcreteCategory.hom
        ((SphereSixComplex.BinaryOpenCover.integralHomologyFunctor 2).map
          (actualCuspMappingTorusToCollarTopCatMap A))
        (ConcreteCategory.hom U.hom xUnion)) at happly
  rw [hUnion, hcancel] at happly
  have hsourceCat :
      (U.hom ≫ (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫ I.inv) ≫
          (I.hom ≫ refine ≫ pullback) =
        U.hom ≫ (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫
          refine ≫ pullback := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hsourceApply := DFunLike.congr_fun
    (congrArg ConcreteCategory.hom hsourceCat) xUnion
  change ConcreteCategory.hom (I.hom ≫ refine ≫ pullback)
      (ConcreteCategory.hom
        (U.hom ≫ (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫ I.inv)
        xUnion) =
    ConcreteCategory.hom
      ((mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫
        refine ≫ pullback) (ConcreteCategory.hom U.hom xUnion) at hsourceApply
  rw [hUnion] at hsourceApply
  have hconnecting : actualCuspVertexEdgeCoverConnectingHom A x =
      ConcreteCategory.hom
        (U.hom ≫ (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫ I.inv)
        xUnion := by
    unfold actualCuspVertexEdgeCoverConnectingHom
    simp only [AddMonoidHom.comp_apply, e, xUnion]
    unfold SphereSixComplex.coverBoundary
    rfl
  have htransport (y : ActualCuspVertexEdgeOverlapHomologyOne A) :
      actualCuspSignedRefinementOverlapTransport R C y =
        ConcreteCategory.hom (I.hom ≫ refine ≫ pullback) y := by
    rfl
  change (actualCuspSignedRefinementOverlapTransport R C)
      (actualCuspVertexEdgeCoverConnectingHom A x) =
    R.twoDiscCover.cuspOpenCoverConnectingHom x
  calc
    _ = (actualCuspSignedRefinementOverlapTransport R C)
        (ConcreteCategory.hom
          (U.hom ≫ (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫ I.inv)
          xUnion) := congrArg (actualCuspSignedRefinementOverlapTransport R C) hconnecting
    _ = ConcreteCategory.hom (I.hom ≫ refine ≫ pullback)
        (ConcreteCategory.hom
          (U.hom ≫ (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫ I.inv)
          xUnion) := htransport _
    _ = ConcreteCategory.hom
        ((mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫
          refine ≫ pullback) (e x) := hsourceApply
    _ = _ := happly

/-- The marked sign required of the concrete full-overlap refinement transport. -/
public def ActualCuspOrientedCoverRefinementMarkedSign
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspOrientedCoverRefinement R) : Prop :=
  (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment).comp
      (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne.comp
        (actualCuspSignedRefinementOverlapTransport R C)) =
    (actualCuspFiberFourthCoordinateHom A).comp
      (actualCuspVertexEdgeOverlapFirstLeg A)

/-- The oriented refinement and its marked sign prove the exact remaining invariant-basis
statement. -/
public theorem cuspPulledBackMarkedInvariantBasisData_of_signedCoverRefinement
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspOrientedCoverRefinement R)
    (hsign : ActualCuspOrientedCoverRefinementMarkedSign R C) :
    CuspPulledBackMarkedInvariantBasisData R := by
  apply cuspPulledBackMarkedInvariantBasisData_of_twoLegCoverChainNaturality R
    (actualCuspSignedRefinementOverlapTransport R C)
  exact ⟨actualCuspSignedRefinement_connectingNaturality R C, hsign⟩

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
