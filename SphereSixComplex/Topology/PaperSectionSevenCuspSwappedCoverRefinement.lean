module

public import SphereSixComplex.Topology.PaperSectionSevenCuspMappingTorusPhaseBridge
public import SphereSixComplex.Topology.PaperSectionSevenCuspSignedCoverRefinement

/-!
# Correctly oriented cusp-cover refinement

The explicit mapping-torus vertex open refines the order-four cusp open, while its edge open
refines the order-three cusp open.  Thus the target cover occurs in the reverse of its marked
order.  This file records the resulting refinement, transports its boundary through the canonical
cover swap, and isolates marked-overlap compatibility as the remaining geometric input.
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

/-- The cusp cover in the order dictated by the actual vertex/edge refinement. -/
public theorem actualCuspSwappedOpenCover
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.cuspOrderFourOpen ⊔ R.twoDiscCover.cuspOrderThreeOpen = ⊤ := by
  rw [sup_comm]
  exact R.twoDiscCover.cuspOpenCover

/-- Canonical Mayer--Vietoris comparison for the cusp collar in corrected order. -/
public noncomputable def actualCuspSwappedOpenCoverHomologyComparison
    (R : A.SectionSevenAffineRadialCompletionInput) :
    SphereSixComplex.BinaryOpenCover.OpenCoverHomologyComparison
      R.twoDiscCover.cuspOrderFourOpen R.twoDiscCover.cuspOrderThreeOpen :=
  SphereSixComplex.BinaryOpenCover.openCoverHomologyComparisonOfCover
    (actualCuspSwappedOpenCover R)

/-- Swapping the corrected cusp cover back to its marked order negates its boundary. -/
public theorem actualCuspSwappedOpenCover_boundary_swap
    (R : A.SectionSevenAffineRadialCompletionInput) (n : ℕ) :
    (actualCuspSwappedOpenCoverHomologyComparison R).boundary n ≫
        SphereSixComplex.BinaryOpenCover.openIntersectionSwapHomologyMap
          R.twoDiscCover.cuspOrderFourOpen R.twoDiscCover.cuspOrderThreeOpen n =
      -R.twoDiscCover.cuspOpenCoverHomologyComparison.boundary n := by
  exact SphereSixComplex.BinaryOpenCover.openCoverHomologyComparisonOfCover_boundary_swap
    (actualCuspSwappedOpenCover R) R.twoDiscCover.cuspOpenCover n

/-- The correctly oriented refinement datum.  No existence is asserted here: proving these two
global inclusions is precisely the remaining cover geometry. -/
public structure ActualCuspSwappedCoverRefinement
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop where
  vertex_le :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    mappingTorusVertexOpen G.clutching ≤ actualCuspMappingTorusOrderFourOpen R
  edge_le :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    mappingTorusEdgeOpen G.clutching ≤ actualCuspMappingTorusOrderThreeOpen R

/-- The corrected refinement is canonically natural before the target-cover swap. -/
public theorem actualCuspSwappedRefinement_boundary_naturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspSwappedCoverRefinement R) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫
        SphereSixComplex.BinaryOpenCover.openIntersectionRefinementHomologyMap
          C.vertex_le C.edge_le 1 ≫
        SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyMap
          (actualCuspMappingTorusToCollarTopCatMap A)
          R.twoDiscCover.cuspOrderFourOpen R.twoDiscCover.cuspOrderThreeOpen 1 =
      (SphereSixComplex.BinaryOpenCover.integralHomologyFunctor 2).map
          (actualCuspMappingTorusToCollarTopCatMap A) ≫
        (actualCuspSwappedOpenCoverHomologyComparison R).boundary 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact SphereSixComplex.BinaryOpenCover.OpenCoverHomologyComparison.boundary_refinement_pullback_naturality
    (actualCuspMappingTorusToCollarTopCatMap A)
    R.twoDiscCover.cuspOrderFourOpen R.twoDiscCover.cuspOrderThreeOpen
    C.vertex_le C.edge_le
    (mappingTorusOpenCoverHomologyComparison G.clutching)
    (actualCuspMappingTorusPulledBackSwappedHomologyComparison R)
    (actualCuspSwappedOpenCoverHomologyComparison R)
    (SphereSixComplex.BinaryOpenCover.openCoverHomologyComparisonOfCover_refinementNaturality
      C.vertex_le C.edge_le
      (mappingTorusOpenCover G.clutching)
      (actualCuspMappingTorusPulledBackSwappedOpenCover R))
    (SphereSixComplex.BinaryOpenCover.openCoverHomologyComparisonOfCover_pullbackNaturality
      (actualCuspMappingTorusToCollarTopCatMap A)
      R.twoDiscCover.cuspOrderFourOpen R.twoDiscCover.cuspOrderThreeOpen
      (actualCuspMappingTorusPulledBackSwappedOpenCover R)
      (actualCuspSwappedOpenCover R)) 1

/-- After returning the target overlap to marked order, the corrected refinement acquires the
expected minus sign. -/
public theorem actualCuspSwappedRefinement_boundary_swap_naturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspSwappedCoverRefinement R) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫
        SphereSixComplex.BinaryOpenCover.openIntersectionRefinementHomologyMap
          C.vertex_le C.edge_le 1 ≫
        SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyMap
          (actualCuspMappingTorusToCollarTopCatMap A)
          R.twoDiscCover.cuspOrderFourOpen R.twoDiscCover.cuspOrderThreeOpen 1 ≫
        SphereSixComplex.BinaryOpenCover.openIntersectionSwapHomologyMap
          R.twoDiscCover.cuspOrderFourOpen R.twoDiscCover.cuspOrderThreeOpen 1 =
      -((SphereSixComplex.BinaryOpenCover.integralHomologyFunctor 2).map
          (actualCuspMappingTorusToCollarTopCatMap A) ≫
        R.twoDiscCover.cuspOpenCoverHomologyComparison.boundary 1) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let swap := SphereSixComplex.BinaryOpenCover.openIntersectionSwapHomologyMap
    R.twoDiscCover.cuspOrderFourOpen R.twoDiscCover.cuspOrderThreeOpen 1
  have h := congrArg (fun q ↦ q ≫ swap)
    (actualCuspSwappedRefinement_boundary_naturality R C)
  simp only [Category.assoc] at h
  rw [actualCuspSwappedOpenCover_boundary_swap] at h
  simpa only [swap, Category.assoc, Preadditive.comp_neg] using h

/-- The overlap map induced by the corrected refinement, before compensating for the
Mayer--Vietoris sign of the cover swap. -/
public noncomputable def actualCuspSwappedRefinementRawOverlapTransport
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspSwappedCoverRefinement R) :
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
        R.twoDiscCover.cuspOrderFourOpen R.twoDiscCover.cuspOrderThreeOpen 1 ≫
      SphereSixComplex.BinaryOpenCover.openIntersectionSwapHomologyMap
        R.twoDiscCover.cuspOrderFourOpen R.twoDiscCover.cuspOrderThreeOpen 1)

/-- The signed overlap transport in the marked order. -/
public noncomputable def actualCuspSwappedRefinementOverlapTransport
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspSwappedCoverRefinement R) :
    ActualCuspVertexEdgeOverlapHomologyOne A →+
      CuspCoverIntersectionHomologyOne R :=
  -actualCuspSwappedRefinementRawOverlapTransport R C

private theorem swappedMappingTorusOpensUnionHomologyIso_hom_apply
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

/-- The unsigned corrected overlap map intertwines the connecting morphisms with one minus
sign, exactly as dictated by swapping the target cover. -/
public theorem actualCuspSwappedRefinementRaw_connectingNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspSwappedCoverRefinement R) :
    (actualCuspSwappedRefinementRawOverlapTransport R C).comp
        (actualCuspVertexEdgeCoverConnectingHom A) =
      -R.twoDiscCover.cuspOpenCoverConnectingHom := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
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
    R.twoDiscCover.cuspOrderFourOpen R.twoDiscCover.cuspOrderThreeOpen 1
  let swap := SphereSixComplex.BinaryOpenCover.openIntersectionSwapHomologyMap
    R.twoDiscCover.cuspOrderFourOpen R.twoDiscCover.cuspOrderThreeOpen 1
  let e := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  let xUnion := (SphereSixComplex.unionEquiv
    (fun _ : Unit ↦ G.clutching) 2).symm (e x)
  have hcat :
      U.hom ≫ (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫
          refine ≫ pullback ≫ swap =
        -(U.hom ≫
          (SphereSixComplex.BinaryOpenCover.integralHomologyFunctor 2).map
            (actualCuspMappingTorusToCollarTopCatMap A) ≫
          R.twoDiscCover.cuspOpenCoverHomologyComparison.boundary 1) := by
    have h := congrArg (fun q ↦ U.hom ≫ q)
      (actualCuspSwappedRefinement_boundary_swap_naturality R C)
    simpa only [U, refine, pullback, swap, Category.assoc,
      Preadditive.comp_neg] using h
  have happly := DFunLike.congr_fun (congrArg ConcreteCategory.hom hcat) xUnion
  have hUnion : ConcreteCategory.hom U.hom xUnion = e x := by
    change ConcreteCategory.hom U.hom
        ((SphereSixComplex.unionEquiv (fun _ : Unit ↦ G.clutching) 2).symm (e x)) = e x
    rw [swappedMappingTorusOpensUnionHomologyIso_hom_apply A, AddEquiv.apply_symm_apply]
  have hcancel : ConcreteCategory.hom
      ((SphereSixComplex.BinaryOpenCover.integralHomologyFunctor 2).map
        (actualCuspMappingTorusToCollarTopCatMap A)) (e x) = x := by
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  change ConcreteCategory.hom
      ((mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫
        refine ≫ pullback ≫ swap) (ConcreteCategory.hom U.hom xUnion) =
    -ConcreteCategory.hom (R.twoDiscCover.cuspOpenCoverHomologyComparison.boundary 1)
      (ConcreteCategory.hom
        ((SphereSixComplex.BinaryOpenCover.integralHomologyFunctor 2).map
          (actualCuspMappingTorusToCollarTopCatMap A))
        (ConcreteCategory.hom U.hom xUnion)) at happly
  rw [hUnion, hcancel] at happly
  have hsourceCat :
      (U.hom ≫ (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫ I.inv) ≫
          (I.hom ≫ refine ≫ pullback ≫ swap) =
        U.hom ≫ (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫
          refine ≫ pullback ≫ swap := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hsourceApply := DFunLike.congr_fun
    (congrArg ConcreteCategory.hom hsourceCat) xUnion
  change ConcreteCategory.hom (I.hom ≫ refine ≫ pullback ≫ swap)
      (ConcreteCategory.hom
        (U.hom ≫ (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫ I.inv)
        xUnion) =
    ConcreteCategory.hom
      ((mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫
        refine ≫ pullback ≫ swap) (ConcreteCategory.hom U.hom xUnion) at hsourceApply
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
      actualCuspSwappedRefinementRawOverlapTransport R C y =
        ConcreteCategory.hom (I.hom ≫ refine ≫ pullback ≫ swap) y := by
    rfl
  change actualCuspSwappedRefinementRawOverlapTransport R C
      (actualCuspVertexEdgeCoverConnectingHom A x) =
    -R.twoDiscCover.cuspOpenCoverConnectingHom x
  calc
    _ = actualCuspSwappedRefinementRawOverlapTransport R C
        (ConcreteCategory.hom
          (U.hom ≫ (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫ I.inv)
          xUnion) := congrArg (actualCuspSwappedRefinementRawOverlapTransport R C) hconnecting
    _ = ConcreteCategory.hom (I.hom ≫ refine ≫ pullback ≫ swap)
        (ConcreteCategory.hom
          (U.hom ≫ (mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫ I.inv)
          xUnion) := htransport _
    _ = ConcreteCategory.hom
        ((mappingTorusOpenCoverHomologyComparison G.clutching).boundary 1 ≫
          refine ≫ pullback ≫ swap) (e x) := hsourceApply
    _ = _ := happly

/-- Negating the raw transport cancels the cover-swap sign and gives the marked-order connecting
naturality required by the two-leg reduction. -/
public theorem actualCuspSwappedRefinement_connectingNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspSwappedCoverRefinement R) :
    ActualCuspTwoLegConnectingNaturality R
      (actualCuspSwappedRefinementOverlapTransport R C) := by
  rw [ActualCuspTwoLegConnectingNaturality,
    actualCuspSwappedRefinementOverlapTransport]
  apply AddMonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun
    (actualCuspSwappedRefinementRaw_connectingNaturality R C) x
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.neg_apply, neg_neg] using congrArg Neg.neg hx

/-- A correctly oriented refinement together with the one remaining marked-overlap equality
proves the pulled-back invariant-basis calculation. -/
public theorem cuspPulledBackMarkedInvariantBasisData_of_swappedCoverRefinement
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspSwappedCoverRefinement R)
    (hmarked : ActualCuspTwoLegMarkedOverlapNaturality R
      (actualCuspSwappedRefinementOverlapTransport R C)) :
    CuspPulledBackMarkedInvariantBasisData R := by
  apply cuspPulledBackMarkedInvariantBasisData_of_twoLegCoverChainNaturality R
    (actualCuspSwappedRefinementOverlapTransport R C)
  exact ⟨actualCuspSwappedRefinement_connectingNaturality R C, hmarked⟩

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
