module

public import SphereSixComplex.Topology.PaperSectionSevenCuspSignedCoverRefinement
public import SphereSixComplex.Topology.PaperSectionSevenCuspWangFullFibreSlice

/-!
# Geometry required by the signed cusp-cover refinement

The canonical ordinary-homology comparisons are natural under every oriented refinement of
binary open covers.  Consequently the proposed cusp refinement is reduced to two pointwise
open-membership statements.  The marked sign is also decomposed into its exact low- and
high-overlap-leg equations.
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

/-- Pointwise geometric content of the vertex-to-order-three inclusion. -/
public def ActualCuspVertexOrderThreePointwiseMembership
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  ∀ z : CircleMappingTorus G.clutching,
    z ∈ vertexPiece (fun _ : Unit ↦ G.clutching) →
      G.totalHomotopyEquiv.invFun z ∈ R.twoDiscCover.cuspOrderThreeOpen

/-- Pointwise geometric content of the edge-to-order-four inclusion. -/
public def ActualCuspEdgeOrderFourPointwiseMembership
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  ∀ z : CircleMappingTorus G.clutching,
    z ∈ edgePiece (fun _ : Unit ↦ G.clutching) →
      G.totalHomotopyEquiv.invFun z ∈ R.twoDiscCover.cuspOrderFourOpen

/-- A sufficient central-height bound placing the vertex member in the order-three side. -/
public def ActualCuspVertexOrderThreeHeightBound
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  ∀ z : CircleMappingTorus G.clutching,
    z ∈ vertexPiece (fun _ : Unit ↦ G.clutching) →
      A.sectionSevenEllipticCentralHeight
        ⟨R.twoDiscCover.cuspToEllipticInteriorMap (G.totalHomotopyEquiv.invFun z),
          R.twoDiscCover.cuspToEllipticInteriorMap_mem_centralImage _⟩ < 2 / 3

/-- A sufficient central-height bound placing the edge member in the order-four side. -/
public def ActualCuspEdgeOrderFourHeightBound
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  ∀ z : CircleMappingTorus G.clutching,
    z ∈ edgePiece (fun _ : Unit ↦ G.clutching) →
      1 / 3 < A.sectionSevenEllipticCentralHeight
        ⟨R.twoDiscCover.cuspToEllipticInteriorMap (G.totalHomotopyEquiv.invFun z),
          R.twoDiscCover.cuspToEllipticInteriorMap_mem_centralImage _⟩

/-- The upper height bound implies the literal vertex membership. -/
public theorem actualCuspVertexOrderThreePointwiseMembership_of_heightBound
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : ActualCuspVertexOrderThreeHeightBound R) :
    ActualCuspVertexOrderThreePointwiseMembership R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  intro z hz
  let q := G.totalHomotopyEquiv.invFun z
  let x := R.twoDiscCover.cuspToEllipticInteriorMap q
  have hxcentral : x ∈ A.sectionSevenEllipticCentralImage :=
    R.twoDiscCover.cuspToEllipticInteriorMap_mem_centralImage q
  change x ∈ A.sectionSevenActualAffineSplit.allocation.orderThreeSide
  right
  exact ⟨⟨x, hxcentral⟩, h z hz, rfl⟩

/-- The lower height bound implies the literal edge membership. -/
public theorem actualCuspEdgeOrderFourPointwiseMembership_of_heightBound
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : ActualCuspEdgeOrderFourHeightBound R) :
    ActualCuspEdgeOrderFourPointwiseMembership R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  intro z hz
  let q := G.totalHomotopyEquiv.invFun z
  let x := R.twoDiscCover.cuspToEllipticInteriorMap q
  have hxcentral : x ∈ A.sectionSevenEllipticCentralImage :=
    R.twoDiscCover.cuspToEllipticInteriorMap_mem_centralImage q
  change x ∈ A.sectionSevenActualAffineSplit.allocation.orderFourSide
  right
  exact ⟨⟨x, hxcentral⟩, h z hz, rfl⟩

/-- The vertex refinement inequality is exactly its pointwise membership statement. -/
public theorem actualCuspVertex_le_iff_pointwiseMembership
    (R : A.SectionSevenAffineRadialCompletionInput) :
    (let G := A.actualCuspRadialClutchingData
     let _ := G.fiberTopology
     mappingTorusVertexOpen G.clutching ≤ actualCuspMappingTorusOrderThreeOpen R) ↔
      ActualCuspVertexOrderThreePointwiseMembership R := by
  rfl

/-- The edge refinement inequality is exactly its pointwise membership statement. -/
public theorem actualCuspEdge_le_iff_pointwiseMembership
    (R : A.SectionSevenAffineRadialCompletionInput) :
    (let G := A.actualCuspRadialClutchingData
     let _ := G.fiberTopology
     mappingTorusEdgeOpen G.clutching ≤ actualCuspMappingTorusOrderFourOpen R) ↔
      ActualCuspEdgeOrderFourPointwiseMembership R := by
  rfl

/-- Once the two literal memberships are known, canonical chain naturality constructs the
entire oriented cover refinement. -/
public theorem actualCuspOrientedCoverRefinement_of_pointwiseMembership
    (R : A.SectionSevenAffineRadialCompletionInput)
    (hvertex : ActualCuspVertexOrderThreePointwiseMembership R)
    (hedge : ActualCuspEdgeOrderFourPointwiseMembership R) :
    ActualCuspOrientedCoverRefinement R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  have hV : mappingTorusVertexOpen G.clutching ≤
      actualCuspMappingTorusOrderThreeOpen R :=
    (actualCuspVertex_le_iff_pointwiseMembership R).2 hvertex
  have hE : mappingTorusEdgeOpen G.clutching ≤
      actualCuspMappingTorusOrderFourOpen R :=
    (actualCuspEdge_le_iff_pointwiseMembership R).2 hedge
  exact {
    vertex_le := hV
    edge_le := hE
    comparison_naturality :=
      SphereSixComplex.BinaryOpenCover.openCoverHomologyComparisonOfCover_refinementNaturality
        hV hE (mappingTorusOpenCover G.clutching)
        (actualCuspMappingTorusPulledBackOpenCover R)
  }

/-- The two explicit central-height inequalities construct the full oriented refinement. -/
public theorem actualCuspOrientedCoverRefinement_of_heightBounds
    (R : A.SectionSevenAffineRadialCompletionInput)
    (hvertex : ActualCuspVertexOrderThreeHeightBound R)
    (hedge : ActualCuspEdgeOrderFourHeightBound R) :
    ActualCuspOrientedCoverRefinement R :=
  actualCuspOrientedCoverRefinement_of_pointwiseMembership R
    (actualCuspVertexOrderThreePointwiseMembership_of_heightBound R hvertex)
    (actualCuspEdgeOrderFourPointwiseMembership_of_heightBound R hedge)

/-- Thus the oriented refinement has no additional chain-level residual: it is equivalent to
the two literal pointwise inclusions. -/
public theorem actualCuspOrientedCoverRefinement_iff_pointwiseMembership
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspOrientedCoverRefinement R ↔
      ActualCuspVertexOrderThreePointwiseMembership R ∧
        ActualCuspEdgeOrderFourPointwiseMembership R := by
  constructor
  · intro C
    exact ⟨(actualCuspVertex_le_iff_pointwiseMembership R).1 C.vertex_le,
      (actualCuspEdge_le_iff_pointwiseMembership R).1 C.edge_le⟩
  · rintro ⟨hvertex, hedge⟩
    exact actualCuspOrientedCoverRefinement_of_pointwiseMembership R hvertex hedge

/-- A first-homology class supported on the oriented low overlap leg. -/
public noncomputable def actualCuspVertexEdgeOverlapLowLegClass
    (x : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber) :
    ActualCuspVertexEdgeOverlapHomologyOne A := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact overlapEquiv (fun _ : Unit ↦ G.clutching) 1
    (fun _ : Unit ↦ x, fun _ : Unit ↦ 0)

/-- A first-homology class supported on the oriented high overlap leg. -/
public noncomputable def actualCuspVertexEdgeOverlapHighLegClass
    (x : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber) :
    ActualCuspVertexEdgeOverlapHomologyOne A := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact overlapEquiv (fun _ : Unit ↦ G.clutching) 1
    (fun _ : Unit ↦ 0, fun _ : Unit ↦ x)

@[simp]
public theorem actualCuspVertexEdgeOverlapFirstLeg_lowLegClass
    (x : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber) :
    actualCuspVertexEdgeOverlapFirstLeg A
      (actualCuspVertexEdgeOverlapLowLegClass (A := A) x) = x := by
  simp [actualCuspVertexEdgeOverlapFirstLeg, actualCuspVertexEdgeOverlapLowLegClass]

@[simp]
public theorem actualCuspVertexEdgeOverlapFirstLeg_highLegClass
    (x : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber) :
    actualCuspVertexEdgeOverlapFirstLeg A
      (actualCuspVertexEdgeOverlapHighLegClass (A := A) x) = 0 := by
  simp [actualCuspVertexEdgeOverlapFirstLeg, actualCuspVertexEdgeOverlapHighLegClass]

/-- Every class of the two-component overlap is the sum of its low and high parts. -/
public theorem actualCuspVertexEdgeOverlap_eq_lowLeg_add_highLeg
    (z : ActualCuspVertexEdgeOverlapHomologyOne A) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    let e := overlapEquiv (fun _ : Unit ↦ G.clutching) 1
    let p := e.symm z
    z = actualCuspVertexEdgeOverlapLowLegClass (A := A) (p.1 ()) +
      actualCuspVertexEdgeOverlapHighLegClass (A := A) (p.2 ()) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := overlapEquiv (fun _ : Unit ↦ G.clutching) 1
  let p := e.symm z
  calc
    z = e p := (e.apply_symm_apply z).symm
    _ = actualCuspVertexEdgeOverlapLowLegClass (A := A) (p.1 ()) +
        actualCuspVertexEdgeOverlapHighLegClass (A := A) (p.2 ()) := by
      change e p = e (fun _ : Unit ↦ p.1 (), fun _ : Unit ↦ 0) +
        e (fun _ : Unit ↦ 0, fun _ : Unit ↦ p.2 ())
      rw [← e.map_add]
      congr 1
      ext <;> simp

/-- The marked sign is exactly the conjunction of the positive low-leg formula and vanishing
of the high leg.  This is the smallest coordinate-level residual exposed by the two-leg cover. -/
public theorem actualCuspOrientedCoverRefinementMarkedSign_iff_low_high
    (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspOrientedCoverRefinement R) :
    ActualCuspOrientedCoverRefinementMarkedSign R C ↔
      (∀ x, (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
          (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne
            (actualCuspSignedRefinementOverlapTransport R C
              (actualCuspVertexEdgeOverlapLowLegClass (A := A) x))) =
        actualCuspFiberFourthCoordinateHom A x) ∧
      (∀ x, (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
          (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne
            (actualCuspSignedRefinementOverlapTransport R C
              (actualCuspVertexEdgeOverlapHighLegClass (A := A) x))) = 0) := by
  constructor
  · intro h
    constructor
    · intro x
      have hx := DFunLike.congr_fun h
        (actualCuspVertexEdgeOverlapLowLegClass (A := A) x)
      simpa only [AddMonoidHom.comp_apply,
        actualCuspVertexEdgeOverlapFirstLeg_lowLegClass] using hx
    · intro x
      have hx := DFunLike.congr_fun h
        (actualCuspVertexEdgeOverlapHighLegClass (A := A) x)
      simpa only [AddMonoidHom.comp_apply,
        actualCuspVertexEdgeOverlapFirstLeg_highLegClass, map_zero] using hx
  · rintro ⟨hlow, hhigh⟩
    apply AddMonoidHom.ext
    intro z
    rw [actualCuspVertexEdgeOverlap_eq_lowLeg_add_highLeg (A := A) z]
    simp only [AddMonoidHom.comp_apply, map_add,
      actualCuspVertexEdgeOverlapFirstLeg_lowLegClass,
      actualCuspVertexEdgeOverlapFirstLeg_highLegClass]
    rw [hlow, hhigh]
    simp

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
