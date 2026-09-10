module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspSignedCoverRefinementGeometryReduction

/-!
# Exact analytic residual for the signed cusp-cover height bounds

The affine height of an arbitrary cusp-collar point is the real part of the reciprocal of the
normalized modular cusp product.  Thus the two signed-cover height bounds reduce exactly to two
sector inequalities for that explicit analytic expression.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace

namespace SphereSixComplex.Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open SphereSixComplex
open SphereSixComplex.Geometry.CuspPeriodExpansion

variable {A : PaperAnalyticData}

namespace EllipticTwoDiscCoverData

/-- A selected additive cusp-cover representative of a cusp-collar point. -/
public noncomputable def actualCuspAdditiveLift
    (q : PuncturedLocalCuspQuotient A.starCuspWitness) :
    additiveCuspRadiusCover A.starCuspWitness.localWitness.radius :=
  Classical.choose
    ((additiveCuspBoundaryProjection_isQuotientCoveringMap A.starCuspWitness).surjective q)

/-- The selected additive representative projects to the original collar point. -/
public theorem additiveCuspBoundaryProjection_actualCuspAdditiveLift
    (q : PuncturedLocalCuspQuotient A.starCuspWitness) :
    additiveCuspBoundaryProjection A.starCuspWitness (actualCuspAdditiveLift q) = q :=
  Classical.choose_spec
    ((additiveCuspBoundaryProjection_isQuotientCoveringMap A.starCuspWitness).surjective q)

/-- On an additive cusp lift, the affine height is the real part of the normalized modular
coordinate. -/
public theorem sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_additivePoint
    (D : A.EllipticTwoDiscCoverData)
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.ellipticCentralHeight
        ⟨D.cuspToEllipticInteriorMap
            (additiveCuspBoundaryProjection A.starCuspWitness p),
          D.cuspToEllipticInteriorMap_mem_centralImage _⟩ =
      (A.modular.sourceCoordinate.coordinate (A.cuspCoordinate.lift p.1.2)).re := by
  change (A.ellipticCentralCoordinate _).1.re = _
  rw [D.sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_additivePoint_fst]

/-- The same height written using the exact reciprocal cusp factorization. -/
public theorem sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_additivePoint_eq
    (D : A.EllipticTwoDiscCoverData)
    (p : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.ellipticCentralHeight
        ⟨D.cuspToEllipticInteriorMap
            (additiveCuspBoundaryProjection A.starCuspWitness p),
          D.cuspToEllipticInteriorMap_mem_centralImage _⟩ =
      ((cuspQ p.1.2 * A.actualNormalizedModularJUniformization.cusp.cuspUnit
        (cuspQ p.1.2))⁻¹).re := by
  rw [D.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_additivePoint]
  have hs : p.1.2 ∈ cuspHalfPlane A.cuspCoordinate.height :=
    additiveCuspRadiusCover_halfPlane A.starCuspWitness.localWitness.radius_le p
  have h := congrArg Inv.inv
    (A.actualPuncturedCuspWitness_reciprocal_factorization p.1.2 hs p.2)
  simpa only [inv_inv] using congrArg Complex.re h

/-- The exact reciprocal-product formula after passing from the radial mapping torus to the
actual cusp collar. -/
public theorem sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus
    (D : A.EllipticTwoDiscCoverData)
    (z : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      CircleMappingTorus G.clutching) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    A.ellipticCentralHeight
        ⟨D.cuspToEllipticInteriorMap (G.totalHomotopyEquiv.invFun z),
          D.cuspToEllipticInteriorMap_mem_centralImage _⟩ =
      let p := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
      ((cuspQ p.1.2 * A.actualNormalizedModularJUniformization.cusp.cuspUnit
        (cuspQ p.1.2))⁻¹).re := by
  dsimp only
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let q := G.totalHomotopyEquiv.invFun z
  let p := actualCuspAdditiveLift q
  have hp := additiveCuspBoundaryProjection_actualCuspAdditiveLift q
  change A.ellipticCentralHeight
      ⟨D.cuspToEllipticInteriorMap q,
        D.cuspToEllipticInteriorMap_mem_centralImage _⟩ =
    ((cuspQ p.1.2 * A.actualNormalizedModularJUniformization.cusp.cuspUnit
      (cuspQ p.1.2))⁻¹).re
  have hmap := congrArg D.cuspToEllipticInteriorMap hp
  have hpoint :
      (⟨D.cuspToEllipticInteriorMap
          (additiveCuspBoundaryProjection A.starCuspWitness p),
        D.cuspToEllipticInteriorMap_mem_centralImage _⟩ :
          A.ellipticCentralImage) =
        ⟨D.cuspToEllipticInteriorMap q,
          D.cuspToEllipticInteriorMap_mem_centralImage _⟩ :=
    Subtype.ext hmap
  calc
    _ = A.ellipticCentralHeight
        ⟨D.cuspToEllipticInteriorMap
            (additiveCuspBoundaryProjection A.starCuspWitness p),
          D.cuspToEllipticInteriorMap_mem_centralImage _⟩ :=
      congrArg A.ellipticCentralHeight hpoint.symm
    _ = _ :=
      D.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_additivePoint_eq p

/-- On the actual affine allocation, a cusp-collar point belongs to the order-three side exactly
when its central height is below `2/3`.  The filling-image alternative cannot add points above
that height because of the proved central separation. -/
public theorem cuspToEllipticInteriorMap_mem_orderThreeSide_iff_height
    (R : A.AffineRadialCompletionInput)
    (q : A.openEmbeddingStarData.collarSource 0) :
    R.twoDiscCover.cuspToEllipticInteriorMap q ∈ R.twoDiscCover.orderThreeSide ↔
      A.ellipticCentralHeight
        ⟨R.twoDiscCover.cuspToEllipticInteriorMap q,
          R.twoDiscCover.cuspToEllipticInteriorMap_mem_centralImage q⟩ < 2 / 3 := by
  let x := R.twoDiscCover.cuspToEllipticInteriorMap q
  have hxcentral : x ∈ A.ellipticCentralImage :=
    R.twoDiscCover.cuspToEllipticInteriorMap_mem_centralImage q
  change x ∈ A.actualAffineHeightSplit.allocation.orderThreeSide ↔
    A.ellipticCentralHeight ⟨x, hxcentral⟩ < (2 : ℝ) / 3
  constructor
  · rintro (hxfill | hxlower)
    · by_contra hheight
      have hge : (2 : ℝ) / 3 ≤
          A.ellipticCentralHeight ⟨x, hxcentral⟩ :=
        le_of_not_gt hheight
      have hxupper : x ∈ centralHeightUpperRegion
          A.ellipticCentralHeight (1 / 3 : ℝ) :=
        ⟨⟨x, hxcentral⟩, (by linarith : (1 : ℝ) / 3 <
          A.ellipticCentralHeight ⟨x, hxcentral⟩), rfl⟩
      exact (Set.disjoint_left.mp
        A.affineCentralSeparation.orderThreeFilling_disjoint_upper
          hxfill hxupper).elim
    · rcases hxlower with ⟨y, hy, hyx⟩
      have hxy : y = (⟨x, hxcentral⟩ : A.ellipticCentralImage) :=
        Subtype.ext hyx
      change A.ellipticCentralHeight y < (2 : ℝ) / 3 at hy
      simpa [hxy] using hy
  · intro hheight
    exact Or.inr ⟨⟨x, hxcentral⟩, hheight, rfl⟩

/-- On the actual affine allocation, a cusp-collar point belongs to the order-four side exactly
when its central height is above `1/3`. -/
public theorem cuspToEllipticInteriorMap_mem_orderFourSide_iff_height
    (R : A.AffineRadialCompletionInput)
    (q : A.openEmbeddingStarData.collarSource 0) :
    R.twoDiscCover.cuspToEllipticInteriorMap q ∈ R.twoDiscCover.orderFourSide ↔
      1 / 3 < A.ellipticCentralHeight
        ⟨R.twoDiscCover.cuspToEllipticInteriorMap q,
          R.twoDiscCover.cuspToEllipticInteriorMap_mem_centralImage q⟩ := by
  let x := R.twoDiscCover.cuspToEllipticInteriorMap q
  have hxcentral : x ∈ A.ellipticCentralImage :=
    R.twoDiscCover.cuspToEllipticInteriorMap_mem_centralImage q
  change x ∈ A.actualAffineHeightSplit.allocation.orderFourSide ↔
    (1 : ℝ) / 3 < A.ellipticCentralHeight ⟨x, hxcentral⟩
  constructor
  · rintro (hxfill | hxupper)
    · by_contra hheight
      have hle : A.ellipticCentralHeight ⟨x, hxcentral⟩ ≤ 1 / 3 :=
        le_of_not_gt hheight
      have hxlower : x ∈ centralHeightLowerRegion
          A.ellipticCentralHeight (2 / 3 : ℝ) :=
        ⟨⟨x, hxcentral⟩, (by linarith :
          A.ellipticCentralHeight ⟨x, hxcentral⟩ < (2 : ℝ) / 3), rfl⟩
      exact (Set.disjoint_left.mp
        A.affineCentralSeparation.orderFourFilling_disjoint_lower
          hxfill hxlower).elim
    · rcases hxupper with ⟨y, hy, hyx⟩
      have hxy : y = (⟨x, hxcentral⟩ : A.ellipticCentralImage) :=
        Subtype.ext hyx
      change (1 : ℝ) / 3 < A.ellipticCentralHeight y at hy
      simpa [hxy] using hy
  · intro hheight
    exact Or.inr ⟨⟨x, hxcentral⟩, hheight, rfl⟩

/-- The proposed vertex inclusion is equivalent, not merely implied by, its height bound. -/
public theorem actualCuspVertexOrderThreePointwiseMembership_iff_heightBound
    (R : A.AffineRadialCompletionInput) :
    ActualCuspVertexOrderThreePointwiseMembership R ↔
      ActualCuspVertexOrderThreeHeightBound R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  constructor
  · intro h z hz
    exact (cuspToEllipticInteriorMap_mem_orderThreeSide_iff_height R _).1 (h z hz)
  · exact actualCuspVertexOrderThreePointwiseMembership_of_heightBound R

/-- The proposed edge inclusion is equivalent, not merely implied by, its height bound. -/
public theorem actualCuspEdgeOrderFourPointwiseMembership_iff_heightBound
    (R : A.AffineRadialCompletionInput) :
    ActualCuspEdgeOrderFourPointwiseMembership R ↔
      ActualCuspEdgeOrderFourHeightBound R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  constructor
  · intro h z hz
    exact (cuspToEllipticInteriorMap_mem_orderFourSide_iff_height R _).1 (h z hz)
  · exact actualCuspEdgeOrderFourPointwiseMembership_of_heightBound R

/-- Consequently, the proposed oriented refinement exists exactly when both reciprocal-product
sector inequalities hold; there is no weaker set-theoretic route hidden in the filling sides. -/
public theorem actualCuspOrientedCoverRefinement_iff_heightBounds
    (R : A.AffineRadialCompletionInput) :
    ActualCuspOrientedCoverRefinement R ↔
      ActualCuspVertexOrderThreeHeightBound R ∧
        ActualCuspEdgeOrderFourHeightBound R := by
  rw [actualCuspOrientedCoverRefinement_iff_pointwiseMembership,
    actualCuspVertexOrderThreePointwiseMembership_iff_heightBound,
    actualCuspEdgeOrderFourPointwiseMembership_iff_heightBound]

/-- The remaining upper-sector inequality, stated directly in the exact normalized cusp
factorization and independently of the affine radial-completion package. -/
public def ActualCuspVertexReciprocalProductBound (A : PaperAnalyticData) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  ∀ z : CircleMappingTorus G.clutching,
    z ∈ vertexPiece (fun _ : Unit ↦ G.clutching) →
      let p := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
      ((cuspQ p.1.2 * A.actualNormalizedModularJUniformization.cusp.cuspUnit
        (cuspQ p.1.2))⁻¹).re < 2 / 3

/-- The remaining lower-sector inequality, stated directly in the exact normalized cusp
factorization and independently of the affine radial-completion package. -/
public def ActualCuspEdgeReciprocalProductBound (A : PaperAnalyticData) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  ∀ z : CircleMappingTorus G.clutching,
    z ∈ edgePiece (fun _ : Unit ↦ G.clutching) →
      let p := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
      1 / 3 < ((cuspQ p.1.2 * A.actualNormalizedModularJUniformization.cusp.cuspUnit
        (cuspQ p.1.2))⁻¹).re

/-- The vertex height bound is exactly the upper-sector inequality for the normalized modular
cusp product. -/
public theorem actualCuspVertexOrderThreeHeightBound_iff_reciprocalProductBound
    (R : A.AffineRadialCompletionInput) :
    ActualCuspVertexOrderThreeHeightBound R ↔
      ActualCuspVertexReciprocalProductBound A := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  constructor
  · intro h z hz
    have heq :=
      R.twoDiscCover.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus z
    simpa only [heq] using h z hz
  · intro h z hz
    have heq :=
      R.twoDiscCover.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus z
    simpa only [heq] using h z hz

/-- The edge height bound is exactly the lower-sector inequality for the normalized modular
cusp product. -/
public theorem actualCuspEdgeOrderFourHeightBound_iff_reciprocalProductBound
    (R : A.AffineRadialCompletionInput) :
    ActualCuspEdgeOrderFourHeightBound R ↔
      ActualCuspEdgeReciprocalProductBound A := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  constructor
  · intro h z hz
    have heq :=
      R.twoDiscCover.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus z
    simpa only [heq] using h z hz
  · intro h z hz
    have heq :=
      R.twoDiscCover.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus z
    simpa only [heq] using h z hz

/-- Exact final form of the residual: the proposed oriented refinement is equivalent to the two
explicit sector inequalities for the reciprocal normalized cusp product. -/
public theorem actualCuspOrientedCoverRefinement_iff_reciprocalProductBounds
    (R : A.AffineRadialCompletionInput) :
    ActualCuspOrientedCoverRefinement R ↔
      ActualCuspVertexReciprocalProductBound A ∧
        ActualCuspEdgeReciprocalProductBound A := by
  rw [actualCuspOrientedCoverRefinement_iff_heightBounds,
    actualCuspVertexOrderThreeHeightBound_iff_reciprocalProductBound,
    actualCuspEdgeOrderFourHeightBound_iff_reciprocalProductBound]

/-- Exact form of a counterexample to the proposed vertex inclusion. -/
public theorem not_actualCuspVertexOrderThreeHeightBound_iff_exists_counterexample
    (R : A.AffineRadialCompletionInput) :
    (¬ ActualCuspVertexOrderThreeHeightBound R) ↔
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      ∃ z : CircleMappingTorus G.clutching,
        z ∈ vertexPiece (fun _ : Unit ↦ G.clutching) ∧
          let p := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
          2 / 3 ≤ ((cuspQ p.1.2 *
            A.actualNormalizedModularJUniformization.cusp.cuspUnit (cuspQ p.1.2))⁻¹).re := by
  rw [actualCuspVertexOrderThreeHeightBound_iff_reciprocalProductBound]
  simp only [ActualCuspVertexReciprocalProductBound]
  push Not
  rfl

/-- Exact form of a counterexample to the proposed edge inclusion. -/
public theorem not_actualCuspEdgeOrderFourHeightBound_iff_exists_counterexample
    (R : A.AffineRadialCompletionInput) :
    (¬ ActualCuspEdgeOrderFourHeightBound R) ↔
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      ∃ z : CircleMappingTorus G.clutching,
        z ∈ edgePiece (fun _ : Unit ↦ G.clutching) ∧
          let p := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
          ((cuspQ p.1.2 *
            A.actualNormalizedModularJUniformization.cusp.cuspUnit (cuspQ p.1.2))⁻¹).re ≤ 1 / 3 := by
  rw [actualCuspEdgeOrderFourHeightBound_iff_reciprocalProductBound]
  simp only [ActualCuspEdgeReciprocalProductBound]
  push Not
  rfl

end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end
