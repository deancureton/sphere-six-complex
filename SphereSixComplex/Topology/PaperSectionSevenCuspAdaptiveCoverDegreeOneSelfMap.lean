module

public import SphereSixComplex.Topology.MayerVietorisWangDegreeOneCoverComparison
public import SphereSixComplex.Topology.PaperSectionSevenCuspHeightLoopCrossingProof

/-!
# A degree-one self-map reduction for the adaptive cusp cover

The corrected ordering of the height-preimage cover is order four followed by order three.
This file isolates the exact self-map and oriented-overlap datum that would identify that cover
with a pullback of the standard mapping-torus vertex--edge cover.  It also constructs the two
scalar height-to-phase charts underlying such a self-map.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.MappingTorusDegreeOneCoverComparison
open SphereSixComplex.Topology.CanonicalProductWangBoundaryNaturality

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-! ## Scalar phase charts -/

/-- The lower-half standard mapping-torus phase determined by an affine height. -/
public noncomputable def heightToLowerPhase : C(ℝ, unitInterval) where
  toFun h := ⟨max 0 (min (1 / 2) ((1 - h) / 2)), by
    constructor
    · exact le_max_left _ _
    · apply max_le
      · norm_num
      · exact (min_le_left _ _).trans (by norm_num)⟩
  continuous_toFun := by fun_prop

/-- The lower height phase stays in the lower semicircle. -/
public theorem heightToLowerPhase_le_half (h : ℝ) :
    (heightToLowerPhase h : ℝ) ≤ 1 / 2 := by
  change max 0 (min (1 / 2) ((1 - h) / 2)) ≤ 1 / 2
  apply max_le
  · norm_num
  · exact min_le_left _ _

/-- The lower phase lies in the standard vertex band exactly above the lower affine
threshold. -/
public theorem heightToLowerPhase_mem_vertexBand_iff (h : ℝ) :
    heightToLowerPhase h ∈ vertexBand ↔ (1 / 3 : ℝ) < h := by
  change max 0 (min (1 / 2) ((1 - h) / 2)) < 1 / 3 ∨
      2 / 3 < max 0 (min (1 / 2) ((1 - h) / 2)) ↔ _
  constructor
  · rintro (hlt | hgt)
    · rw [max_lt_iff, min_lt_iff] at hlt
      rcases hlt.2 with hfalse | hraw
      · norm_num at hfalse
      · linarith
    · have hupper : max 0 (min (1 / 2) ((1 - h) / 2)) ≤ 1 / 2 := by
        apply max_le
        · norm_num
        · exact min_le_left _ _
      linarith
  · intro hh
    left
    rw [max_lt_iff, min_lt_iff]
    exact ⟨by norm_num, Or.inr (by linarith)⟩

/-- The lower phase lies in the standard edge band exactly below the upper affine
threshold. -/
public theorem heightToLowerPhase_mem_edgeBand_iff (h : ℝ) :
    heightToLowerPhase h ∈ edgeBand ↔ h < (2 / 3 : ℝ) := by
  change 1 / 6 < max 0 (min (1 / 2) ((1 - h) / 2)) ∧
      max 0 (min (1 / 2) ((1 - h) / 2)) < 5 / 6 ↔ _
  constructor
  · rintro ⟨hlow, -⟩
    rw [lt_max_iff] at hlow
    rcases hlow with hfalse | hmin
    · norm_num at hfalse
    · rw [lt_min_iff] at hmin
      linarith [hmin.2]
  · intro hh
    constructor
    · rw [lt_max_iff, lt_min_iff]
      exact Or.inr ⟨by norm_num, by linarith⟩
    · have hupper : max 0 (min (1 / 2) ((1 - h) / 2)) ≤ 1 / 2 := by
        apply max_le
        · norm_num
        · exact min_le_left _ _
      linarith

/-- The reflected upper-half phase chart. -/
public noncomputable def heightToUpperPhase : C(ℝ, unitInterval) where
  toFun h := ⟨1 - heightToLowerPhase h, by
    have hmem := (heightToLowerPhase h).2
    constructor
    · linarith [hmem.2]
    · linarith [hmem.1]⟩
  continuous_toFun := by fun_prop

/-- The upper phase has the same vertex-band height criterion as the lower phase. -/
public theorem heightToUpperPhase_mem_vertexBand_iff (h : ℝ) :
    heightToUpperPhase h ∈ vertexBand ↔ (1 / 3 : ℝ) < h := by
  change 1 - (heightToLowerPhase h : ℝ) < 1 / 3 ∨
      2 / 3 < 1 - (heightToLowerPhase h : ℝ) ↔ _
  have hhalf := heightToLowerPhase_le_half h
  constructor
  · intro hvertex
    apply (heightToLowerPhase_mem_vertexBand_iff h).1
    left
    rcases hvertex with hfalse | hlower
    · linarith
    · linarith
  · intro hh
    right
    have hvertex := (heightToLowerPhase_mem_vertexBand_iff h).2 hh
    rcases hvertex with hlower | hfalse
    · linarith
    · linarith

/-- The upper phase has the same edge-band height criterion as the lower phase. -/
public theorem heightToUpperPhase_mem_edgeBand_iff (h : ℝ) :
    heightToUpperPhase h ∈ edgeBand ↔ h < (2 / 3 : ℝ) := by
  change 1 / 6 < 1 - (heightToLowerPhase h : ℝ) ∧
      1 - (heightToLowerPhase h : ℝ) < 5 / 6 ↔ _
  have hmem := (heightToLowerPhase h).2
  constructor
  · intro hedge
    apply (heightToLowerPhase_mem_edgeBand_iff h).1
    constructor
    · linarith [hedge.2]
    · linarith [hmem.1]
  · intro hh
    have hedge := (heightToLowerPhase_mem_edgeBand_iff h).2 hh
    constructor
    · linarith [heightToLowerPhase_le_half h]
    · linarith [hedge.1]

/-- The two scalar charts agree at every nonpositive height. -/
public theorem heightToLowerPhase_eq_heightToUpperPhase_of_nonpos {h : ℝ} (hh : h ≤ 0) :
    heightToLowerPhase h = heightToUpperPhase h := by
  apply Subtype.ext
  change max 0 (min (1 / 2) ((1 - h) / 2)) =
    1 - max 0 (min (1 / 2) ((1 - h) / 2))
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
  norm_num

/-- The lower and upper charts glue at the certified negative phase of the actual cusp loop. -/
public theorem actualCuspHeightPhaseCharts_agree_at_five_sixteenths
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    let m : unitInterval := ⟨5 / 16, by constructor <;> norm_num⟩
    heightToLowerPhase (actualCuspCylinderHeightLoop R y m) =
      heightToUpperPhase (actualCuspCylinderHeightLoop R y m) := by
  let m : unitInterval := ⟨5 / 16, by constructor <;> norm_num⟩
  apply heightToLowerPhase_eq_heightToUpperPhase_of_nonpos
  exact (actualCuspCylinderHeightLoop_five_sixteenths_neg R y).le

/-- The lower chart reads the order-four member of the genuine cusp cover as the standard
vertex member on every mapping-torus cylinder. -/
public theorem heightToLowerPhase_mem_vertexBand_iff_orderFourOpen
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) (t : unitInterval) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    heightToLowerPhase (actualCuspCylinderHeightLoop R y t) ∈ vertexBand ↔
      G.totalHomotopyEquiv.invFun
          (circleMappingTorusCylinderProjection G.clutching (t, y)) ∈
        R.twoDiscCover.cuspOrderFourOpen := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let q : A.openEmbeddingStarData.collarSource 0 := G.totalHomotopyEquiv.invFun
    (circleMappingTorusCylinderProjection G.clutching (t, y))
  rw [heightToLowerPhase_mem_vertexBand_iff]
  change (1 / 3 : ℝ) < actualCuspCylinderHeightLoop R y t ↔
    R.twoDiscCover.cuspToEllipticInteriorMap q ∈ R.twoDiscCover.orderFourSide
  rw [cuspToEllipticInteriorMap_mem_orderFourSide_iff_height]
  rfl

/-- The lower chart reads the order-three member of the genuine cusp cover as the standard
edge member on every mapping-torus cylinder. -/
public theorem heightToLowerPhase_mem_edgeBand_iff_orderThreeOpen
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) (t : unitInterval) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    heightToLowerPhase (actualCuspCylinderHeightLoop R y t) ∈ edgeBand ↔
      G.totalHomotopyEquiv.invFun
          (circleMappingTorusCylinderProjection G.clutching (t, y)) ∈
        R.twoDiscCover.cuspOrderThreeOpen := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let q : A.openEmbeddingStarData.collarSource 0 := G.totalHomotopyEquiv.invFun
    (circleMappingTorusCylinderProjection G.clutching (t, y))
  rw [heightToLowerPhase_mem_edgeBand_iff]
  change actualCuspCylinderHeightLoop R y t < (2 / 3 : ℝ) ↔
    R.twoDiscCover.cuspToEllipticInteriorMap q ∈ R.twoDiscCover.orderThreeSide
  rw [cuspToEllipticInteriorMap_mem_orderThreeSide_iff_height]
  rfl

/-! ## Exact self-map residual -/

/-- Exact data still needed to realize the adaptive height-preimage cover as the pullback of
the ordered standard vertex--edge cover by a degree-one self-map. -/
public structure ActualCuspAdaptiveCoverDegreeOneSelfMap
    (R : A.SectionSevenAffineRadialCompletionInput) where
  selfMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(CircleMappingTorus G.clutching, CircleMappingTorus G.clutching)
  homotopic_id :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    selfMap.Homotopic (ContinuousMap.id (CircleMappingTorus G.clutching))
  vertex_pullback :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (Opens.map (TopCat.ofHom selfMap)).obj (mappingTorusVertexOpen G.clutching) =
      actualCuspMappingTorusOrderFourOpen R
  edge_pullback :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (Opens.map (TopCat.ofHom selfMap)).obj (mappingTorusEdgeOpen G.clutching) =
      actualCuspMappingTorusOrderThreeOpen R

/-- Read the adaptive overlap through the low leg of the target vertex--edge overlap.  This
definition, rather than another hypothesis, fixes the Mayer--Vietoris orientation. -/
public noncomputable def ActualCuspAdaptiveCoverDegreeOneSelfMap.sourceRead
    {R : A.SectionSevenAffineRadialCompletionInput}
    (D : ActualCuspAdaptiveCoverDegreeOneSelfMap R) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1
        ((Opens.toTopCat (TopCat.of (CircleMappingTorus G.clutching))).obj
          ((Opens.map (TopCat.ofHom D.selfMap)).obj (mappingTorusVertexOpen G.clutching) ⊓
            (Opens.map (TopCat.ofHom D.selfMap)).obj (mappingTorusEdgeOpen G.clutching))) →+
      IntegralSingularHomology 1 G.Fiber := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact
    (lowOverlapRead G.clutching 1).comp
      (SphereSixComplex.BinaryOpenCover.openIntersectionPullbackHomologyHom
        (TopCat.ofHom D.selfMap) (mappingTorusVertexOpen G.clutching)
        (mappingTorusEdgeOpen G.clutching) 1)

/-- Transport the oriented pullback-overlap reading along specified equalities of the two
ordered cover members. -/
public noncomputable def ActualCuspAdaptiveCoverDegreeOneSelfMap.sourceReadOfOpenEq
    {R : A.SectionSevenAffineRadialCompletionInput}
    (D : ActualCuspAdaptiveCoverDegreeOneSelfMap R)
    (U V : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      Opens (TopCat.of (CircleMappingTorus G.clutching)))
    (hU : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      U = (Opens.map (TopCat.ofHom D.selfMap)).obj (mappingTorusVertexOpen G.clutching))
    (hV : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      V = (Opens.map (TopCat.ofHom D.selfMap)).obj (mappingTorusEdgeOpen G.clutching)) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1
        ((Opens.toTopCat (TopCat.of (CircleMappingTorus G.clutching))).obj (U ⊓ V)) →+
      IntegralSingularHomology 1 G.Fiber := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [hU, hV]
  exact D.sourceRead

/-- The same oriented reading, transported to the literal order-four/order-three intersection
of the genuine height-preimage cover. -/
public noncomputable def ActualCuspAdaptiveCoverDegreeOneSelfMap.actualSourceRead
    {R : A.SectionSevenAffineRadialCompletionInput}
    (D : ActualCuspAdaptiveCoverDegreeOneSelfMap R) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1
        ((Opens.toTopCat (TopCat.of (CircleMappingTorus G.clutching))).obj
          (actualCuspMappingTorusOrderFourOpen R ⊓
            actualCuspMappingTorusOrderThreeOpen R)) →+
      IntegralSingularHomology 1 G.Fiber := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact D.sourceReadOfOpenEq
    (actualCuspMappingTorusOrderFourOpen R) (actualCuspMappingTorusOrderThreeOpen R)
    D.vertex_pullback.symm D.edge_pullback.symm

/-- The exact adaptive self-map residual supplies the degree-one pullback-cover comparison. -/
public theorem ActualCuspAdaptiveCoverDegreeOneSelfMap.toPullbackCoverComparison
    (R : A.SectionSevenAffineRadialCompletionInput)
    (D : ActualCuspAdaptiveCoverDegreeOneSelfMap R) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    SphereSixComplex.BinaryOpenCover.DegreeOnePullbackCoverComparison
      (TopCat.ofHom D.selfMap) (mappingTorusVertexOpen G.clutching)
      (mappingTorusEdgeOpen G.clutching) 1 D.sourceRead (lowOverlapRead G.clutching 1) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact SphereSixComplex.BinaryOpenCover.DegreeOnePullbackCoverComparison.of_homotopic_id
    D.selfMap D.homotopic_id (mappingTorusVertexOpen G.clutching)
    (mappingTorusEdgeOpen G.clutching) 1 D.sourceRead (lowOverlapRead G.clutching 1)
    rfl

/-- Consequently, the oriented boundary of the adaptive pullback cover is the canonical Wang
boundary. -/
public theorem ActualCuspAdaptiveCoverDegreeOneSelfMap.boundary_eq_wang
    (R : A.SectionSevenAffineRadialCompletionInput)
    (D : ActualCuspAdaptiveCoverDegreeOneSelfMap R) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    D.sourceRead.comp
        ((SphereSixComplex.BinaryOpenCover.openCoverHomologyComparisonOfCover
          (SphereSixComplex.BinaryOpenCover.pullback_open_cover
            (TopCat.ofHom D.selfMap) (mappingTorusVertexOpen G.clutching)
            (mappingTorusEdgeOpen G.clutching) (mappingTorusOpenCover G.clutching))).boundaryHom
              1) =
      (circleMappingTorusWangPresentationOfCover G.clutching 1).boundary := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact degreeOnePullbackCover_boundary_eq_wang G.clutching (TopCat.ofHom D.selfMap) 1
    D.sourceRead D.toPullbackCoverComparison

private theorem adaptive_boundary_eq_wang_of_open_eq_aux
    (R : A.SectionSevenAffineRadialCompletionInput)
    (D : ActualCuspAdaptiveCoverDegreeOneSelfMap R)
    (U V : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      Opens (TopCat.of (CircleMappingTorus G.clutching)))
    (hU : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      U = (Opens.map (TopCat.ofHom D.selfMap)).obj (mappingTorusVertexOpen G.clutching))
    (hV : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      V = (Opens.map (TopCat.ofHom D.selfMap)).obj (mappingTorusEdgeOpen G.clutching))
    (hcover : U ⊔ V = ⊤) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (D.sourceReadOfOpenEq U V hU hV).comp
        ((SphereSixComplex.BinaryOpenCover.openCoverHomologyComparisonOfCover hcover).boundaryHom
          1) =
      (circleMappingTorusWangPresentationOfCover G.clutching 1).boundary := by
  subst U
  subst V
  exact D.boundary_eq_wang

/-- In the literal adaptive-cover interface, the oriented order-four/order-three
Mayer--Vietoris boundary is the canonical Wang boundary. -/
public theorem ActualCuspAdaptiveCoverDegreeOneSelfMap.actual_boundary_eq_wang
    (R : A.SectionSevenAffineRadialCompletionInput)
    (D : ActualCuspAdaptiveCoverDegreeOneSelfMap R) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    D.actualSourceRead.comp
        ((actualCuspMappingTorusPulledBackSwappedHomologyComparison R).boundaryHom 1) =
      (circleMappingTorusWangPresentationOfCover G.clutching 1).boundary := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  simpa only [ActualCuspAdaptiveCoverDegreeOneSelfMap.actualSourceRead,
    actualCuspMappingTorusPulledBackSwappedHomologyComparison] using
    adaptive_boundary_eq_wang_of_open_eq_aux R D
    (actualCuspMappingTorusOrderFourOpen R) (actualCuspMappingTorusOrderThreeOpen R)
    D.vertex_pullback.symm D.edge_pullback.symm
    (actualCuspMappingTorusPulledBackSwappedOpenCover R)

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
