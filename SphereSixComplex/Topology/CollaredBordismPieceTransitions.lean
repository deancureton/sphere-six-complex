module

public import SphereSixComplex.Topology.CollaredBordismOpenPresentation
public import SphereSixComplex.Topology.SmoothOpenGluingCompatibility

/-!
# Smooth changes of pieces in the canonical collared-bordism gluing

The three-piece presentation of a glued collared bordism uses the two original carriers away
from the glued boundary and an explicit signed bicollar.  This file verifies that every ordered
change of pieces is smooth for the product model with corners.
-/

@[expose] public section

noncomputable section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SphereSixComplex
namespace SmoothCollaredBordism
namespace QuotientGluing

universe uE uH uM

variable {E : Type uE} {H : Type uH} {M₀ M₁ M₂ : Type uM}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M₀] [T2Space M₀] [SecondCountableTopology M₀]
  [ChartedSpace H M₀] [IsManifold I ∞ M₀] [CompactSpace M₀]
  [BoundarylessManifold I M₀]
  [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
  [ChartedSpace H M₁] [IsManifold I ∞ M₁] [CompactSpace M₁]
  [BoundarylessManifold I M₁]
  [TopologicalSpace M₂] [T2Space M₂] [SecondCountableTopology M₂]
  [ChartedSpace H M₂] [IsManifold I ∞ M₂] [CompactSpace M₂]
  [BoundarylessManifold I M₂]

variable
  (B₀₁ : SmoothCollaredBordism.{uE, uH, uM} I M₀ M₁)
  (B₁₂ : SmoothCollaredBordism.{uE, uH, uM} I M₁ M₂)

section GenericOpenEmbeddingPresentation

variable {J X : Type uM} [TopologicalSpace X]
  (U : J → Type uM) [∀ i, TopologicalSpace (U i)]
  (e : ∀ i, U i → X) (he : ∀ i, IsOpenEmbedding (e i))
  [∀ i, ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) (U i)]

private noncomputable local instance openEmbeddingGlueDataPieceChartedSpace (i : J) :
    ChartedSpace (ModelProd H (EuclideanHalfSpace 1))
      ((OpenEmbeddingGluing.glueData U e he).U i) := by
  change ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) (U i)
  infer_instance

private theorem openEmbeddingPieceTransition_source (p q : Sigma fun i ↦ U i) :
    (openGluingPieceTransition (OpenEmbeddingGluing.glueData U e he) p q).source =
      Set.range ((OpenEmbeddingGluing.glueData U e he).f p.1 q.1) := by
  exact openGluingPieceTransition_source
    (OpenEmbeddingGluing.glueData U e he) p q

/-- For a gluing presented by open embeddings, smoothness of its concrete overlap maps implies
smoothness of the corresponding canonical partial changes of pieces. -/
private theorem contMDiffOn_pieceTransition_of_contMDiff_transition
    (htrans : ∀ i j,
      ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
        (OpenEmbeddingGluing.transition U e he i j))
    (p q : Sigma fun i ↦ U i) :
    ContMDiffOn (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (openGluingPieceTransition (OpenEmbeddingGluing.glueData U e he) p q)
      (openGluingPieceTransition (OpenEmbeddingGluing.glueData U e he) p q).source := by
  rw [openEmbeddingPieceTransition_source]
  rintro x ⟨z, rfl⟩
  have hsmooth : ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (fun z : OpenEmbeddingGluing.overlap U e he p.1 q.1 ↦
        ((OpenEmbeddingGluing.transition U e he p.1 q.1 z :
          OpenEmbeddingGluing.overlap U e he q.1 p.1) : U q.1)) :=
    contMDiff_subtype_val.comp (htrans p.1 q.1)
  have hrestricted : ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (fun z : OpenEmbeddingGluing.overlap U e he p.1 q.1 ↦
        openGluingPieceTransition (OpenEmbeddingGluing.glueData U e he) p q z.1) := by
    apply hsmooth.congr
    intro z
    exact openGluingPieceTransition_apply_f
      (OpenEmbeddingGluing.glueData U e he) p q z
  exact (contMDiffAt_subtype_iff.mp (hrestricted z)).contMDiffWithinAt

end GenericOpenEmbeddingPresentation

/-- The affine change from a left collar coordinate to the signed seam coordinate is smooth. -/
private theorem contMDiff_seamFromLeftCollarSource :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (seamFromLeftCollarSource : CollarSource M₁ → M₁ × OpenCollarParameter) := by
  apply contMDiff_fst.prodMk
  apply (ContMDiff.subtypeVal_comp_iff collarInterior _).mp
  apply contMDiff_iff_comp_subtypeVal_Icc.mpr
  constructor
  · apply (continuous_subtype_val.comp
        (continuous_snd.comp continuous_seamFromLeftCollarSource)).congr
    intro p
    apply Subtype.ext
    rfl
  · have h : ContDiff ℝ ∞ (fun x : ℝ ↦ (1 - x) / 2) := by fun_prop
    exact h.comp_contMDiff
      (contMDiff_subtypeVal_Icc.comp
        (contMDiff_subtype_val.comp contMDiff_snd))

/-- The affine change from a right collar coordinate to the signed seam coordinate is smooth. -/
private theorem contMDiff_seamFromRightCollarSource :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (seamFromRightCollarSource : CollarSource M₁ → M₁ × OpenCollarParameter) := by
  apply contMDiff_fst.prodMk
  apply (ContMDiff.subtypeVal_comp_iff collarInterior _).mp
  apply contMDiff_iff_comp_subtypeVal_Icc.mpr
  constructor
  · apply (continuous_subtype_val.comp
        (continuous_snd.comp continuous_seamFromRightCollarSource)).congr
    intro p
    apply Subtype.ext
    rfl
  · have h : ContDiff ℝ ∞ (fun x : ℝ ↦ (x + 1) / 2) := by fun_prop
    exact h.comp_contMDiff
      (contMDiff_subtypeVal_Icc.comp
        (contMDiff_subtype_val.comp contMDiff_snd))

/-- Each member of the canonical open presentation carries its inherited product-model smooth
structure. -/
public noncomputable instance instOpenPieceChartedSpace (i : OpenPieceIndex) :
    ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) (OpenPiece B₀₁ B₁₂ i) := by
  cases i <;> infer_instance

/-- Every member of the canonical open presentation is a smooth manifold with corners. -/
public instance instOpenPieceIsManifold (i : OpenPieceIndex) :
    IsManifold (I.prod (𝓡∂ 1)) ∞ (OpenPiece B₀₁ B₁₂ i) := by
  cases i <;> infer_instance

/-- The same charted-space family, exposed through the `U` field of the gluing data. -/
public noncomputable instance instOpenPresentationPieceChartedSpace
    (i : (openPresentation B₀₁ B₁₂).J) :
    ChartedSpace (ModelProd H (EuclideanHalfSpace 1))
      ((openPresentation B₀₁ B₁₂).U i) := by
  change OpenPieceIndex at i
  change ChartedSpace (ModelProd H (EuclideanHalfSpace 1))
    (OpenPiece B₀₁ B₁₂ i)
  exact instOpenPieceChartedSpace B₀₁ B₁₂ i

/-- The same manifold family, exposed through the `U` field of the gluing data. -/
public instance instOpenPresentationPieceIsManifold
    (i : (openPresentation B₀₁ B₁₂).J) :
    IsManifold (I.prod (𝓡∂ 1)) ∞
      ((openPresentation B₀₁ B₁₂).U i) := by
  change OpenPieceIndex at i
  exact instOpenPieceIsManifold B₀₁ B₁₂ i

/-- A self-overlap has the identity as its change of pieces. -/
private theorem contMDiff_openPieceTransition_refl (i : OpenPieceIndex) :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (OpenEmbeddingGluing.transition
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂) i i) := by
  apply (ContMDiff.subtypeVal_comp_iff
    (OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂) i i) _).mp
  apply contMDiff_subtype_val.congr
  intro z
  apply (openPieceMap_isOpenEmbedding B₀₁ B₁₂ i).injective
  exact OpenEmbeddingGluing.map_transition
    (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
    (openPieceMap_isOpenEmbedding B₀₁ B₁₂) i i z

/-- A point in the left--seam overlap lies in the outgoing collar target. -/
private theorem leftSeamOverlap_mem_collarTarget
    (z : OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
    (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.left OpenPieceIndex.seam) :
    z.1.1 ∈ B₀₁.outgoing.chart.target := by
  have hzrange := z.property
  change toGlueLeft B₀₁ B₁₂ z.1.1 ∈
    Set.range (signedSeamMap B₀₁ B₁₂) at hzrange
  rcases hzrange with ⟨s, hs⟩
  have hz : toGlueLeft B₀₁ B₁₂ z.1.1 ∈
      signedSeamMap B₀₁ B₁₂ '' Set.univ :=
    ⟨s, Set.mem_univ s, hs⟩
  obtain ⟨p, hp, -⟩ :=
    (toGlueLeft_mem_image_signedSeamMap_iff B₀₁ B₁₂ Set.univ z.1.1).1 hz
  rw [← hp]
  exact (B₀₁.outgoing.chart.toDiffeomorph p).property

/-- Read a left--seam overlap point in outgoing collar coordinates. -/
private def leftSeamOverlapToCollarTarget
    (z : OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.left OpenPieceIndex.seam) :
    B₀₁.outgoing.chart.target :=
  ⟨z.1.1, leftSeamOverlap_mem_collarTarget B₀₁ B₁₂ z⟩

private theorem contMDiff_leftSeamOverlapToCollarTarget :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (leftSeamOverlapToCollarTarget B₀₁ B₁₂) := by
  apply (ContMDiff.subtypeVal_comp_iff B₀₁.outgoing.chart.target _).mp
  have hval : ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (fun z : OpenEmbeddingGluing.overlap
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
        OpenPieceIndex.left OpenPieceIndex.seam ↦ z.1.1) :=
    (contMDiff_subtype_val (I := I.prod (𝓡∂ 1))
      (U := leftAwaySource B₀₁)).comp
        (contMDiff_subtype_val (I := I.prod (𝓡∂ 1)))
  simpa only [Function.comp_def, leftSeamOverlapToCollarTarget] using hval

/-- The left-to-seam change of pieces is the inverse outgoing collar chart followed by the
reversed affine half-cylinder coordinate. -/
private theorem contMDiff_openPieceTransition_left_seam :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (OpenEmbeddingGluing.transition
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
        OpenPieceIndex.left OpenPieceIndex.seam) := by
  apply (ContMDiff.subtypeVal_comp_iff
    (OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.seam OpenPieceIndex.left) _).mp
  apply (contMDiff_seamFromLeftCollarSource (I := I)).comp
      (B₀₁.outgoing.chart.toDiffeomorph.contMDiff_invFun.comp
        (contMDiff_leftSeamOverlapToCollarTarget B₀₁ B₁₂)) |>.congr
  intro z
  apply signedSeamMap_injective B₀₁ B₁₂
  have hmap : signedSeamMap B₀₁ B₁₂
        (OpenEmbeddingGluing.transition
          (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
          (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
          OpenPieceIndex.left OpenPieceIndex.seam z) =
      toGlueLeft B₀₁ B₁₂ z.1.1 :=
    OpenEmbeddingGluing.map_transition
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.left OpenPieceIndex.seam z
  have hexp : signedSeamMap B₀₁ B₁₂
        (seamFromLeftCollarSource
          (B₀₁.outgoing.chart.toDiffeomorph.symm
            (leftSeamOverlapToCollarTarget B₀₁ B₁₂ z))) =
      toGlueLeft B₀₁ B₁₂ z.1.1 := by
    rw [signedSeamMap_fromLeftCollarSource]
    congr 1
    exact congrArg Subtype.val
      (B₀₁.outgoing.chart.toDiffeomorph.apply_symm_apply
        (leftSeamOverlapToCollarTarget B₀₁ B₁₂ z))
  exact hmap.trans hexp.symm

/-- A point in the right--seam overlap lies in the incoming collar target. -/
private theorem rightSeamOverlap_mem_collarTarget
    (z : OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.right OpenPieceIndex.seam) :
    z.1.1 ∈ B₁₂.incoming.chart.target := by
  have hzrange := z.property
  change toGlueRight B₀₁ B₁₂ z.1.1 ∈
    Set.range (signedSeamMap B₀₁ B₁₂) at hzrange
  rcases hzrange with ⟨s, hs⟩
  have hz : toGlueRight B₀₁ B₁₂ z.1.1 ∈
      signedSeamMap B₀₁ B₁₂ '' Set.univ :=
    ⟨s, Set.mem_univ s, hs⟩
  obtain ⟨p, hp, -⟩ :=
    (toGlueRight_mem_image_signedSeamMap_iff B₀₁ B₁₂ Set.univ z.1.1).1 hz
  rw [← hp]
  exact (B₁₂.incoming.chart.toDiffeomorph p).property

/-- Read a right--seam overlap point in incoming collar coordinates. -/
private def rightSeamOverlapToCollarTarget
    (z : OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.right OpenPieceIndex.seam) :
    B₁₂.incoming.chart.target :=
  ⟨z.1.1, rightSeamOverlap_mem_collarTarget B₀₁ B₁₂ z⟩

private theorem contMDiff_rightSeamOverlapToCollarTarget :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (rightSeamOverlapToCollarTarget B₀₁ B₁₂) := by
  apply (ContMDiff.subtypeVal_comp_iff B₁₂.incoming.chart.target _).mp
  have hval : ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (fun z : OpenEmbeddingGluing.overlap
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
        OpenPieceIndex.right OpenPieceIndex.seam ↦ z.1.1) :=
    (contMDiff_subtype_val (I := I.prod (𝓡∂ 1))
      (U := rightAwaySource B₁₂)).comp
        (contMDiff_subtype_val (I := I.prod (𝓡∂ 1)))
  simpa only [Function.comp_def, rightSeamOverlapToCollarTarget] using hval

/-- The right-to-seam change of pieces is the inverse incoming collar chart followed by the
right affine half-cylinder coordinate. -/
private theorem contMDiff_openPieceTransition_right_seam :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (OpenEmbeddingGluing.transition
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
        OpenPieceIndex.right OpenPieceIndex.seam) := by
  apply (ContMDiff.subtypeVal_comp_iff
    (OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.seam OpenPieceIndex.right) _).mp
  apply (contMDiff_seamFromRightCollarSource (I := I)).comp
      (B₁₂.incoming.chart.toDiffeomorph.contMDiff_invFun.comp
        (contMDiff_rightSeamOverlapToCollarTarget B₀₁ B₁₂)) |>.congr
  intro z
  apply signedSeamMap_injective B₀₁ B₁₂
  have hmap : signedSeamMap B₀₁ B₁₂
        (OpenEmbeddingGluing.transition
          (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
          (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
          OpenPieceIndex.right OpenPieceIndex.seam z) =
      toGlueRight B₀₁ B₁₂ z.1.1 :=
    OpenEmbeddingGluing.map_transition
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.right OpenPieceIndex.seam z
  have hexp : signedSeamMap B₀₁ B₁₂
        (seamFromRightCollarSource
          (B₁₂.incoming.chart.toDiffeomorph.symm
            (rightSeamOverlapToCollarTarget B₀₁ B₁₂ z))) =
      toGlueRight B₀₁ B₁₂ z.1.1 := by
    rw [signedSeamMap_fromRightCollarSource]
    congr 1
    exact congrArg Subtype.val
      (B₁₂.incoming.chart.toDiffeomorph.apply_symm_apply
        (rightSeamOverlapToCollarTarget B₀₁ B₁₂ z))
  exact hmap.trans hexp.symm

/-- The open collar interior lies in the half-open collar domain. -/
private theorem collarInterior_le_startNeighborhood :
    collarInterior ≤ collarStartNeighborhood := by
  intro t ht
  exact ht.2

/-- On the seam--left overlap, the signed coordinate lies strictly to the left of the
midpoint. -/
private theorem seamLeftOverlap_coordinate_lt
    (z : OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.seam OpenPieceIndex.left) :
    seamCoordinate z.1.2 < 1 / 2 := by
  have hzrange := z.property
  change signedSeamMap B₀₁ B₁₂ z.1 ∈
    Set.range (fun x : leftAwaySource B₀₁ ↦
      toGlueLeft B₀₁ B₁₂ x.1) at hzrange
  rcases hzrange with ⟨x, hx⟩
  have hzimage : toGlueLeft B₀₁ B₁₂ x.1 ∈
      signedSeamMap B₀₁ B₁₂ '' ({z.1} : Set (M₁ × OpenCollarParameter)) :=
    ⟨z.1, Set.mem_singleton z.1, hx.symm⟩
  obtain ⟨p, hpchart, hpz⟩ :=
    (toGlueLeft_mem_image_signedSeamMap_iff B₀₁ B₁₂ ({z.1} :
      Set (M₁ × OpenCollarParameter)) x.1).1 hzimage
  have hpz' : seamFromLeftCollarSource p = z.1 := by
    simpa only [Set.mem_singleton_iff] using hpz
  rw [← hpz', seamCoordinate_fromLeftCollarSource]
  have hnonneg : 0 ≤ ((p.2.1 : CollarParameter) : ℝ) := p.2.1.property.1
  have hle : (1 - ((p.2.1 : CollarParameter) : ℝ)) / 2 ≤ (1 / 2 : ℝ) := by
    linarith
  apply lt_of_le_of_ne hle
  intro heq
  have hrval : ((p.2.1 : CollarParameter) : ℝ) = 0 := by
    linarith
  have hr : p.2 = halfCollarStart := by
    apply Subtype.ext
    apply Subtype.ext
    exact hrval
  apply x.2
  refine ⟨p.1, ?_⟩
  rw [← hpchart]
  change B₀₁.outgoing.chart (p.1, halfCollarStart) =
    B₀₁.outgoing.chart p
  congr 1
  exact Prod.ext rfl hr.symm

/-- On the seam--right overlap, the signed coordinate lies strictly to the right of the
midpoint. -/
private theorem seamRightOverlap_coordinate_lt
    (z : OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.seam OpenPieceIndex.right) :
    1 / 2 < seamCoordinate z.1.2 := by
  have hzrange := z.property
  change signedSeamMap B₀₁ B₁₂ z.1 ∈
    Set.range (fun x : rightAwaySource B₁₂ ↦
      toGlueRight B₀₁ B₁₂ x.1) at hzrange
  rcases hzrange with ⟨x, hx⟩
  have hzimage : toGlueRight B₀₁ B₁₂ x.1 ∈
      signedSeamMap B₀₁ B₁₂ '' ({z.1} : Set (M₁ × OpenCollarParameter)) :=
    ⟨z.1, Set.mem_singleton z.1, hx.symm⟩
  obtain ⟨p, hpchart, hpz⟩ :=
    (toGlueRight_mem_image_signedSeamMap_iff B₀₁ B₁₂ ({z.1} :
      Set (M₁ × OpenCollarParameter)) x.1).1 hzimage
  have hpz' : seamFromRightCollarSource p = z.1 := by
    simpa only [Set.mem_singleton_iff] using hpz
  rw [← hpz', seamCoordinate_fromRightCollarSource]
  have hnonneg : 0 ≤ ((p.2.1 : CollarParameter) : ℝ) := p.2.1.property.1
  have hle : (1 / 2 : ℝ) ≤ (((p.2.1 : CollarParameter) : ℝ) + 1) / 2 := by
    linarith
  apply lt_of_le_of_ne hle
  intro heq
  have hrval : ((p.2.1 : CollarParameter) : ℝ) = 0 := by
    linarith
  have hr : p.2 = halfCollarStart := by
    apply Subtype.ext
    apply Subtype.ext
    exact hrval
  apply x.2
  refine ⟨p.1, ?_⟩
  rw [← hpchart]
  change B₁₂.incoming.chart (p.1, halfCollarStart) =
    B₁₂.incoming.chart p
  congr 1
  exact Prod.ext rfl hr.symm

/-- Regard a seam--left overlap point as a point of the strict left half-cylinder. -/
private def seamLeftOverlapToLeftHalf
    (z : OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.seam OpenPieceIndex.left) :
    M₁ × LeftOpenCollarParameter :=
  (z.1.1, ⟨z.1.2.1, ⟨z.1.2.2.1, seamLeftOverlap_coordinate_lt B₀₁ B₁₂ z⟩⟩)

private theorem contMDiff_seamLeftOverlapToLeftHalf :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (seamLeftOverlapToLeftHalf B₀₁ B₁₂) := by
  apply (contMDiff_fst.comp contMDiff_subtype_val).prodMk
  apply (ContMDiff.subtypeVal_comp_iff collarLeftOpenInterval _).mp
  have hval : ContMDiff (I.prod (𝓡∂ 1)) (𝓡∂ 1) ∞
      (fun z : OpenEmbeddingGluing.overlap
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
        OpenPieceIndex.seam OpenPieceIndex.left ↦ z.1.2.1) :=
    contMDiff_subtype_val.comp (contMDiff_snd.comp contMDiff_subtype_val)
  simpa only [Function.comp_def, seamLeftOverlapToLeftHalf] using hval

/-- Regard an interior collar parameter as a point of the half-open collar domain. -/
private def openCollarToHalfCollar (t : OpenCollarParameter) : HalfCollarParameter :=
  Opens.inclusion collarInterior_le_startNeighborhood t

private theorem contMDiff_openCollarToHalfCollar :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ openCollarToHalfCollar :=
  contMDiff_inclusion collarInterior_le_startNeighborhood

/-- Convert the strict signed left half-cylinder back to the outgoing collar source. -/
private def leftHalfToCollarSource (p : M₁ × LeftOpenCollarParameter) : CollarSource M₁ :=
  (p.1, openCollarToHalfCollar (openCollarToReversedLeftHalf.symm p.2))

private theorem contMDiff_leftHalfToCollarSource :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (leftHalfToCollarSource (M₁ := M₁)) := by
  exact contMDiff_fst.prodMk
    (contMDiff_openCollarToHalfCollar.comp
      (openCollarToReversedLeftHalf.contMDiff_invFun.comp contMDiff_snd))

/-- The two affine coordinate changes on the strict left overlap are inverse. -/
private theorem seamFromLeft_leftHalfToCollarSource
    (z : OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.seam OpenPieceIndex.left) :
    seamFromLeftCollarSource
        (leftHalfToCollarSource
          (seamLeftOverlapToLeftHalf B₀₁ B₁₂ z)) = z.1 := by
  apply Prod.ext
  · rfl
  · apply openCollarParameter_ext
    rw [seamCoordinate_fromLeftCollarSource]
    have ha := openCollarToReversedLeftHalf.apply_symm_apply
      (seamLeftOverlapToLeftHalf B₀₁ B₁₂ z).2
    have hv := congrArg
      (fun t : LeftOpenCollarParameter ↦ ((t.1 : CollarParameter) : ℝ)) ha
    simpa only [leftHalfToCollarSource, openCollarToHalfCollar,
      seamLeftOverlapToLeftHalf, openCollarToReversedLeftHalf_val,
      seamCoordinate_apply] using hv

/-- The seam-to-left change of pieces is the outgoing collar chart applied to the inverse
reversed affine coordinate. -/
private theorem contMDiff_openPieceTransition_seam_left :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (OpenEmbeddingGluing.transition
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
        OpenPieceIndex.seam OpenPieceIndex.left) := by
  apply (ContMDiff.subtypeVal_comp_iff
    (OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.left OpenPieceIndex.seam) _).mp
  apply (ContMDiff.subtypeVal_comp_iff (leftAwaySource B₀₁) _).mp
  have hsmooth : ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (fun z : OpenEmbeddingGluing.overlap
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
        OpenPieceIndex.seam OpenPieceIndex.left ↦
          B₀₁.outgoing.chart
            (leftHalfToCollarSource
              (seamLeftOverlapToLeftHalf B₀₁ B₁₂ z))) :=
    B₀₁.outgoing.chart.contMDiff.comp
      ((contMDiff_leftHalfToCollarSource (I := I)).comp
        (contMDiff_seamLeftOverlapToLeftHalf B₀₁ B₁₂))
  apply hsmooth.congr
  intro z
  apply (toGlueLeft_isClosedEmbedding B₀₁ B₁₂).injective
  have hmap : toGlueLeft B₀₁ B₁₂
        (OpenEmbeddingGluing.transition
          (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
          (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
          OpenPieceIndex.seam OpenPieceIndex.left z).1.1 =
      signedSeamMap B₀₁ B₁₂ z.1 :=
    OpenEmbeddingGluing.map_transition
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.seam OpenPieceIndex.left z
  have hexp : signedSeamMap B₀₁ B₁₂ z.1 =
      toGlueLeft B₀₁ B₁₂
        (B₀₁.outgoing.chart
          (leftHalfToCollarSource
            (seamLeftOverlapToLeftHalf B₀₁ B₁₂ z))) := by
    rw [← seamFromLeft_leftHalfToCollarSource B₀₁ B₁₂ z,
      signedSeamMap_fromLeftCollarSource]
  exact hmap.trans hexp

/-- Regard a seam--right overlap point as a point of the strict right half-cylinder. -/
private def seamRightOverlapToRightHalf
    (z : OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.seam OpenPieceIndex.right) :
    M₁ × RightOpenCollarParameter :=
  (z.1.1, ⟨z.1.2.1, ⟨seamRightOverlap_coordinate_lt B₀₁ B₁₂ z, z.1.2.2.2⟩⟩)

private theorem contMDiff_seamRightOverlapToRightHalf :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (seamRightOverlapToRightHalf B₀₁ B₁₂) := by
  apply (contMDiff_fst.comp contMDiff_subtype_val).prodMk
  apply (ContMDiff.subtypeVal_comp_iff collarRightOpenInterval _).mp
  have hval : ContMDiff (I.prod (𝓡∂ 1)) (𝓡∂ 1) ∞
      (fun z : OpenEmbeddingGluing.overlap
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
        OpenPieceIndex.seam OpenPieceIndex.right ↦ z.1.2.1) :=
    contMDiff_subtype_val.comp (contMDiff_snd.comp contMDiff_subtype_val)
  simpa only [Function.comp_def, seamRightOverlapToRightHalf] using hval

/-- Convert the strict signed right half-cylinder back to the incoming collar source. -/
private def rightHalfToCollarSource (p : M₁ × RightOpenCollarParameter) : CollarSource M₁ :=
  (p.1, openCollarToHalfCollar (openCollarToRightHalf.symm p.2))

private theorem contMDiff_rightHalfToCollarSource :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (rightHalfToCollarSource (M₁ := M₁)) := by
  exact contMDiff_fst.prodMk
    (contMDiff_openCollarToHalfCollar.comp
      (openCollarToRightHalf.contMDiff_invFun.comp contMDiff_snd))

/-- The two affine coordinate changes on the strict right overlap are inverse. -/
private theorem seamFromRight_rightHalfToCollarSource
    (z : OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.seam OpenPieceIndex.right) :
    seamFromRightCollarSource
        (rightHalfToCollarSource
          (seamRightOverlapToRightHalf B₀₁ B₁₂ z)) = z.1 := by
  apply Prod.ext
  · rfl
  · apply openCollarParameter_ext
    rw [seamCoordinate_fromRightCollarSource]
    have ha := openCollarToRightHalf.apply_symm_apply
      (seamRightOverlapToRightHalf B₀₁ B₁₂ z).2
    have hv := congrArg
      (fun t : RightOpenCollarParameter ↦ ((t.1 : CollarParameter) : ℝ)) ha
    simpa only [rightHalfToCollarSource, openCollarToHalfCollar,
      seamRightOverlapToRightHalf, openCollarToRightHalf_val,
      seamCoordinate_apply] using hv

/-- The seam-to-right change of pieces is the incoming collar chart applied to the inverse
right affine coordinate. -/
private theorem contMDiff_openPieceTransition_seam_right :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (OpenEmbeddingGluing.transition
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
        OpenPieceIndex.seam OpenPieceIndex.right) := by
  apply (ContMDiff.subtypeVal_comp_iff
    (OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.right OpenPieceIndex.seam) _).mp
  apply (ContMDiff.subtypeVal_comp_iff (rightAwaySource B₁₂) _).mp
  have hsmooth : ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (fun z : OpenEmbeddingGluing.overlap
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
        OpenPieceIndex.seam OpenPieceIndex.right ↦
          B₁₂.incoming.chart
            (rightHalfToCollarSource
              (seamRightOverlapToRightHalf B₀₁ B₁₂ z))) :=
    B₁₂.incoming.chart.contMDiff.comp
      ((contMDiff_rightHalfToCollarSource (I := I)).comp
        (contMDiff_seamRightOverlapToRightHalf B₀₁ B₁₂))
  apply hsmooth.congr
  intro z
  apply (toGlueRight_isClosedEmbedding B₀₁ B₁₂).injective
  have hmap : toGlueRight B₀₁ B₁₂
        (OpenEmbeddingGluing.transition
          (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
          (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
          OpenPieceIndex.seam OpenPieceIndex.right z).1.1 =
      signedSeamMap B₀₁ B₁₂ z.1 :=
    OpenEmbeddingGluing.map_transition
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.seam OpenPieceIndex.right z
  have hexp : signedSeamMap B₀₁ B₁₂ z.1 =
      toGlueRight B₀₁ B₁₂
        (B₁₂.incoming.chart
          (rightHalfToCollarSource
            (seamRightOverlapToRightHalf B₀₁ B₁₂ z))) := by
    rw [← seamFromRight_rightHalfToCollarSource B₀₁ B₁₂ z,
      signedSeamMap_fromRightCollarSource]
  exact hmap.trans hexp

/-- The two away pieces have empty overlap. -/
private theorem leftRightOverlap_false
    (z : OpenEmbeddingGluing.overlap
      (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
      (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
      OpenPieceIndex.left OpenPieceIndex.right) : False := by
  have hzrange := z.property
  change toGlueLeft B₀₁ B₁₂ z.1.1 ∈
    Set.range (fun y : rightAwaySource B₁₂ ↦
      toGlueRight B₀₁ B₁₂ y.1) at hzrange
  rcases hzrange with ⟨y, hy⟩
  obtain ⟨a, haleft, -⟩ :=
    (toGlueLeft_eq_toGlueRight_iff B₀₁ B₁₂ z.1.1 y.1).1 hy.symm
  exact z.1.2 ⟨a, haleft⟩

/-- The left-to-right transition is smooth vacuously. -/
private theorem contMDiff_openPieceTransition_left_right :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (OpenEmbeddingGluing.transition
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
        OpenPieceIndex.left OpenPieceIndex.right) := by
  intro z
  exact (leftRightOverlap_false B₀₁ B₁₂ z).elim

/-- The right-to-left transition is smooth vacuously. -/
private theorem contMDiff_openPieceTransition_right_left :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (OpenEmbeddingGluing.transition
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
        OpenPieceIndex.right OpenPieceIndex.left) := by
  intro z
  have hzrange := z.property
  change toGlueRight B₀₁ B₁₂ z.1.1 ∈
    Set.range (fun x : leftAwaySource B₀₁ ↦
      toGlueLeft B₀₁ B₁₂ x.1) at hzrange
  rcases hzrange with ⟨x, hx⟩
  obtain ⟨a, -, haright⟩ :=
    (toGlueLeft_eq_toGlueRight_iff B₀₁ B₁₂ x.1 z.1.1).1 hx
  exact (z.1.2 ⟨a, haright⟩).elim

/-- Every concrete overlap map in the canonical three-piece presentation is smooth. -/
public theorem openPieceTransition_contMDiff (i j : OpenPieceIndex) :
    ContMDiff (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (OpenEmbeddingGluing.transition
        (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
        (openPieceMap_isOpenEmbedding B₀₁ B₁₂) i j) := by
  cases i <;> cases j
  · exact contMDiff_openPieceTransition_refl B₀₁ B₁₂ OpenPieceIndex.left
  · exact contMDiff_openPieceTransition_left_seam B₀₁ B₁₂
  · exact contMDiff_openPieceTransition_left_right B₀₁ B₁₂
  · exact contMDiff_openPieceTransition_seam_left B₀₁ B₁₂
  · exact contMDiff_openPieceTransition_refl B₀₁ B₁₂ OpenPieceIndex.seam
  · exact contMDiff_openPieceTransition_seam_right B₀₁ B₁₂
  · exact contMDiff_openPieceTransition_right_left B₀₁ B₁₂
  · exact contMDiff_openPieceTransition_right_seam B₀₁ B₁₂
  · exact contMDiff_openPieceTransition_refl B₀₁ B₁₂ OpenPieceIndex.right

/-- Every ordered canonical partial change of pieces in the three-piece presentation is smooth
on its natural source. -/
public theorem openPresentation_pieceTransition_contMDiffOn
    (p q : Sigma fun i ↦ OpenPiece B₀₁ B₁₂ i) :
    ContMDiffOn (I.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞
      (openGluingPieceTransition (openPresentation B₀₁ B₁₂) p q)
      (openGluingPieceTransition (openPresentation B₀₁ B₁₂) p q).source :=
  contMDiffOn_pieceTransition_of_contMDiff_transition
    (I := I) (OpenPiece B₀₁ B₁₂) (openPieceMap B₀₁ B₁₂)
    (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
    (openPieceTransition_contMDiff B₀₁ B₁₂) p q

/-- The pushed piece charts of the canonical presentation are smoothly compatible. -/
public theorem openPresentation_smoothCompatibility :
    OpenGluingSmoothCompatibility (openPresentation B₀₁ B₁₂)
      (I.prod (𝓡∂ 1)) ∞ :=
  openGluingSmoothCompatibility_of_contMDiffOn_pieceTransition
    (openPresentation B₀₁ B₁₂) (I.prod (𝓡∂ 1)) ∞
    (openPresentation_pieceTransition_contMDiffOn B₀₁ B₁₂)

/-- The canonical three-piece open gluing is a smooth manifold with corners. -/
public theorem openPresentation_isManifold :
    letI : ChartedSpace (ModelProd H (EuclideanHalfSpace 1))
        (OpenGluedCarrier B₀₁ B₁₂) :=
      openGluingChartedSpace (openPresentation B₀₁ B₁₂)
    IsManifold (I.prod (𝓡∂ 1)) ∞ (OpenGluedCarrier B₀₁ B₁₂) := by
  exact openGluing_isManifold_of_contMDiffOn_pieceTransition
    (openPresentation B₀₁ B₁₂) (I.prod (𝓡∂ 1)) ∞
    (openPresentation_pieceTransition_contMDiffOn B₀₁ B₁₂)

end QuotientGluing
end SmoothCollaredBordism
end SphereSixComplex
