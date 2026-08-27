module

public import SphereSixComplex.Topology.CollaredBordismPieceBoundary
public import SphereSixComplex.Topology.CollaredBordismPieceTransitions
public import SphereSixComplex.Topology.SmoothOpenGluingInclusions

/-!
# Smooth assembly of the three-piece collared-bordism gluing

The canonical left-away, seam, and right-away presentation has smoothly compatible changes of
pieces.  This file installs the resulting manifold structure, bundles its canonical piece maps
as smooth open embeddings, and uses those local diffeomorphisms to compute the boundary of the
glued carrier.
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

/-- The manifold instance produced by the smoothly compatible three-piece presentation. -/
public noncomputable instance instIsManifoldOpenGluedCarrier :
    IsManifold (I.prod (𝓡∂ 1)) ∞ (OpenGluedCarrier B₀₁ B₁₂) :=
  openPresentation_isManifold B₀₁ B₁₂

/-- A canonical member of the three-piece cover, bundled as a smooth open embedding into the
glued carrier. -/
public noncomputable def openPieceSmoothOpenEmbedding (i : OpenPieceIndex) :
    SmoothOpenEmbedding (I.prod (𝓡∂ 1))
      (OpenPiece B₀₁ B₁₂ i) (OpenGluedCarrier B₀₁ B₁₂) :=
  openGluingPieceSmoothOpenEmbedding (openPresentation B₀₁ B₁₂)
    (I.prod (𝓡∂ 1)) (openPresentation_smoothCompatibility B₀₁ B₁₂) i

@[simp]
public theorem openPieceSmoothOpenEmbedding_apply (i : OpenPieceIndex)
    (x : OpenPiece B₀₁ B₁₂ i) :
    openPieceSmoothOpenEmbedding B₀₁ B₁₂ i x =
      (openPresentation B₀₁ B₁₂).toGlueData.ι i x := by
  exact openGluingPieceSmoothOpenEmbedding_apply
    (openPresentation B₀₁ B₁₂) (I.prod (𝓡∂ 1))
    (openPresentation_smoothCompatibility B₀₁ B₁₂) i x

/-- Boundary membership can be checked in any canonical open piece containing the point. -/
public theorem openPiece_mem_boundary_iff (i : OpenPieceIndex)
    (x : OpenPiece B₀₁ B₁₂ i) :
    (openPresentation B₀₁ B₁₂).toGlueData.ι i x ∈
        (I.prod (𝓡∂ 1)).boundary (OpenGluedCarrier B₀₁ B₁₂) ↔
      x ∈ (I.prod (𝓡∂ 1)).boundary (OpenPiece B₀₁ B₁₂ i) := by
  let e := openPieceSmoothOpenEmbedding B₀₁ B₁₂ i
  have hpre := e.toDiffeomorph.preimage_boundary (n := ∞) (by simp)
  rw [ModelWithCorners.boundary_open] at hpre
  have hx := Set.ext_iff.mp hpre x
  rw [← openPieceSmoothOpenEmbedding_apply B₀₁ B₁₂ i x]
  simpa [e] using hx

/-- The incoming outer end as a map into the smooth three-piece gluing. -/
public def smoothIncomingInclusion (x : M₀) : OpenGluedCarrier B₀₁ B₁₂ :=
  (openPresentation B₀₁ B₁₂).toGlueData.ι OpenPieceIndex.left
    (incomingBoundaryInLeftAway B₀₁ x)

/-- The outgoing outer end as a map into the smooth three-piece gluing. -/
public def smoothOutgoingInclusion (x : M₂) : OpenGluedCarrier B₀₁ B₁₂ :=
  (openPresentation B₀₁ B₁₂).toGlueData.ι OpenPieceIndex.right
    (outgoingBoundaryInRightAway B₁₂ x)

/-- Under the canonical comparison with the direct quotient, the smooth incoming map is the
usual quotient incoming map. -/
@[simp]
public theorem openPresentationHomeomorph_smoothIncomingInclusion (x : M₀) :
    openPresentationHomeomorph B₀₁ B₁₂ (smoothIncomingInclusion B₀₁ B₁₂ x) =
      incomingInclusion B₀₁ B₁₂ x := by
  rw [smoothIncomingInclusion, openPresentationHomeomorph_piece]
  rfl

/-- Under the canonical comparison with the direct quotient, the smooth outgoing map is the
usual quotient outgoing map. -/
@[simp]
public theorem openPresentationHomeomorph_smoothOutgoingInclusion (x : M₂) :
    openPresentationHomeomorph B₀₁ B₁₂ (smoothOutgoingInclusion B₀₁ B₁₂ x) =
      outgoingInclusion B₀₁ B₁₂ x := by
  rw [smoothOutgoingInclusion, openPresentationHomeomorph_piece]
  rfl

/-- The boundary of the smoothly glued carrier consists exactly of the two untouched outer
ends. -/
public theorem boundary_openGluedCarrier :
    (I.prod (𝓡∂ 1)).boundary (OpenGluedCarrier B₀₁ B₁₂) =
      Set.range (smoothIncomingInclusion B₀₁ B₁₂) ∪
        Set.range (smoothOutgoingInclusion B₀₁ B₁₂) := by
  ext q
  constructor
  · intro hq
    obtain ⟨i, x, rfl⟩ := (openPresentation B₀₁ B₁₂).ι_jointly_surjective q
    have hx := (openPiece_mem_boundary_iff B₀₁ B₁₂ i x).1 hq
    cases i with
    | left =>
        rw [boundary_leftAwaySource B₀₁] at hx
        rcases hx with ⟨a, rfl⟩
        exact Or.inl ⟨a, rfl⟩
    | seam =>
        rw [boundary_seamPiece (I := I) (M₁ := M₁)] at hx
        exact hx.elim
    | right =>
        rw [boundary_rightAwaySource B₁₂] at hx
        rcases hx with ⟨a, rfl⟩
        exact Or.inr ⟨a, rfl⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · apply (openPiece_mem_boundary_iff B₀₁ B₁₂ OpenPieceIndex.left _).2
      rw [boundary_leftAwaySource B₀₁]
      exact ⟨a, rfl⟩
    · apply (openPiece_mem_boundary_iff B₀₁ B₁₂ OpenPieceIndex.right _).2
      rw [boundary_rightAwaySource B₁₂]
      exact ⟨a, rfl⟩

/-- The untouched incoming collar, followed by the left canonical piece inclusion. -/
public noncomputable def smoothIncomingChart :
    SmoothOpenEmbedding (I.prod (𝓡∂ 1)) (CollarSource M₀)
      (OpenGluedCarrier B₀₁ B₁₂) :=
  (openPieceSmoothOpenEmbedding B₀₁ B₁₂ OpenPieceIndex.left).comp
    (incomingAwayChart B₀₁)

/-- The untouched outgoing collar, followed by the right canonical piece inclusion. -/
public noncomputable def smoothOutgoingChart :
    SmoothOpenEmbedding (I.prod (𝓡∂ 1)) (CollarSource M₂)
      (OpenGluedCarrier B₀₁ B₁₂) :=
  (openPieceSmoothOpenEmbedding B₀₁ B₁₂ OpenPieceIndex.right).comp
    (outgoingAwayChart B₁₂)

@[simp]
public theorem smoothIncomingChart_apply (p : CollarSource M₀) :
    smoothIncomingChart B₀₁ B₁₂ p =
      (openPresentation B₀₁ B₁₂).toGlueData.ι OpenPieceIndex.left
        (incomingAwayChart B₀₁ p) := by
  change (openPieceSmoothOpenEmbedding B₀₁ B₁₂ OpenPieceIndex.left).comp
      (incomingAwayChart B₀₁) p = _
  rw [SmoothOpenEmbedding.comp_apply, openPieceSmoothOpenEmbedding_apply]

@[simp]
public theorem smoothOutgoingChart_apply (p : CollarSource M₂) :
    smoothOutgoingChart B₀₁ B₁₂ p =
      (openPresentation B₀₁ B₁₂).toGlueData.ι OpenPieceIndex.right
        (outgoingAwayChart B₁₂ p) := by
  change (openPieceSmoothOpenEmbedding B₀₁ B₁₂ OpenPieceIndex.right).comp
      (outgoingAwayChart B₁₂) p = _
  rw [SmoothOpenEmbedding.comp_apply, openPieceSmoothOpenEmbedding_apply]

@[simp]
public theorem smoothIncomingChart_zero (x : M₀) :
    smoothIncomingChart B₀₁ B₁₂ (collarSourceZeroSection M₀ x) =
      smoothIncomingInclusion B₀₁ B₁₂ x := by
  rw [smoothIncomingChart_apply]
  rfl

@[simp]
public theorem smoothOutgoingChart_zero (x : M₂) :
    smoothOutgoingChart B₀₁ B₁₂ (collarSourceZeroSection M₂ x) =
      smoothOutgoingInclusion B₀₁ B₁₂ x := by
  rw [smoothOutgoingChart_apply]
  rfl

/-- The two outer ends remain disjoint in the smooth three-piece gluing. -/
public theorem smoothOuterRanges_disjoint :
    Disjoint (Set.range (smoothIncomingInclusion B₀₁ B₁₂))
      (Set.range (smoothOutgoingInclusion B₀₁ B₁₂)) := by
  rw [Set.disjoint_left]
  rintro q ⟨x, hx⟩ ⟨y, hy⟩
  have hxy : incomingInclusion B₀₁ B₁₂ x = outgoingInclusion B₀₁ B₁₂ y := by
    rw [← openPresentationHomeomorph_smoothIncomingInclusion,
      ← openPresentationHomeomorph_smoothOutgoingInclusion]
    exact congrArg (openPresentationHomeomorph B₀₁ B₁₂) (hx.trans hy.symm)
  exact Set.disjoint_left.1 (outerRanges_disjoint B₀₁ B₁₂)
    ⟨x, rfl⟩ ⟨y, hxy.symm⟩

end QuotientGluing
end SmoothCollaredBordism
end SphereSixComplex
