module

public import SphereSixComplex.Topology.CollaredBordismSeam
public import SphereSixComplex.Topology.OpenEmbeddingGluing

/-!
# The three-piece open presentation of a glued collared bordism

The direct quotient of two collared bordisms is covered by the complement of the outgoing
boundary in the left carrier, a signed open bicollar around the seam, and the complement of the
incoming boundary in the right carrier.  This file packages that cover as `TopCat.GlueData` while
retaining the original topology on each of the three source pieces.
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

/-- The three members of the canonical seam cover. -/
public inductive OpenPieceIndex : Type uM
  | left
  | seam
  | right
  deriving DecidableEq

/-- The left away piece packaged as an actual open subspace, so it inherits the ambient smooth
structure definitionally. -/
public def leftAwaySource : Opens B₀₁.W where
  carrier := (Set.range B₀₁.outgoing.inclusion)ᶜ
  is_open' := (B₀₁.outgoing.inclusion_contMDiff.continuous.isClosedEmbedding
    B₀₁.outgoing.inclusion_isEmbedding.injective).isClosed_range.isOpen_compl

/-- The right away piece packaged as an actual open subspace. -/
public def rightAwaySource : Opens B₁₂.W where
  carrier := (Set.range B₁₂.incoming.inclusion)ᶜ
  is_open' := (B₁₂.incoming.inclusion_contMDiff.continuous.isClosedEmbedding
    B₁₂.incoming.inclusion_isEmbedding.injective).isClosed_range.isOpen_compl

/-- The source space of each member of the canonical seam cover. -/
public abbrev OpenPiece : OpenPieceIndex → Type uM
  | .left => leftAwaySource B₀₁
  | .seam => M₁ × OpenCollarParameter
  | .right => rightAwaySource B₁₂

public instance (i : OpenPieceIndex) : TopologicalSpace (OpenPiece B₀₁ B₁₂ i) := by
  cases i <;> infer_instance

/-- Each of the three open pieces mapped into the direct quotient. -/
public def openPieceMap : ∀ i : OpenPieceIndex,
    OpenPiece B₀₁ B₁₂ i → Glue B₀₁ B₁₂
  | .left => fun x ↦ toGlueLeftAway B₀₁ B₁₂ ⟨x.1, x.2⟩
  | .seam => signedSeamMap B₀₁ B₁₂
  | .right => fun x ↦ toGlueRightAway B₀₁ B₁₂ ⟨x.1, x.2⟩

/-- Every member of the three-piece presentation is an open embedding. -/
public theorem openPieceMap_isOpenEmbedding (i : OpenPieceIndex) :
    IsOpenEmbedding (openPieceMap B₀₁ B₁₂ i) := by
  cases i with
  | left => exact toGlueLeftAway_isOpenEmbedding B₀₁ B₁₂
  | seam => exact signedSeamMap_isOpenEmbedding B₀₁ B₁₂
  | right => exact toGlueRightAway_isOpenEmbedding B₀₁ B₁₂

/-- The ranges of the three piece maps cover the direct quotient. -/
public theorem range_openPieceMap_iUnion :
    (⋃ i, Set.range (openPieceMap B₀₁ B₁₂ i)) = Set.univ := by
  ext q
  constructor
  · intro
    trivial
  · intro
    have hq : q ∈
        Set.range (toGlueLeftAway B₀₁ B₁₂) ∪
          seamNeighborhood B₀₁ B₁₂ ∪
          Set.range (toGlueRightAway B₀₁ B₁₂) := by
      rw [threePieceSeamCover B₀₁ B₁₂]
      trivial
    rcases hq with hleftOrSeam | hright
    · rcases hleftOrSeam with hleft | hseam
      · exact Set.mem_iUnion.2 ⟨OpenPieceIndex.left, hleft⟩
      · rw [← range_signedSeamMap B₀₁ B₁₂] at hseam
        exact Set.mem_iUnion.2 ⟨OpenPieceIndex.seam, hseam⟩
    · exact Set.mem_iUnion.2 ⟨OpenPieceIndex.right, hright⟩

/-- The `TopCat.GlueData` presented by the three open pieces. -/
public abbrev openPresentation : TopCat.GlueData :=
  OpenEmbeddingGluing.glueData
    (OpenPiece B₀₁ B₁₂)
    (openPieceMap B₀₁ B₁₂)
    (openPieceMap_isOpenEmbedding B₀₁ B₁₂)

/-- The abstract carrier obtained by gluing the three smooth source pieces. -/
public abbrev OpenGluedCarrier :=
  (openPresentation B₀₁ B₁₂).toGlueData.glued

/-- The abstract three-piece gluing is canonically homeomorphic to the direct quotient. -/
public def openPresentationHomeomorph :
    OpenGluedCarrier B₀₁ B₁₂ ≃ₜ Glue B₀₁ B₁₂ :=
  OpenEmbeddingGluing.glueHomeomorph
    (OpenPiece B₀₁ B₁₂)
    (openPieceMap B₀₁ B₁₂)
    (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
    (range_openPieceMap_iUnion B₀₁ B₁₂)

@[simp]
public theorem openPresentationHomeomorph_piece
    (i : OpenPieceIndex) (x : OpenPiece B₀₁ B₁₂ i) :
    openPresentationHomeomorph B₀₁ B₁₂
        ((openPresentation B₀₁ B₁₂).toGlueData.ι i x) =
      openPieceMap B₀₁ B₁₂ i x :=
  OpenEmbeddingGluing.glueHomeomorph_ι
    (OpenPiece B₀₁ B₁₂)
    (openPieceMap B₀₁ B₁₂)
    (openPieceMap_isOpenEmbedding B₀₁ B₁₂)
    (range_openPieceMap_iUnion B₀₁ B₁₂) i x

end QuotientGluing
end SmoothCollaredBordism
end SphereSixComplex
