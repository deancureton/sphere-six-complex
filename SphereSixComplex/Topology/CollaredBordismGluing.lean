module

public import SphereSixComplex.Topology.CollaredBordismGluingHomotopy
public import SphereSixComplex.Topology.SmoothOpenEmbeddingPostcomp

/-!
# Gluing smooth collared bordisms

This file assembles the smooth three-piece carrier into an actual `SmoothCollaredBordism`.
The untouched outer collars are first restricted to the away pieces and then postcomposed with
the canonical smooth open embeddings.  The needed smooth-embedding facts are proved directly
for open changes of codomain, avoiding Mathlib's unfinished general composition declaration.
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

/-- The incoming outer end remains smoothly embedded after restricting its codomain to the left
away piece. -/
public theorem incomingBoundaryInLeftAway_isSmoothEmbedding :
    Manifold.IsSmoothEmbedding I (I.prod (𝓡∂ 1)) ∞
      (incomingBoundaryInLeftAway B₀₁) := by
  let hU : ∀ x : M₀, B₀₁.incoming.inclusion x ∈ leftAwaySource B₀₁ :=
    fun x ↦ (incomingBoundaryInLeftAway B₀₁ x).2
  have h := B₀₁.incoming.inclusion_isSmoothEmbedding.codRestrictOpens
    (leftAwaySource B₀₁) hU
  have heq : (fun x ↦ ⟨B₀₁.incoming.inclusion x, hU x⟩) =
      incomingBoundaryInLeftAway B₀₁ := by
    funext x
    apply Subtype.ext
    rfl
  rw [← heq]
  exact h

/-- The outgoing outer end remains smoothly embedded after restricting its codomain to the right
away piece. -/
public theorem outgoingBoundaryInRightAway_isSmoothEmbedding :
    Manifold.IsSmoothEmbedding I (I.prod (𝓡∂ 1)) ∞
      (outgoingBoundaryInRightAway B₁₂) := by
  let hU : ∀ x : M₂, B₁₂.outgoing.inclusion x ∈ rightAwaySource B₁₂ :=
    fun x ↦ (outgoingBoundaryInRightAway B₁₂ x).2
  have h := B₁₂.outgoing.inclusion_isSmoothEmbedding.codRestrictOpens
    (rightAwaySource B₁₂) hU
  have heq : (fun x ↦ ⟨B₁₂.outgoing.inclusion x, hU x⟩) =
      outgoingBoundaryInRightAway B₁₂ := by
    funext x
    apply Subtype.ext
    rfl
  rw [← heq]
  exact h

/-- The incoming outer collar on the smoothly glued carrier. -/
public noncomputable def smoothIncomingCollar :
    SmoothCollar I M₀ (OpenGluedCarrier B₀₁ B₁₂) where
  chart := smoothIncomingChart B₀₁ B₁₂
  inclusion_isSmoothEmbedding := by
    have h := (incomingBoundaryInLeftAway_isSmoothEmbedding B₀₁).comp_smoothOpenEmbedding
      (openPieceSmoothOpenEmbedding B₀₁ B₁₂ OpenPieceIndex.left)
    have heq :
        (openPieceSmoothOpenEmbedding B₀₁ B₁₂ OpenPieceIndex.left ∘
          incomingBoundaryInLeftAway B₀₁) =
      (fun x ↦ smoothIncomingChart B₀₁ B₁₂ (collarSourceZeroSection M₀ x)) := by
      funext x
      change openPieceSmoothOpenEmbedding B₀₁ B₁₂ OpenPieceIndex.left
          (incomingBoundaryInLeftAway B₀₁ x) = _
      rw [openPieceSmoothOpenEmbedding_apply, smoothIncomingChart_zero]
      rfl
    rw [← heq]
    exact h

/-- The outgoing outer collar on the smoothly glued carrier. -/
public noncomputable def smoothOutgoingCollar :
    SmoothCollar I M₂ (OpenGluedCarrier B₀₁ B₁₂) where
  chart := smoothOutgoingChart B₀₁ B₁₂
  inclusion_isSmoothEmbedding := by
    have h := (outgoingBoundaryInRightAway_isSmoothEmbedding B₁₂).comp_smoothOpenEmbedding
      (openPieceSmoothOpenEmbedding B₀₁ B₁₂ OpenPieceIndex.right)
    have heq :
        (openPieceSmoothOpenEmbedding B₀₁ B₁₂ OpenPieceIndex.right ∘
          outgoingBoundaryInRightAway B₁₂) =
      (fun x ↦ smoothOutgoingChart B₀₁ B₁₂ (collarSourceZeroSection M₂ x)) := by
      funext x
      change openPieceSmoothOpenEmbedding B₀₁ B₁₂ OpenPieceIndex.right
          (outgoingBoundaryInRightAway B₁₂ x) = _
      rw [openPieceSmoothOpenEmbedding_apply, smoothOutgoingChart_zero]
      rfl
    rw [← heq]
    exact h

@[simp]
public theorem smoothIncomingCollar_inclusion (x : M₀) :
    (smoothIncomingCollar B₀₁ B₁₂).inclusion x =
      smoothIncomingInclusion B₀₁ B₁₂ x :=
  smoothIncomingChart_zero B₀₁ B₁₂ x

@[simp]
public theorem smoothOutgoingCollar_inclusion (x : M₂) :
    (smoothOutgoingCollar B₀₁ B₁₂).inclusion x =
      smoothOutgoingInclusion B₀₁ B₁₂ x :=
  smoothOutgoingChart_zero B₀₁ B₁₂ x

/-- The smooth collared bordism obtained by gluing the outgoing collar of `B₀₁` to the
incoming collar of `B₁₂`. -/
public noncomputable def smoothGlue : SmoothCollaredBordism.{uE, uH, uM} I M₀ M₂ where
  W := OpenGluedCarrier B₀₁ B₁₂
  incoming := smoothIncomingCollar B₀₁ B₁₂
  outgoing := smoothOutgoingCollar B₀₁ B₁₂
  ends_disjoint := by
    have hin : (smoothIncomingCollar B₀₁ B₁₂).inclusion =
        smoothIncomingInclusion B₀₁ B₁₂ := by
      funext x
      exact smoothIncomingCollar_inclusion B₀₁ B₁₂ x
    have hout : (smoothOutgoingCollar B₀₁ B₁₂).inclusion =
        smoothOutgoingInclusion B₀₁ B₁₂ := by
      funext x
      exact smoothOutgoingCollar_inclusion B₀₁ B₁₂ x
    rw [hin, hout]
    exact smoothOuterRanges_disjoint B₀₁ B₁₂
  boundary_eq := by
    have hin : (smoothIncomingCollar B₀₁ B₁₂).inclusion =
        smoothIncomingInclusion B₀₁ B₁₂ := by
      funext x
      exact smoothIncomingCollar_inclusion B₀₁ B₁₂ x
    have hout : (smoothOutgoingCollar B₀₁ B₁₂).inclusion =
        smoothOutgoingInclusion B₀₁ B₁₂ := by
      funext x
      exact smoothOutgoingCollar_inclusion B₀₁ B₁₂ x
    rw [hin, hout]
    exact boundary_openGluedCarrier B₀₁ B₁₂

@[simp]
public theorem smoothGlue_incoming_inclusion (x : M₀) :
    (smoothGlue B₀₁ B₁₂).incoming.inclusion x =
      smoothIncomingInclusion B₀₁ B₁₂ x :=
  smoothIncomingCollar_inclusion B₀₁ B₁₂ x

@[simp]
public theorem smoothGlue_outgoing_inclusion (x : M₂) :
    (smoothGlue B₀₁ B₁₂).outgoing.inclusion x =
      smoothOutgoingInclusion B₀₁ B₁₂ x :=
  smoothOutgoingCollar_inclusion B₀₁ B₁₂ x

/-- The glued bordism's actual incoming collar inclusion is a homotopy equivalence under the two
incoming h-cobordism hypotheses. -/
public theorem smoothGlue_incoming_isHomotopyEquivalence
    (hIncoming₀₁ : IsHomotopyEquivalence B₀₁.incoming.inclusion)
    (hIncoming₁₂ : IsHomotopyEquivalence B₁₂.incoming.inclusion) :
    IsHomotopyEquivalence (smoothGlue B₀₁ B₁₂).incoming.inclusion := by
  apply (smoothIncomingInclusion_isHomotopyEquivalence B₀₁ B₁₂
    hIncoming₀₁ hIncoming₁₂).congr
  funext x
  exact (smoothGlue_incoming_inclusion B₀₁ B₁₂ x).symm

/-- The glued bordism's actual outgoing collar inclusion is a homotopy equivalence under the two
outgoing h-cobordism hypotheses. -/
public theorem smoothGlue_outgoing_isHomotopyEquivalence
    (hOutgoing₀₁ : IsHomotopyEquivalence B₀₁.outgoing.inclusion)
    (hOutgoing₁₂ : IsHomotopyEquivalence B₁₂.outgoing.inclusion) :
    IsHomotopyEquivalence (smoothGlue B₀₁ B₁₂).outgoing.inclusion := by
  apply (smoothOutgoingInclusion_isHomotopyEquivalence B₀₁ B₁₂
    hOutgoing₀₁ hOutgoing₁₂).congr
  funext x
  exact (smoothGlue_outgoing_inclusion B₀₁ B₁₂ x).symm

end QuotientGluing
end SmoothCollaredBordism
end SphereSixComplex
