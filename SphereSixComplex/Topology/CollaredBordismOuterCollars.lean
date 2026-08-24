module

public import SphereSixComplex.Topology.CollarBoundary
public import SphereSixComplex.Topology.CollaredBordismOpenStructure
public import SphereSixComplex.Topology.SmoothOpenEmbeddingRestrict

/-!
# The untouched outer collars in the away pieces

The incoming collar of the left bordism never meets its outgoing boundary, and symmetrically for
the right bordism.  Hence both untouched collars restrict to smooth open embeddings into the two
away pieces of the three-piece presentation.
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

/-- The incoming collar target lies in the left away piece. -/
public theorem incomingChart_target_subset_leftAwaySource :
    (B₀₁.incoming.chart.target : Set B₀₁.W) ⊆ leftAwaySource B₀₁ := by
  intro w hw
  exact Set.disjoint_left.1 (B₀₁.incoming_target_disjoint_outgoing) hw

/-- The outgoing collar target lies in the right away piece. -/
public theorem outgoingChart_target_subset_rightAwaySource :
    (B₁₂.outgoing.chart.target : Set B₁₂.W) ⊆ rightAwaySource B₁₂ := by
  intro w hw
  exact Set.disjoint_left.1 (B₁₂.outgoing_target_disjoint_incoming) hw

/-- The original incoming collar, with codomain restricted to the left away piece. -/
public def incomingAwayChart :
    SmoothOpenEmbedding (I.prod (𝓡∂ 1)) (CollarSource M₀) (leftAwaySource B₀₁) :=
  B₀₁.incoming.chart.codRestrict (leftAwaySource B₀₁)
    (incomingChart_target_subset_leftAwaySource B₀₁)

/-- The original outgoing collar, with codomain restricted to the right away piece. -/
public def outgoingAwayChart :
    SmoothOpenEmbedding (I.prod (𝓡∂ 1)) (CollarSource M₂) (rightAwaySource B₁₂) :=
  B₁₂.outgoing.chart.codRestrict (rightAwaySource B₁₂)
    (outgoingChart_target_subset_rightAwaySource B₁₂)

@[simp]
public theorem incomingAwayChart_val (p : CollarSource M₀) :
    ((incomingAwayChart B₀₁ p : leftAwaySource B₀₁) : B₀₁.W) =
      B₀₁.incoming.chart p :=
  SmoothOpenEmbedding.codRestrict_apply _ _ _ _

@[simp]
public theorem outgoingAwayChart_val (p : CollarSource M₂) :
    ((outgoingAwayChart B₁₂ p : rightAwaySource B₁₂) : B₁₂.W) =
      B₁₂.outgoing.chart p :=
  SmoothOpenEmbedding.codRestrict_apply _ _ _ _

@[simp]
public theorem incomingAwayChart_zero (x : M₀) :
    ((incomingAwayChart B₀₁ (collarSourceZeroSection M₀ x) :
        leftAwaySource B₀₁) : B₀₁.W) =
      B₀₁.incoming.inclusion x := by
  rfl

@[simp]
public theorem outgoingAwayChart_zero (x : M₂) :
    ((outgoingAwayChart B₁₂ (collarSourceZeroSection M₂ x) :
        rightAwaySource B₁₂) : B₁₂.W) =
      B₁₂.outgoing.inclusion x := by
  rfl

end QuotientGluing
end SmoothCollaredBordism
end SphereSixComplex
