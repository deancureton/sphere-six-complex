module

public import SphereSixComplex.Topology.ClosedEmbeddingGluing
public import SphereSixComplex.Topology.CollaredBordism

/-!
# The topological quotient of two collared bordisms

This file constructs the point-set topological carrier obtained by gluing the outgoing boundary
of one `SmoothCollaredBordism` to the incoming boundary of another.  The smooth structure near the
seam is deliberately not constructed here.  The carrier is the direct quotient of the disjoint
union, identifying only corresponding points of the common boundary manifold.

The general compact-Hausdorff quotient results are in `ClosedEmbeddingGluing`.  Here they are
specialized to collar inclusions and packaged with the canonical maps from the two bordisms and
from the two unglued outer boundary components.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold Topology

namespace SphereSixComplex
namespace SmoothCollaredBordism
namespace QuotientGluing

open ClosedEmbeddingGluing

universe uE uH uM₀ uM₁ uM₂ uW₀₁ uW₁₂

variable {E : Type uE} {H : Type uH} {M₀ : Type uM₀} {M₁ : Type uM₁}
  {M₂ : Type uM₂}
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
  (B₀₁ : SmoothCollaredBordism.{uE, uH, uW₀₁, uM₀, uM₁} I M₀ M₁)
  (B₁₂ : SmoothCollaredBordism.{uE, uH, uW₁₂, uM₁, uM₂} I M₁ M₂)

/-- The direct equivalence relation used to glue the two bordism carriers.  It identifies
`B₀₁.outgoing.inclusion x` with `B₁₂.incoming.inclusion x`, and makes no other
identifications. -/
public abbrev glueSetoid : Setoid (B₀₁.W ⊕ B₁₂.W) :=
  sumGlueSetoid B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective

/-- The topological carrier obtained by gluing the two bordisms along their common end. -/
public abbrev Glue := Quotient (glueSetoid B₀₁ B₁₂)

/-- The canonical map from the first bordism into the glued carrier. -/
public def toGlueLeft : B₀₁.W → Glue B₀₁ B₁₂ :=
  toSumGlueLeft B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective

/-- The canonical map from the second bordism into the glued carrier. -/
public def toGlueRight : B₁₂.W → Glue B₀₁ B₁₂ :=
  toSumGlueRight B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective

@[simp]
public theorem toGlue_commute (x : M₁) :
    toGlueLeft B₀₁ B₁₂ (B₀₁.outgoing.inclusion x) =
      toGlueRight B₀₁ B₁₂ (B₁₂.incoming.inclusion x) :=
  ClosedEmbeddingGluing.toSumGlue_commute
    B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective x

/-- Equality between points from opposite bordism carriers occurs precisely at a common seam
point. -/
public theorem toGlueLeft_eq_toGlueRight_iff (w₀₁ : B₀₁.W) (w₁₂ : B₁₂.W) :
    toGlueLeft B₀₁ B₁₂ w₀₁ = toGlueRight B₀₁ B₁₂ w₁₂ ↔
      ∃ x : M₁, B₀₁.outgoing.inclusion x = w₀₁ ∧
        B₁₂.incoming.inclusion x = w₁₂ :=
  toSumGlue_eq_iff B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective w₀₁ w₁₂

/-- The glued carrier is compact. -/
public theorem glue_compactSpace : CompactSpace (Glue B₀₁ B₁₂) :=
  inferInstance

/-- The glued carrier is Hausdorff. -/
public theorem glue_t2Space : T2Space (Glue B₀₁ B₁₂) :=
  sumGlue_t2Space B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective
    B₀₁.outgoing.inclusion_contMDiff.continuous
    B₁₂.incoming.inclusion_contMDiff.continuous

/-- The canonical Hausdorff instance on the glued carrier. -/
public noncomputable instance instT2Space : T2Space (Glue B₀₁ B₁₂) :=
  glue_t2Space B₀₁ B₁₂

/-- The glued carrier is second countable. -/
public theorem glue_secondCountableTopology :
    SecondCountableTopology (Glue B₀₁ B₁₂) :=
  sumGlue_secondCountableTopology
    B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective
    B₀₁.outgoing.inclusion_contMDiff.continuous
    B₁₂.incoming.inclusion_contMDiff.continuous

/-- The canonical second-countable instance on the glued carrier. -/
public noncomputable instance instSecondCountableTopology :
    SecondCountableTopology (Glue B₀₁ B₁₂) :=
  glue_secondCountableTopology B₀₁ B₁₂

/-- The first bordism is a closed subspace of the glued carrier. -/
public theorem toGlueLeft_isClosedEmbedding :
    IsClosedEmbedding (toGlueLeft B₀₁ B₁₂) :=
  ClosedEmbeddingGluing.toSumGlueLeft_isClosedEmbedding
    B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective
    B₀₁.outgoing.inclusion_contMDiff.continuous
    B₁₂.incoming.inclusion_contMDiff.continuous

/-- The second bordism is a closed subspace of the glued carrier. -/
public theorem toGlueRight_isClosedEmbedding :
    IsClosedEmbedding (toGlueRight B₀₁ B₁₂) :=
  ClosedEmbeddingGluing.toSumGlueRight_isClosedEmbedding
    B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective
    B₀₁.outgoing.inclusion_contMDiff.continuous
    B₁₂.incoming.inclusion_contMDiff.continuous

/-- Points of the first bordism away from the glued outgoing boundary. -/
public abbrev LeftAway :=
  ClosedEmbeddingGluing.LeftAway B₀₁.outgoing.inclusion

/-- Points of the second bordism away from the glued incoming boundary. -/
public abbrev RightAway :=
  ClosedEmbeddingGluing.RightAway B₁₂.incoming.inclusion

/-- The canonical map on the first bordism away from the seam. -/
public def toGlueLeftAway : LeftAway B₀₁ → Glue B₀₁ B₁₂ :=
  toSumGlueLeftAway B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective

/-- The canonical map on the second bordism away from the seam. -/
public def toGlueRightAway : RightAway B₁₂ → Glue B₀₁ B₁₂ :=
  toSumGlueRightAway B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective

/-- The image of the first bordism away from the seam is the complement of the image of the
second bordism. -/
public theorem range_toGlueLeftAway :
    Set.range (toGlueLeftAway B₀₁ B₁₂) =
      (Set.range (toGlueRight B₀₁ B₁₂))ᶜ :=
  range_toSumGlueLeftAway
    B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective

/-- The image of the second bordism away from the seam is the complement of the image of the
first bordism. -/
public theorem range_toGlueRightAway :
    Set.range (toGlueRightAway B₀₁ B₁₂) =
      (Set.range (toGlueLeft B₀₁ B₁₂))ᶜ :=
  range_toSumGlueRightAway
    B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective

/-- Away from the seam, the first canonical map is an open embedding. -/
public theorem toGlueLeftAway_isOpenEmbedding :
    IsOpenEmbedding (toGlueLeftAway B₀₁ B₁₂) :=
  ClosedEmbeddingGluing.toSumGlueLeftAway_isOpenEmbedding
    B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective
    B₀₁.outgoing.inclusion_contMDiff.continuous
    B₁₂.incoming.inclusion_contMDiff.continuous

/-- Away from the seam, the second canonical map is an open embedding. -/
public theorem toGlueRightAway_isOpenEmbedding :
    IsOpenEmbedding (toGlueRightAway B₀₁ B₁₂) :=
  ClosedEmbeddingGluing.toSumGlueRightAway_isOpenEmbedding
    B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective
    B₀₁.outgoing.inclusion_contMDiff.continuous
    B₁₂.incoming.inclusion_contMDiff.continuous

/-- The incoming outer boundary of the composite, as a map to the glued carrier. -/
public def incomingInclusion : M₀ → Glue B₀₁ B₁₂ :=
  toGlueLeft B₀₁ B₁₂ ∘ B₀₁.incoming.inclusion

/-- The outgoing outer boundary of the composite, as a map to the glued carrier. -/
public def outgoingInclusion : M₂ → Glue B₀₁ B₁₂ :=
  toGlueRight B₀₁ B₁₂ ∘ B₁₂.outgoing.inclusion

/-- The incoming outer boundary, regarded as a map into the first bordism away from the seam. -/
public def incomingToLeftAway (x : M₀) : LeftAway B₀₁ :=
  ⟨B₀₁.incoming.inclusion x, by
    rintro ⟨y, hy⟩
    exact Set.disjoint_left.1 B₀₁.ends_disjoint ⟨x, rfl⟩ ⟨y, hy⟩⟩

/-- The outgoing outer boundary, regarded as a map into the second bordism away from the seam. -/
public def outgoingToRightAway (x : M₂) : RightAway B₁₂ :=
  ⟨B₁₂.outgoing.inclusion x, by
    rintro ⟨y, hy⟩
    exact Set.disjoint_left.1 B₁₂.ends_disjoint ⟨y, hy⟩ ⟨x, rfl⟩⟩

@[simp]
public theorem incomingInclusion_apply (x : M₀) :
    incomingInclusion B₀₁ B₁₂ x =
      toGlueLeft B₀₁ B₁₂ (B₀₁.incoming.inclusion x) :=
  rfl

@[simp]
public theorem outgoingInclusion_apply (x : M₂) :
    outgoingInclusion B₀₁ B₁₂ x =
      toGlueRight B₀₁ B₁₂ (B₁₂.outgoing.inclusion x) :=
  rfl

/-- The incoming outer-boundary map factors through the open complement of the seam. -/
public theorem incomingInclusion_factor :
    incomingInclusion B₀₁ B₁₂ =
      toGlueLeftAway B₀₁ B₁₂ ∘ incomingToLeftAway B₀₁ :=
  rfl

/-- The outgoing outer-boundary map factors through the open complement of the seam. -/
public theorem outgoingInclusion_factor :
    outgoingInclusion B₀₁ B₁₂ =
      toGlueRightAway B₀₁ B₁₂ ∘ outgoingToRightAway B₁₂ :=
  rfl

/-- The incoming outer boundary remains embedded after restricting its codomain to the first
bordism away from the seam. -/
public theorem incomingToLeftAway_isEmbedding :
    IsEmbedding (incomingToLeftAway B₀₁) := by
  rw [← IsEmbedding.subtypeVal.of_comp_iff]
  exact B₀₁.incoming.inclusion_isEmbedding

/-- The outgoing outer boundary remains embedded after restricting its codomain to the second
bordism away from the seam. -/
public theorem outgoingToRightAway_isEmbedding :
    IsEmbedding (outgoingToRightAway B₁₂) := by
  rw [← IsEmbedding.subtypeVal.of_comp_iff]
  exact B₁₂.outgoing.inclusion_isEmbedding

/-- The incoming outer boundary is closed even in the open complement of the seam. -/
public theorem incomingToLeftAway_isClosedEmbedding :
    IsClosedEmbedding (incomingToLeftAway B₀₁) :=
  (incomingToLeftAway_isEmbedding B₀₁).continuous.isClosedEmbedding
    (incomingToLeftAway_isEmbedding B₀₁).injective

/-- The outgoing outer boundary is closed even in the open complement of the seam. -/
public theorem outgoingToRightAway_isClosedEmbedding :
    IsClosedEmbedding (outgoingToRightAway B₁₂) :=
  (outgoingToRightAway_isEmbedding B₁₂).continuous.isClosedEmbedding
    (outgoingToRightAway_isEmbedding B₁₂).injective

/-- The incoming outer boundary is a closed subspace of the glued carrier. -/
public theorem incomingInclusion_isClosedEmbedding :
    IsClosedEmbedding (incomingInclusion B₀₁ B₁₂) := by
  exact (toGlueLeft_isClosedEmbedding B₀₁ B₁₂).comp
    (B₀₁.incoming.inclusion_contMDiff.continuous.isClosedEmbedding
      B₀₁.incoming.inclusion_isEmbedding.injective)

/-- The outgoing outer boundary is a closed subspace of the glued carrier. -/
public theorem outgoingInclusion_isClosedEmbedding :
    IsClosedEmbedding (outgoingInclusion B₀₁ B₁₂) := by
  exact (toGlueRight_isClosedEmbedding B₀₁ B₁₂).comp
    (B₁₂.outgoing.inclusion_contMDiff.continuous.isClosedEmbedding
      B₁₂.outgoing.inclusion_isEmbedding.injective)

/-- The incoming outer boundary map is a topological embedding. -/
public theorem incomingInclusion_isEmbedding :
    IsEmbedding (incomingInclusion B₀₁ B₁₂) :=
  (incomingInclusion_isClosedEmbedding B₀₁ B₁₂).isEmbedding

/-- The outgoing outer boundary map is a topological embedding. -/
public theorem outgoingInclusion_isEmbedding :
    IsEmbedding (outgoingInclusion B₀₁ B₁₂) :=
  (outgoingInclusion_isClosedEmbedding B₀₁ B₁₂).isEmbedding

/-- The two unglued outer boundary components have disjoint images in the quotient. -/
public theorem outerRanges_disjoint :
    Disjoint (Set.range (incomingInclusion B₀₁ B₁₂))
      (Set.range (outgoingInclusion B₀₁ B₁₂)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨z, hz⟩
  obtain ⟨y, hy, -⟩ :=
    (toGlueLeft_eq_toGlueRight_iff B₀₁ B₁₂
      (B₀₁.incoming.inclusion x) (B₁₂.outgoing.inclusion z)).1 hz.symm
  exact Set.disjoint_left.1 B₀₁.ends_disjoint ⟨x, rfl⟩ ⟨y, hy⟩

end QuotientGluing
end SmoothCollaredBordism
end SphereSixComplex
