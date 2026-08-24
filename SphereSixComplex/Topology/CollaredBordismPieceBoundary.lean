module

public import SphereSixComplex.Topology.CollaredBordismOuterCollars

/-!
# Boundary calculations on the three open gluing pieces

The left away piece retains exactly the incoming boundary of the first bordism, the right away
piece retains exactly the outgoing boundary of the second, and the signed seam cylinder is
boundaryless.
-/

@[expose] public section

noncomputable section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

/-- The open collar interval has no manifold boundary. -/
public theorem boundary_openCollarParameter :
    (𝓡∂ 1).boundary OpenCollarParameter = ∅ := by
  rw [ModelWithCorners.boundary_open, boundary_Icc]
  ext t
  constructor
  · intro ht
    rcases ht with ht | ht
    · have hzero : (⊥ : CollarParameter) = collarStart := by
        apply Subtype.ext
        norm_num [collarStart]
      have hv := congrArg Subtype.val (ht.trans hzero)
      have hpos := t.2.1
      change (0 : ℝ) < (t.1 : ℝ) at hpos
      change ((t.1 : CollarParameter) : ℝ) = 0 at hv
      linarith
    · have hone : (⊤ : CollarParameter) = collarFinish := by
        apply Subtype.ext
        norm_num [collarFinish]
      have hv := congrArg Subtype.val (ht.trans hone)
      have hlt := t.2.2
      change (t.1 : ℝ) < 1 at hlt
      change ((t.1 : CollarParameter) : ℝ) = 1 at hv
      linarith
  · intro ht
    exact ht.elim

/-- The canonical boundaryless structure on the open collar interval. -/
public instance instBoundarylessManifoldOpenCollarParameter :
    BoundarylessManifold (𝓡∂ 1) OpenCollarParameter :=
  ModelWithCorners.Boundaryless.of_boundary_eq_empty boundary_openCollarParameter

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

/-- The incoming end as a point of the left away piece. -/
public def incomingBoundaryInLeftAway (x : M₀) : leftAwaySource B₀₁ :=
  ⟨B₀₁.incoming.inclusion x, by
    rintro ⟨y, hy⟩
    exact Set.disjoint_left.1 B₀₁.ends_disjoint ⟨x, rfl⟩ ⟨y, hy⟩⟩

/-- The outgoing end as a point of the right away piece. -/
public def outgoingBoundaryInRightAway (x : M₂) : rightAwaySource B₁₂ :=
  ⟨B₁₂.outgoing.inclusion x, by
    rintro ⟨y, hy⟩
    exact Set.disjoint_left.1 B₁₂.ends_disjoint ⟨y, hy⟩ ⟨x, rfl⟩⟩

/-- The only boundary remaining in the left away piece is the incoming end. -/
public theorem boundary_leftAwaySource :
    (I.prod (𝓡∂ 1)).boundary (leftAwaySource B₀₁) =
      Set.range (incomingBoundaryInLeftAway B₀₁) := by
  rw [ModelWithCorners.boundary_open]
  ext w
  rw [B₀₁.boundary_eq]
  constructor
  · rintro (⟨x, hx⟩ | ⟨y, hy⟩)
    · refine ⟨x, Subtype.ext hx⟩
    · exact False.elim (w.2 ⟨y, hy⟩)
  · rintro ⟨x, hx⟩
    left
    exact ⟨x, congrArg Subtype.val hx⟩

/-- The only boundary remaining in the right away piece is the outgoing end. -/
public theorem boundary_rightAwaySource :
    (I.prod (𝓡∂ 1)).boundary (rightAwaySource B₁₂) =
      Set.range (outgoingBoundaryInRightAway B₁₂) := by
  rw [ModelWithCorners.boundary_open]
  ext w
  rw [B₁₂.boundary_eq]
  constructor
  · rintro (⟨x, hx⟩ | ⟨y, hy⟩)
    · exact False.elim (w.2 ⟨x, hx⟩)
    · refine ⟨y, Subtype.ext hy⟩
  · rintro ⟨y, hy⟩
    right
    exact ⟨y, congrArg Subtype.val hy⟩

/-- The signed seam cylinder is boundaryless. -/
public theorem boundary_seamPiece :
    (I.prod (𝓡∂ 1)).boundary (M₁ × OpenCollarParameter) = ∅ :=
  ModelWithCorners.Boundaryless.boundary_eq_empty

end QuotientGluing
end SmoothCollaredBordism
end SphereSixComplex
