module

public import SphereSixComplex.Topology.CollaredBordismOpenPresentation
public import SphereSixComplex.Topology.SmoothOpenGluing

/-!
# Topological and charted structures on the three-piece bordism gluing

This file installs the structures which do not depend on checking smooth transitions.  The
Hausdorff, compact, and second-countable properties are transported across the canonical
homeomorphism to the direct compact-Hausdorff quotient.  The charted-space structure is the one
obtained by pushing the charts of the three source pieces through their open embeddings.
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

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every source in the three-piece cover carries the ambient bordism model's charted
structure. -/
public instance (i : OpenPieceIndex) :
    ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) (OpenPiece B₀₁ B₁₂ i) := by
  cases i <;> infer_instance

/-- Every source in the three-piece cover is an infinitely smooth manifold with corners. -/
public instance (i : OpenPieceIndex) :
    IsManifold (I.prod (𝓡∂ 1)) ∞ (OpenPiece B₀₁ B₁₂ i) := by
  cases i <;> infer_instance

/-- The same piecewise charted-space family, with its domain displayed through the gluing data.
This explicit bridge avoids relying on reduction of the gluing constructor during typeclass
search. -/
@[instance_reducible]
public noncomputable def openPresentationPieceChartedSpaces :
    (i : (openPresentation B₀₁ B₁₂).J) →
      ChartedSpace (ModelProd H (EuclideanHalfSpace 1))
        ((openPresentation B₀₁ B₁₂).U i) := by
  intro i
  change OpenPieceIndex at i
  change ChartedSpace (ModelProd H (EuclideanHalfSpace 1))
    (OpenPiece B₀₁ B₁₂ i)
  exact inferInstance

/-- The charted-space structure obtained from the preferred charts on all three open pieces. -/
public noncomputable instance instChartedSpaceOpenGluedCarrier :
    ChartedSpace (ModelProd H (EuclideanHalfSpace 1))
      (OpenGluedCarrier B₀₁ B₁₂) :=
  @openGluingChartedSpace _ _
    (openPresentation B₀₁ B₁₂)
    (openPresentationPieceChartedSpaces B₀₁ B₁₂)

/-- The abstract open gluing is Hausdorff because it is homeomorphic to the direct quotient. -/
public noncomputable instance instT2SpaceOpenGluedCarrier :
    T2Space (OpenGluedCarrier B₀₁ B₁₂) :=
  (openPresentationHomeomorph B₀₁ B₁₂).symm.t2Space

/-- The abstract open gluing is compact because it is homeomorphic to the direct quotient. -/
public noncomputable instance instCompactSpaceOpenGluedCarrier :
    CompactSpace (OpenGluedCarrier B₀₁ B₁₂) :=
  (openPresentationHomeomorph B₀₁ B₁₂).symm.compactSpace

/-- The abstract open gluing is second countable because it is homeomorphic to the direct
quotient. -/
public noncomputable instance instSecondCountableTopologyOpenGluedCarrier :
    SecondCountableTopology (OpenGluedCarrier B₀₁ B₁₂) :=
  (openPresentationHomeomorph B₀₁ B₁₂).secondCountableTopology

end QuotientGluing
end SmoothCollaredBordism
end SphereSixComplex
