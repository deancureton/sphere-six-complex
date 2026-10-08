module

public import ForMathlib.Topology.Covering.Quotient

public import ForMathlib.Geometry.Manifold.Quotient.DeckFundamentalGroup

/-!
# Marked loops for quotient covering maps

This module packages the properly-discontinuous-action constructor for quotient covering maps
and connects the existing projected-deck-path calculation to Mathlib's canonical
fundamental-group equivalence.
-/

@[expose] public section

open MulOpposite Topology

namespace SphereSixComplex.Topology.QuotientCoveringMarkedLoops

noncomputable section

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [Group G] [MulAction G E]

variable {p : E → X} (hp : IsQuotientCoveringMap p G)

/-- The existing projected-deck-path monodromy calculation expressed through the canonical
fundamental-group equivalence. -/
public theorem fundamentalGroupEquiv_projectedQuotientDeckPath
    [SimplyConnectedSpace E] (e : E) (g : G) (Γ : Path e (g • e)) :
    hp.fundamentalGroupEquiv ⟨e, rfl⟩
        (pathLoopClass
          (projectedQuotientDeckPath hp e g Γ)) =
      op g := by
  change hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩
      (pathLoopClass
        (projectedQuotientDeckPath hp e g Γ)) = op g
  exact fundamentalGroupToMulOpposite_projectedQuotientDeckPath
    hp e g Γ

end

end SphereSixComplex.Topology.QuotientCoveringMarkedLoops
