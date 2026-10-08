module

public import Mathlib.Topology.Covering.Quotient

open Topology

namespace Topology

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [Group G] [MulAction G E]

/-- A free properly discontinuous action whose orbits are exactly the fibres of a quotient map
produces a quotient covering map. -/
public theorem isQuotientCoveringMap_of_properlyDiscontinuous
    [T2Space E] [LocallyCompactSpace E] [ContinuousConstSMul G E]
    [ProperlyDiscontinuousSMul G E] {p : E → X}
    (hquot : IsQuotientMap p)
    (hfiber : ∀ {e₁ e₂}, p e₁ = p e₂ ↔ e₁ ∈ MulAction.orbit G e₂)
    (hfree : ∀ g : G, ∀ e : E, g • e = e → g = 1) :
    IsQuotientCoveringMap p G where
  __ := hquot
  continuous_const_smul := continuous_const_smul
  apply_eq_iff_mem_orbit := hfiber
  disjoint e := by
    obtain ⟨U, hU, hdisjoint⟩ :=
      ProperlyDiscontinuousSMul.exists_nhds_disjoint_image G e
    refine ⟨U, hU, fun g hnonempty ↦ ?_⟩
    by_contra hg
    have hgmove : g • e ≠ e := fun hfix ↦ hg (hfree g e hfix)
    obtain ⟨z, hz₁, hz₂⟩ := hnonempty
    exact Set.disjoint_left.mp (hdisjoint g hgmove) hz₁ hz₂

/-- The typeclass form of the properly discontinuous quotient-covering constructor. -/
public theorem isQuotientCoveringMap_of_properlyDiscontinuous_of_isCancelSMul
    [T2Space E] [LocallyCompactSpace E] [ContinuousConstSMul G E]
    [ProperlyDiscontinuousSMul G E] [IsCancelSMul G E] {p : E → X}
    (hquot : IsQuotientMap p)
    (hfiber : ∀ {e₁ e₂}, p e₁ = p e₂ ↔ e₁ ∈ MulAction.orbit G e₂) :
    IsQuotientCoveringMap p G :=
  isQuotientCoveringMap_of_properlyDiscontinuous hquot hfiber fun g e hfix ↦ by
    apply (inferInstance : IsCancelSMul G E).right_cancel g 1 e
    simpa using hfix

end Topology
