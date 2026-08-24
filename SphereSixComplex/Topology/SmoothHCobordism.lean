module

public import SphereSixComplex.Topology.CollaredBordismGluing
public import SphereSixComplex.Topology.CylinderHomotopy
public import SphereSixComplex.Topology.MapHomotopyEquivalence

/-!
# Smooth h-cobordisms

An h-cobordism is a smooth collared bordism for which both *actual end-inclusion maps* are
homotopy equivalences.  The condition uses `IsHomotopyEquivalence f`, which retains equality with
the specified map; a mere type-level `Nonempty (M ≃ₕ W)` would not be sufficient.

Reversal and cylinders are explicit.  Transitivity is proved by the three-piece smooth collar
gluing: two away-from-the-seam pieces and a signed open bicollar carry compatible smooth charts,
and collar homotopy extension identifies the outer inclusions as homotopy equivalences.
-/

@[expose] public section

noncomputable section

open Function
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

universe uE uH uW uM

namespace SmoothCollaredBordism

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M₀ M₁ : Type*}
  [TopologicalSpace M₀] [T2Space M₀] [SecondCountableTopology M₀]
  [ChartedSpace H M₀] [IsManifold I ∞ M₀] [CompactSpace M₀]
  [BoundarylessManifold I M₀]
  [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
  [ChartedSpace H M₁] [IsManifold I ∞ M₁] [CompactSpace M₁]
  [BoundarylessManifold I M₁]

/-- Both specified end inclusions of a collared bordism are homotopy equivalences. -/
public def IsHCobordism (B : SmoothCollaredBordism I M₀ M₁) : Prop :=
  IsHomotopyEquivalence B.incoming.inclusion ∧
    IsHomotopyEquivalence B.outgoing.inclusion

/-- Reversing an h-cobordism preserves its two end conditions. -/
public theorem IsHCobordism.reverse {B : SmoothCollaredBordism I M₀ M₁}
    (hB : B.IsHCobordism) : B.reverse.IsHCobordism :=
  ⟨hB.2, hB.1⟩

section Cylinder

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [BoundarylessManifold I M]

/-- The standard cylinder is an h-cobordism. -/
public theorem cylinder_isHCobordism :
    (cylinder (I := I) (M := M)).IsHCobordism := by
  unfold IsHCobordism cylinder
  constructor
  · refine ⟨cylinderZeroHomotopyEquiv M, ?_⟩
    funext x
    rw [cylinderIncomingCollar_inclusion]
    rw [cylinderZeroHomotopyEquiv_toFun]
    exact Prod.ext rfl (Subtype.ext (by norm_num [collarStart]))
  · refine ⟨cylinderOneHomotopyEquiv M, ?_⟩
    funext x
    rw [cylinderOutgoingCollar_inclusion]
    rw [cylinderOneHomotopyEquiv_toFun]
    exact Prod.ext rfl (Subtype.ext (by norm_num [collarFinish]))

end Cylinder

end SmoothCollaredBordism

section Relation

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)

/-- Existence of one genuine smooth h-cobordism.  Endpoints and the bordism carrier are kept in a
common universe so the cylinder proves reflexivity without universe lifting. -/
public def SmoothHCobordant (M₀ M₁ : Type uM)
    [TopologicalSpace M₀] [T2Space M₀] [SecondCountableTopology M₀]
    [ChartedSpace H M₀] [IsManifold I ∞ M₀] [CompactSpace M₀]
    [BoundarylessManifold I M₀]
    [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [ChartedSpace H M₁] [IsManifold I ∞ M₁] [CompactSpace M₁]
    [BoundarylessManifold I M₁] : Prop :=
  ∃ B : SmoothCollaredBordism.{uE, uH, uM} I M₀ M₁, B.IsHCobordism

namespace SmoothHCobordant

variable {M₀ M₁ M₂ : Type uM}
  [TopologicalSpace M₀] [T2Space M₀] [SecondCountableTopology M₀]
  [ChartedSpace H M₀] [IsManifold I ∞ M₀] [CompactSpace M₀]
  [BoundarylessManifold I M₀]
  [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
  [ChartedSpace H M₁] [IsManifold I ∞ M₁] [CompactSpace M₁]
  [BoundarylessManifold I M₁]
  [TopologicalSpace M₂] [T2Space M₂] [SecondCountableTopology M₂]
  [ChartedSpace H M₂] [IsManifold I ∞ M₂] [CompactSpace M₂]
  [BoundarylessManifold I M₂]

/-- H-cobordism is reflexive, witnessed by the explicit cylinder. -/
public theorem refl : SmoothHCobordant I M₀ M₀ :=
  ⟨SmoothCollaredBordism.cylinder, SmoothCollaredBordism.cylinder_isHCobordism⟩

/-- H-cobordism is symmetric, witnessed by reversal. -/
public theorem symm (h : SmoothHCobordant I M₀ M₁) :
    SmoothHCobordant I M₁ M₀ := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B.reverse, hB.reverse⟩

/-- The relation-level gluing proposition consumed by transitivity. -/
public def GluingStatement : Prop :=
  ∀ (B₀₁ : SmoothCollaredBordism.{uE, uH, uM} I M₀ M₁)
    (B₁₂ : SmoothCollaredBordism.{uE, uH, uM} I M₁ M₂),
    B₀₁.IsHCobordism → B₁₂.IsHCobordism →
      ∃ B₀₂ : SmoothCollaredBordism.{uE, uH, uM} I M₀ M₂,
        B₀₂.IsHCobordism

/-- The constructed three-piece gluing proves the relation-level gluing statement. -/
public theorem gluingStatement : GluingStatement I (M₀ := M₀) (M₁ := M₁) (M₂ := M₂) := by
  intro B₀₁ B₁₂ hB₀₁ hB₁₂
  let B₀₂ := SmoothCollaredBordism.QuotientGluing.smoothGlue B₀₁ B₁₂
  refine ⟨B₀₂, ?_⟩
  constructor
  · exact SmoothCollaredBordism.QuotientGluing.smoothGlue_incoming_isHomotopyEquivalence
      B₀₁ B₁₂ hB₀₁.1 hB₁₂.1
  · exact SmoothCollaredBordism.QuotientGluing.smoothGlue_outgoing_isHomotopyEquivalence
      B₀₁ B₁₂ hB₀₁.2 hB₁₂.2

/-- A supplied gluing statement gives transitivity.  The unconditional theorem below applies the
constructed statement `gluingStatement`. -/
public theorem trans_of_gluing (hglue : GluingStatement I (M₀ := M₀)
    (M₁ := M₁) (M₂ := M₂))
    (h₀₁ : SmoothHCobordant I M₀ M₁) (h₁₂ : SmoothHCobordant I M₁ M₂) :
    SmoothHCobordant I M₀ M₂ := by
  obtain ⟨B₀₁, hB₀₁⟩ := h₀₁
  obtain ⟨B₁₂, hB₁₂⟩ := h₁₂
  exact hglue B₀₁ B₁₂ hB₀₁ hB₁₂

/-- Smooth h-cobordism is transitive, witnessed by the constructed smooth collar gluing. -/
public theorem trans (h₀₁ : SmoothHCobordant I M₀ M₁)
    (h₁₂ : SmoothHCobordant I M₁ M₂) :
    SmoothHCobordant I M₀ M₂ :=
  trans_of_gluing I (gluingStatement I) h₀₁ h₁₂

end SmoothHCobordant

end Relation

end SphereSixComplex
