module

public import SphereSixComplex.Topology.CollarHEP
public import SphereSixComplex.Topology.CollaredBordismPushoutHomotopy
public import SphereSixComplex.Topology.CollaredBordismSmoothGluing
public import SphereSixComplex.Topology.HomeomorphHomotopyEquivalence

/-!
# Homotopy equivalences of the smooth gluing's outer inclusions

The original seam inclusions have the homotopy extension property by their explicit collars.
Together with the h-cobordism hypotheses, relative strictification turns each into a strong
deformation retract.  Pushout homotopy invariance then proves the two outer quotient maps are
homotopy equivalences; the canonical homeomorphism transfers those results to the smooth
three-piece carrier.
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

/-- The incoming outer inclusion of the smooth gluing is a homotopy equivalence. -/
public theorem smoothIncomingInclusion_isHomotopyEquivalence
    (hIncoming₀₁ : IsHomotopyEquivalence B₀₁.incoming.inclusion)
    (hIncoming₁₂ : IsHomotopyEquivalence B₁₂.incoming.inclusion) :
    IsHomotopyEquivalence (smoothIncomingInclusion B₀₁ B₁₂) := by
  obtain ⟨D₁₂⟩ := B₁₂.incoming.exists_ambientStrongDeformationRetract hIncoming₁₂
  have hquotient : IsHomotopyEquivalence (incomingInclusion B₀₁ B₁₂) :=
    incomingInclusion_isHomotopyEquivalence_of_strong B₀₁ B₁₂ D₁₂ hIncoming₀₁
  apply (hquotient.postcomp_homeomorph (openPresentationHomeomorph B₀₁ B₁₂).symm).congr
  funext x
  apply (openPresentationHomeomorph B₀₁ B₁₂).injective
  change openPresentationHomeomorph B₀₁ B₁₂
      ((openPresentationHomeomorph B₀₁ B₁₂).symm (incomingInclusion B₀₁ B₁₂ x)) = _
  rw [Homeomorph.apply_symm_apply, openPresentationHomeomorph_smoothIncomingInclusion]

/-- The outgoing outer inclusion of the smooth gluing is a homotopy equivalence. -/
public theorem smoothOutgoingInclusion_isHomotopyEquivalence
    (hOutgoing₀₁ : IsHomotopyEquivalence B₀₁.outgoing.inclusion)
    (hOutgoing₁₂ : IsHomotopyEquivalence B₁₂.outgoing.inclusion) :
    IsHomotopyEquivalence (smoothOutgoingInclusion B₀₁ B₁₂) := by
  obtain ⟨D₀₁⟩ := B₀₁.outgoing.exists_ambientStrongDeformationRetract hOutgoing₀₁
  have hquotient : IsHomotopyEquivalence (outgoingInclusion B₀₁ B₁₂) :=
    outgoingInclusion_isHomotopyEquivalence_of_strong B₀₁ B₁₂ D₀₁ hOutgoing₁₂
  apply (hquotient.postcomp_homeomorph (openPresentationHomeomorph B₀₁ B₁₂).symm).congr
  funext x
  apply (openPresentationHomeomorph B₀₁ B₁₂).injective
  change openPresentationHomeomorph B₀₁ B₁₂
      ((openPresentationHomeomorph B₀₁ B₁₂).symm (outgoingInclusion B₀₁ B₁₂ x)) = _
  rw [Homeomorph.apply_symm_apply, openPresentationHomeomorph_smoothOutgoingInclusion]

end QuotientGluing
end SmoothCollaredBordism
end SphereSixComplex
