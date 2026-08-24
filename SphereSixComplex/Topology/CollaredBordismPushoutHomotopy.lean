module

public import SphereSixComplex.Topology.ClosedEmbeddingPushout
public import SphereSixComplex.Topology.CollaredBordismQuotient
public import SphereSixComplex.Topology.CollarHomotopyExtension

/-!
# Homotopy equivalences of the outer maps in a collared pushout

Strong deformation-retract data for either seam inclusion makes the opposite summand map into
the direct glued quotient a specified homotopy equivalence.  Combining this with the original
outer-end homotopy equivalences gives the two end conditions for the composite.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousMap Function Set Topology TopologicalSpace
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

/-- The explicit quotient carrier as the categorical pushout of the two seam inclusions. -/
public def glueHomeomorphPushout :
    Glue B₀₁ B₁₂ ≃ₜ
      (pushout (collarAmbientZeroSection B₀₁.outgoing)
        (collarAmbientZeroSection B₁₂.incoming) : TopCat) :=
  ClosedEmbeddingGluing.sumGlueHomeomorphPushout
    B₀₁.outgoing.inclusion B₁₂.incoming.inclusion
    B₀₁.outgoing.inclusion_isEmbedding.injective
    B₁₂.incoming.inclusion_isEmbedding.injective
    B₀₁.outgoing.inclusion_contMDiff.continuous
    B₁₂.incoming.inclusion_contMDiff.continuous

@[simp]
public theorem glueHomeomorphPushout_left (w : B₀₁.W) :
    glueHomeomorphPushout B₀₁ B₁₂ (toGlueLeft B₀₁ B₁₂ w) =
      pushout.inl (collarAmbientZeroSection B₀₁.outgoing)
        (collarAmbientZeroSection B₁₂.incoming) w :=
  rfl

@[simp]
public theorem glueHomeomorphPushout_right (w : B₁₂.W) :
    glueHomeomorphPushout B₀₁ B₁₂ (toGlueRight B₀₁ B₁₂ w) =
      pushout.inr (collarAmbientZeroSection B₀₁.outgoing)
        (collarAmbientZeroSection B₁₂.incoming) w :=
  rfl

@[simp]
public theorem glueHomeomorphPushout_symm_inl (w : B₀₁.W) :
    (glueHomeomorphPushout B₀₁ B₁₂).symm
        (pushout.inl (collarAmbientZeroSection B₀₁.outgoing)
          (collarAmbientZeroSection B₁₂.incoming) w) =
      toGlueLeft B₀₁ B₁₂ w := by
  apply (glueHomeomorphPushout B₀₁ B₁₂).injective
  rw [Homeomorph.apply_symm_apply, glueHomeomorphPushout_left]

@[simp]
public theorem glueHomeomorphPushout_symm_inr (w : B₁₂.W) :
    (glueHomeomorphPushout B₀₁ B₁₂).symm
        (pushout.inr (collarAmbientZeroSection B₀₁.outgoing)
          (collarAmbientZeroSection B₁₂.incoming) w) =
      toGlueRight B₀₁ B₁₂ w := by
  apply (glueHomeomorphPushout B₀₁ B₁₂).injective
  rw [Homeomorph.apply_symm_apply, glueHomeomorphPushout_right]

/-- If the left seam inclusion is a strong deformation retract, the whole right summand maps
homotopy-equivalently into the explicit quotient. -/
public theorem toGlueRight_isHomotopyEquivalence_of_strong
    (D : TopCat.StrongDeformationRetractData
      (collarAmbientZeroSection B₀₁.outgoing)) :
    IsHomotopyEquivalence (toGlueRight B₀₁ B₁₂) := by
  let eP :=
    D.pushoutInrHomotopyEquiv (collarAmbientZeroSection B₁₂.incoming)
  let eQ :=
    eP.trans (glueHomeomorphPushout B₀₁ B₁₂).symm.toHomotopyEquiv
  refine ⟨eQ, ?_⟩
  funext w
  exact glueHomeomorphPushout_symm_inr B₀₁ B₁₂ w

/-- If the right seam inclusion is a strong deformation retract, the whole left summand maps
homotopy-equivalently into the explicit quotient. -/
public theorem toGlueLeft_isHomotopyEquivalence_of_strong
    (D : TopCat.StrongDeformationRetractData
      (collarAmbientZeroSection B₁₂.incoming)) :
    IsHomotopyEquivalence (toGlueLeft B₀₁ B₁₂) := by
  let eP :=
    TopCat.StrongDeformationRetractData.pushoutInlHomotopyEquiv
      (i := collarAmbientZeroSection B₀₁.outgoing)
      (j := collarAmbientZeroSection B₁₂.incoming) D
  let eQ :=
    eP.trans (glueHomeomorphPushout B₀₁ B₁₂).symm.toHomotopyEquiv
  refine ⟨eQ, ?_⟩
  funext w
  change (glueHomeomorphPushout B₀₁ B₁₂).symm (eP w) =
    toGlueLeft B₀₁ B₁₂ w
  rw [TopCat.StrongDeformationRetractData.pushoutInlHomotopyEquiv_apply]
  exact glueHomeomorphPushout_symm_inl B₀₁ B₁₂ w

/-- The incoming outer inclusion is a homotopy equivalence once the right seam is strong and
the original incoming inclusion is. -/
public theorem incomingInclusion_isHomotopyEquivalence_of_strong
    (D : TopCat.StrongDeformationRetractData
      (collarAmbientZeroSection B₁₂.incoming))
    (hIncoming : IsHomotopyEquivalence B₀₁.incoming.inclusion) :
    IsHomotopyEquivalence (incomingInclusion B₀₁ B₁₂) := by
  exact (toGlueLeft_isHomotopyEquivalence_of_strong B₀₁ B₁₂ D).comp hIncoming

/-- The outgoing outer inclusion is a homotopy equivalence once the left seam is strong and
the original outgoing inclusion is. -/
public theorem outgoingInclusion_isHomotopyEquivalence_of_strong
    (D : TopCat.StrongDeformationRetractData
      (collarAmbientZeroSection B₀₁.outgoing))
    (hOutgoing : IsHomotopyEquivalence B₁₂.outgoing.inclusion) :
    IsHomotopyEquivalence (outgoingInclusion B₀₁ B₁₂) := by
  exact (toGlueRight_isHomotopyEquivalence_of_strong B₀₁ B₁₂ D).comp hOutgoing

end QuotientGluing
end SmoothCollaredBordism
end SphereSixComplex
