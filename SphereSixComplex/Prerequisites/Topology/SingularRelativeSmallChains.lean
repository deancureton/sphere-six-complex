module

public import SphereSixComplex.Prerequisites.Topology.SingularExcisionRefinement
public import SphereSixComplex.Prerequisites.Topology.RelativeSingularHomology
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace SphereSixComplex
variable {ι : Type} (X : TopCat) (U : ι → Set X) (i : ι)

public instance coverMemberToSmallIntegralSingularChains_mono :
    Mono (coverMemberToSmallIntegralSingularChains X U i) := by
  have hi : Mono (topologicalSubsetInclusion X (U i)) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  have hm : Mono (integralSingularChainMapObj (topologicalSubsetInclusion X (U i))) := by
    dsimp [integralSingularChainMapObj]
    infer_instance
  exact mono_of_mono_fac (coverMemberToSmallIntegralSingularChains_comp_inclusion X U i)

public def coverSmallRelativeShortComplex : ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (coverMemberToSmallIntegralSingularChains X U i)
    (cokernel.π (coverMemberToSmallIntegralSingularChains X U i)) (cokernel.condition _)

public theorem coverSmallRelativeShortComplex_shortExact :
    (coverSmallRelativeShortComplex X U i).ShortExact :=
  { exact := ShortComplex.exact_cokernel _
    mono_f := coverMemberToSmallIntegralSingularChains_mono X U i
    epi_g := by dsimp [coverSmallRelativeShortComplex]; infer_instance }

public def coverSmallRelativeComparison :
    (coverSmallRelativeShortComplex X U i).X₃ ⟶
      relativeIntegralSingularChainComplex (topologicalSubsetInclusion X (U i)) :=
  cokernel.map (coverMemberToSmallIntegralSingularChains X U i)
    (integralSingularChainMapObj (topologicalSubsetInclusion X (U i)))
    (𝟙 _) (coverSmallIntegralSingularChainInclusion X U)
    (by simpa only [Category.id_comp] using coverMemberToSmallIntegralSingularChains_comp_inclusion X U i)

public def coverSmallRelativeShortComplexComparison :
    coverSmallRelativeShortComplex X U i ⟶
      relativeIntegralSingularShortComplex (topologicalSubsetInclusion X (U i)) where
  τ₁ := 𝟙 _
  τ₂ := coverSmallIntegralSingularChainInclusion X U
  τ₃ := coverSmallRelativeComparison X U i
  comm₁₂ := by
    change 𝟙 _ ≫ integralSingularChainMapObj (topologicalSubsetInclusion X (U i)) =
      coverMemberToSmallIntegralSingularChains X U i ≫ coverSmallIntegralSingularChainInclusion X U
    rw [Category.id_comp]
    exact (coverMemberToSmallIntegralSingularChains_comp_inclusion X U i).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

public theorem coverSmallRelativeComparison_quasiIso
    (h : CoverSmallChainQuasiIsomorphism X U) : QuasiIso (coverSmallRelativeComparison X U i) := by
  let : Mono (topologicalSubsetInclusion X (U i)) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  apply HomologicalComplex.HomologySequence.quasiIso_τ₃
    (coverSmallRelativeShortComplexComparison X U i)
    (coverSmallRelativeShortComplex_shortExact X U i)
    (relativeIntegralSingularShortComplex_shortExact _)
  · change QuasiIso (𝟙 (integralSingularChainComplexObj (TopCat.of (U i))))
    infer_instance
  · exact h

public theorem coverSmallRelativeComparison_quasiIso_of_open_refinement
    {κ : Type} (V : κ → Set X) (r : κ → ι) (h : ∀ j, V j ⊆ U (r j))
    (hVopen : ∀ j, IsOpen (V j)) (hVcover : ⋃ j, V j = Set.univ) :
    QuasiIso (coverSmallRelativeComparison X U i) :=
  coverSmallRelativeComparison_quasiIso X U i
    (coverSmallChainQuasiIsomorphism_of_eventuallySmall X U
      (coverSmallEventuallySmall_of_refinement X V U r h
        (coverSmallAffineSubdivisionEventuallySmall_of_openCover X V hVopen hVcover)))

end SphereSixComplex
