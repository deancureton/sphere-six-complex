module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homotopy.StarConvexComplement
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeHomeomorphism
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeComparison
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainHomotopy

@[expose] public section

noncomputable section

open CategoryTheory ContinuousMap Set

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integralSingularChainMap_quasiIso_of_homotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    QuasiIso (integralSingularChainMap e.toFun) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact (integralSingularHomologyHomotopyEquiv n e).bijective

theorem integralBoundedStarConvexToLocalChainMap_quasiIso {K : Set E} {c : E}
    (hc : c ∈ K) (hs : StarConvex ℝ c K) (hK : Bornology.IsBounded K) :
    QuasiIso (integralRelativeChainMap (ContinuousMap.id E)
      (compl_subset_compl.mpr (singleton_subset_iff.mpr hc))) := by
  have hA : QuasiIso (integralSingularChainMap
      (singularPairRestriction (ContinuousMap.id E)
        (compl_subset_compl.mpr (singleton_subset_iff.mpr hc)))) :=
    integralSingularChainMap_quasiIso_of_homotopyEquiv
      (boundedStarConvexComplementHomotopyEquiv hc hs hK)
  have hE : QuasiIso (integralSingularChainMap (ContinuousMap.id E)) :=
    integralSingularChainMap_quasiIso_of_homotopyEquiv (ContinuousMap.HomotopyEquiv.refl E)
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (integralRelativeSequenceMap (ContinuousMap.id E)
      (compl_subset_compl.mpr (singleton_subset_iff.mpr hc)))
    (integralRelativeChainSequence_shortExact Kᶜ)
    (integralRelativeChainSequence_shortExact ({c}ᶜ : Set E)) hA hE

def integralBoundedStarConvexLocalHomologyIso (n : ℕ) {K : Set E} {c : E}
    (hc : c ∈ K) (hs : StarConvex ℝ c K) (hK : Bornology.IsBounded K) :
    integralRelativeHomology n Kᶜ ≅ integralLocalHomology n c := by
  let := integralBoundedStarConvexToLocalChainMap_quasiIso hc hs hK
  exact asIso (HomologicalComplex.homologyMap
    (integralRelativeChainMap (ContinuousMap.id E)
      (compl_subset_compl.mpr (singleton_subset_iff.mpr hc))) n)

theorem integralBoundedStarConvexLocalHomologyIso_hom (n : ℕ) {K : Set E} {c : E}
    (hc : c ∈ K) (hs : StarConvex ℝ c K) (hK : Bornology.IsBounded K) :
    (integralBoundedStarConvexLocalHomologyIso n hc hs hK).hom.hom =
      integralRelativeHomologyMap n (ContinuousMap.id E)
        (show Kᶜ ⊆ ({c}ᶜ : Set E) from fun _ hx h => hx (h.symm ▸ hc)) := rfl

theorem integralRelativeCohomologyMap_boundedStarConvex_bijective
    (n : ℕ) {K : Set E} {c : E}
    (hc : c ∈ K) (hs : StarConvex ℝ c K) (hK : Bornology.IsBounded K) :
    Function.Bijective (integralRelativeCohomologyMap n (ContinuousMap.id E)
      (compl_subset_compl.mpr (singleton_subset_iff.mpr hc))) := by
  let hf : MapsTo (ContinuousMap.id E) Kᶜ ({c}ᶜ : Set E) :=
    compl_subset_compl.mpr (singleton_subset_iff.mpr hc)
  let e := boundedStarConvexComplementHomotopyEquiv hc hs hK
  have he : singularPairRestriction (ContinuousMap.id E) hf = e.toFun := by
    rw [boundedStarConvexComplementHomotopyEquiv_toFun]
    rfl
  change Function.Bijective (integralRelativeCohomologyMap n (ContinuousMap.id E) hf)
  apply integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
  · intro k
    rw [integralSingularCohomologyMap_id]
    exact Function.bijective_id
  · intro k
    rw [he]
    exact integralSingularCohomologyMap_bijective_of_homotopyEquiv e k

end DifferentialGeometry.Topology

end
