module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RadialHomotopy
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeComparison
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainHomotopy

@[expose] public section

universe v

namespace DifferentialGeometry.Topology

open Set Metric

theorem exists_integralRelativeCohomologyMap_sphere_puncture_bijective
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    ∃ h : MapsTo (ContinuousMap.id E) (sphere (0 : E) 1) ({0}ᶜ : Set E),
      Function.Bijective (integralRelativeCohomologyMap n (ContinuousMap.id E) h) := by
  have hf : MapsTo (ContinuousMap.id E) (sphere (0 : E) 1) ({0}ᶜ : Set E) := by
    intro x hx
    change x ∉ ({0} : Set E)
    intro h
    have he : x = 0 := mem_singleton_iff.mp h
    subst x
    simp at hx
  let e := (puncturedSpaceSphereHomotopyEquiv E).symm
  have he : singularPairRestriction (ContinuousMap.id E) hf = e.toFun := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact (puncturedSpaceSphereHomotopyEquiv_inv_apply E x).symm
  refine ⟨hf, ?_⟩
  · apply integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
    · intro k
      rw [integralSingularCohomologyMap_id]
      exact Function.bijective_id
    · intro k
      rw [he]
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv e k

end DifferentialGeometry.Topology
