module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereRank
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RadialCohomology
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TwoPointCapDuality

@[expose] public section

universe u

namespace DifferentialGeometry.Topology

open Set Metric

theorem exists_integralLocalHomology_cap_bijective_of_finrank_one
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (hd : Module.finrank ℝ E = 1) :
    ∃ c : integralRelativeHomology 1 ({0}ᶜ : Set E),
      Function.Bijective (fun α : integralRelativeCohomology 1 ({0}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) 1 0 α c) := by
  let v := unitSpherePointOfFinrankPos (E := E) (by omega)
  have hS : sphere (0 : E) 1 = ({-(v : E), (v : E)} : Set E) := by
    ext x
    constructor
    · intro hx
      rcases oneDimUnitSphere_eq_or_antipode hd v ⟨x, hx⟩ with h | h
      · exact mem_insert_of_mem _ (mem_singleton_iff.mpr (congrArg Subtype.val h))
      · exact mem_insert_iff.mpr (Or.inl (congrArg Subtype.val h))
    · intro hx
      rcases mem_insert_iff.mp hx with h | h
      · rw [h, mem_sphere_zero_iff_norm, norm_neg]
        exact norm_eq_of_mem_sphere v
      · rw [mem_singleton_iff.mp h]
        exact v.property
  have hcomparison := exists_integralRelativeCohomologyMap_sphere_puncture_bijective E 1
  rw [hS] at hcomparison
  obtain ⟨h, hcoh⟩ := hcomparison
  obtain ⟨c, ⟨_, hcap⟩, _⟩ := exists_unique_relative_pair_cap_bijective
    (-(v : E)) (v : E) (fun h => unitSphere_ne_antipode v (Subtype.ext h.symm))
  refine ⟨integralRelativeHomologyMap 1 (ContinuousMap.id E) h c, ?_⟩
  exact integralRelativeCohomologyCapToAbsolute_bijective_map 1 0 (ContinuousMap.id E) h
    (by rw [integralSingularHomologyMap_id]; exact Function.bijective_id) hcoh c hcap

end DifferentialGeometry.Topology
