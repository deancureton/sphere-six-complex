module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereCohomologyVanishing
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalStarConvex

@[expose] public section

noncomputable section

universe u

namespace DifferentialGeometry.Topology

open CategoryTheory Metric Module Set

theorem integralEuclideanRelativeCohomology_subsingleton
    (n k : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : finrank ℝ E = n + 2) (hk : k ≠ n + 2) :
    Subsingleton (integralRelativeCohomology k ({0}ᶜ : Set E)) := by
  let _ := puncturedSpace_pathConnected_of_finrank E (by omega)
  cases k with
  | zero =>
      exact integralRelativeCohomology_zero_subsingleton_of_pathConnectedSpace
        ({0}ᶜ : Set E) (nonempty_coe_sort.mp inferInstance)
  | succ k =>
      cases k with
      | zero =>
          exact integralRelativeCohomology_one_subsingleton_of_contractibleSpace_of_pathConnectedSpace
            ({0}ᶜ : Set E)
      | succ k =>
          let _ := integralSphereCohomology_subsingleton (n + 1) (k + 1) E hd (by omega) (by omega)
          let e := puncturedSpaceSphereHomotopyEquiv E
          have hs :=
            (integralRelativeCohomologyConnecting_bijective_of_contractibleSpace
              (k + 1) (by omega) ({0}ᶜ : Set E)).surjective.comp
                (integralSingularCohomologyMap_bijective_of_homotopyEquiv e (k + 1)).surjective
          have hz (α : integralRelativeCohomology (k + 2) ({0}ᶜ : Set E)) : α = 0 := by
            obtain ⟨β, rfl⟩ := hs α
            change integralRelativeCohomologyConnecting (k + 1) ({0}ᶜ : Set E)
              (integralSingularCohomologyMap (k + 1) e.toFun β) = 0
            rw [Subsingleton.elim β 0, map_zero, map_zero]
          exact ⟨fun α β => (hz α).trans (hz β).symm⟩

theorem integralBoundedStarConvexRelativeCohomology_subsingleton
    (n k : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : finrank ℝ E = n + 2) (hk : k ≠ n + 2)
    {K : Set E} (h0 : (0 : E) ∈ K) (hs : StarConvex ℝ 0 K) (hK : Bornology.IsBounded K) :
    Subsingleton (integralRelativeCohomology k Kᶜ) := by
  let _ := integralEuclideanRelativeCohomology_subsingleton n k E hd hk
  let hf : MapsTo (ContinuousMap.id E) Kᶜ ({0}ᶜ : Set E) :=
    compl_subset_compl.mpr (singleton_subset_iff.mpr h0)
  have hcoh : Function.Bijective (integralRelativeCohomologyMap k (ContinuousMap.id E) hf) :=
    integralRelativeCohomologyMap_boundedStarConvex_bijective k h0 hs hK
  have hz (α : integralRelativeCohomology k Kᶜ) : α = 0 := by
    obtain ⟨β, rfl⟩ := hcoh.surjective α
    rw [Subsingleton.elim β 0, map_zero]
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

end DifferentialGeometry.Topology

end
