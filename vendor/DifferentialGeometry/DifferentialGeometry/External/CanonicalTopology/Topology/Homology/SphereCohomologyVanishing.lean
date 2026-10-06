module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CohomologyContractibleCover
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanLocalVanishing

@[expose] public section

noncomputable section

universe u

namespace DifferentialGeometry.Topology

open Metric Module Set

private theorem integralSphereCohomology_one_subsingleton
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : 2 < finrank ℝ E) :
    Subsingleton (integralSingularCohomology 1 (sphere (0 : E) 1)) := by
  let v := unitSpherePointOfFinrankPos (E := E) (by omega)
  let _ := spherePuncture_contractible v
  let _ := spherePuncture_contractible (-v)
  let V := (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ
  have hV : 1 < finrank ℝ V := by
    have h := unitSpherePoleHyperplane_finrank (finrank ℝ E - 1) (by omega) (-v)
    change 1 < finrank ℝ (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ
    omega
  let _ := puncturedSpace_pathConnected_of_finrank V hV
  let _ : PathConnectedSpace
      (subspaceIntersection ({v}ᶜ : Set (sphere (0 : E) 1)) {-v}ᶜ) :=
    (sphereDoublePunctureHomeomorph v).symm.surjective.pathConnectedSpace
      (sphereDoublePunctureHomeomorph v).symm.continuous
  let _ := integralRelativeCohomology_one_subsingleton_of_contractibleSpace_of_pathConnectedSpace
    (subspaceIntersection ({v}ᶜ : Set (sphere (0 : E) 1)) {-v}ᶜ)
  have hi := (integralRelativeCohomologyMap_openExcision 1 {v}ᶜ {-v}ᶜ
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v)).injective
  let _ : Subsingleton (integralRelativeCohomology 1 ({v}ᶜ : Set (sphere (0 : E) 1))) :=
    ⟨fun α β => hi (Subsingleton.elim _ _)⟩
  have hs := (integralRelativeToAbsoluteCohomology_bijective_of_contractibleSpace
    0 ({v}ᶜ : Set (sphere (0 : E) 1))).surjective
  have hz (α : integralSingularCohomology 1 (sphere (0 : E) 1)) : α = 0 := by
    obtain ⟨β, rfl⟩ := hs α
    rw [Subsingleton.elim β 0, map_zero]
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

theorem integralSphereCohomology_subsingleton (n k : ℕ) (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : finrank ℝ E = n + 1) (hk : k ≠ 0) (hkn : k ≠ n) :
    Subsingleton (integralSingularCohomology k (sphere (0 : E) 1)) := by
  induction n generalizing E k with
  | zero =>
      let v := unitSpherePointOfFinrankPos (E := E) (by omega)
      let _ := oneDimUnitSphere_finite hd v
      exact integralSingularCohomology_subsingleton_of_totallyDisconnectedSpace _ k hk
  | succ n ih =>
      let v := unitSpherePointOfFinrankPos (E := E) (by omega)
      have hp := unitSpherePoleHyperplane_finrank (n + 1) hd (-v)
      cases k with
      | zero => exact (hk rfl).elim
      | succ k =>
          cases k with
          | zero => exact integralSphereCohomology_one_subsingleton E (by omega)
          | succ k =>
              let _ := ih (k + 1) (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ hp
                (by omega) (by omega)
              let e := spherePoleIntersectionHomotopyEquiv v
              have hs := (integralSingularCohomologyMap_bijective_of_homotopyEquiv
                e (k + 1)).surjective
              have hz (α : integralSingularCohomology (k + 1)
                  (subspaceIntersection ({v}ᶜ : Set (sphere (0 : E) 1)) {-v}ᶜ)) : α = 0 := by
                obtain ⟨β, rfl⟩ := hs α
                rw [Subsingleton.elim β 0, map_zero]
              let _ : Subsingleton (integralSingularCohomology (k + 1)
                  (subspaceIntersection ({v}ᶜ : Set (sphere (0 : E) 1)) {-v}ᶜ)) :=
                ⟨fun α β => (hz α).trans (hz β).symm⟩
              let _ := spherePuncture_contractible v
              let _ := spherePuncture_contractible (-v)
              exact ⟨fun α β => (integralCohomologyContractibleCoverEquiv k {v}ᶜ {-v}ᶜ
                isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v)).injective
                  (Subsingleton.elim _ _)⟩

end DifferentialGeometry.Topology

end
