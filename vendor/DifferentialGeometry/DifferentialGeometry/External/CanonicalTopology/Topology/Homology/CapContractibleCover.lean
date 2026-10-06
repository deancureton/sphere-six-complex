module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CohomologyContractibleCover
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ContractiblePair
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCapCohomologyConnecting
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ZeroAugmentation

@[expose] public section

noncomputable section

universe u

namespace DifferentialGeometry.Topology

theorem integralSingularCohomologyCapProduct_zero_contractibleCover
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (α : integralSingularCohomology (n + 2) X)
    (c : integralSingularHomology (n + 2) X) :
    integralSingularCohomologyCapProduct (n + 2) 0 α c =
      integralSingularHomologyMap 0 (singularSubspaceInclusion B)
        (integralSingularHomologyMap 0 (singularSubspaceInclusion (subspaceIntersection A B))
          (integralSingularCohomologyCapProduct (n + 1) 0
            (integralCohomologyContractibleCoverEquiv n A B hA hB hcover α)
            (integralHomologyContractibleCoverEquiv n A B hA hB hcover c))) := by
  let eA := LinearEquiv.ofBijective (integralRelativeToAbsoluteCohomology (n + 2) A)
    (integralRelativeToAbsoluteCohomology_bijective_of_contractibleSpace (n + 1) A)
  let eB := (integralRelativeOpenExcisionIso (n + 2) A B hA hB hcover).toLinearEquiv
  let a := eA.symm α
  let b := eB.symm (integralAbsoluteToRelative (n + 2) A c)
  have ha : integralRelativeToAbsoluteCohomology (n + 2) A a = α :=
    eA.apply_symm_apply α
  have hb : integralRelativeHomologyMap (n + 2) (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B) b = integralAbsoluteToRelative (n + 2) A c :=
    eB.apply_symm_apply _
  have he : integralRelativeCohomologyMap (n + 2) (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B) a =
      integralRelativeCohomologyConnecting (n + 1) (subspaceIntersection A B)
        (integralCohomologyContractibleCoverEquiv n A B hA hB hcover α) := by
    rw [← ha]
    exact (integralCohomologyContractibleCoverEquiv_connecting n A B hA hB hcover a).symm
  have hc : integralHomologyContractibleCoverEquiv n A B hA hB hcover c =
      integralRelativeConnecting (n + 1) (subspaceIntersection A B) b := rfl
  calc
    integralSingularCohomologyCapProduct (n + 2) 0 α c =
        integralRelativeCohomologyCapToAbsolute A (n + 2) 0 a
          (integralAbsoluteToRelative (n + 2) A c) := by
      rw [integralRelativeCohomologyCapToAbsolute_absoluteToRelative, ha]
    _ = integralSingularHomologyMap 0 (singularSubspaceInclusion B)
        (integralRelativeCohomologyCapToAbsolute (subspaceIntersection A B) (n + 2) 0
          (integralRelativeCohomologyMap (n + 2) (singularSubspaceInclusion B)
            (subspaceIntersection_mapsTo A B) a) b) := by
      rw [integralRelativeCohomologyCapToAbsolute_natural, hb]
    _ = _ := by
      rw [he, hc]
      congr 1
      have h := integralRelativeCohomologyCapToAbsolute_connecting (subspaceIntersection A B)
        (n + 1) 0 (integralCohomologyContractibleCoverEquiv n A B hA hB hcover α) b
      exact h


theorem integralZeroAugmentation_cap_contractibleCover
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (α : integralSingularCohomology (n + 2) X)
    (c : integralSingularHomology (n + 2) X) :
    integralZeroAugmentation (integralSingularCohomologyCapProduct (n + 2) 0 α c) =
      integralZeroAugmentation (integralSingularCohomologyCapProduct (n + 1) 0
        (integralCohomologyContractibleCoverEquiv n A B hA hB hcover α)
        (integralHomologyContractibleCoverEquiv n A B hA hB hcover c)) := by
  rw [integralSingularCohomologyCapProduct_zero_contractibleCover n A B hA hB hcover]
  calc
    _ = integralZeroAugmentation
        (integralSingularHomologyMap 0 (singularSubspaceInclusion (subspaceIntersection A B))
          (integralSingularCohomologyCapProduct (n + 1) 0
            (integralCohomologyContractibleCoverEquiv n A B hA hB hcover α)
            (integralHomologyContractibleCoverEquiv n A B hA hB hcover c))) :=
      LinearMap.congr_fun (integralZeroAugmentation_natural (singularSubspaceInclusion B)) _
    _ = _ := LinearMap.congr_fun
      (integralZeroAugmentation_natural (singularSubspaceInclusion (subspaceIntersection A B))) _

theorem integralZeroAugmentation_cap_bijective_contractibleCover_iff
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (c : integralSingularHomology (n + 2) X) :
    Function.Bijective (fun α : integralSingularCohomology (n + 2) X =>
      integralZeroAugmentation (integralSingularCohomologyCapProduct (n + 2) 0 α c)) ↔
      Function.Bijective (fun β : integralSingularCohomology (n + 1) (subspaceIntersection A B) =>
        integralZeroAugmentation (integralSingularCohomologyCapProduct (n + 1) 0 β
          (integralHomologyContractibleCoverEquiv n A B hA hB hcover c))) := by
  let e := integralCohomologyContractibleCoverEquiv n A B hA hB hcover
  let f := fun β : integralSingularCohomology (n + 1) (subspaceIntersection A B) =>
    integralZeroAugmentation (integralSingularCohomologyCapProduct (n + 1) 0 β
      (integralHomologyContractibleCoverEquiv n A B hA hB hcover c))
  have heq : (fun α : integralSingularCohomology (n + 2) X =>
      integralZeroAugmentation (integralSingularCohomologyCapProduct (n + 2) 0 α c)) = f ∘ e :=
    funext fun α => integralZeroAugmentation_cap_contractibleCover n A B hA hB hcover α c
  rw [heq]
  exact Function.Bijective.of_comp_iff f e.bijective


end DifferentialGeometry.Topology

end
