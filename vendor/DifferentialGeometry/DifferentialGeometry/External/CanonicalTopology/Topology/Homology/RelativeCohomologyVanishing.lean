module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ConnectedZeroCohomology
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CohomologyVanishing
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCochains

@[expose] public section

noncomputable section

universe u

namespace DifferentialGeometry.Topology

theorem integralRelativeCohomologyConnecting_bijective
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X)
    [Subsingleton (integralSingularCohomology n X)]
    [Subsingleton (integralSingularCohomology (n + 1) X)] :
    Function.Bijective (integralRelativeCohomologyConnecting n A) := by
  have hi := integralRelativeCohomology_exact_subspace n A
  have hs := integralRelativeCohomology_exact_relative n A
  have hleft : integralSingularCohomologyMap n (singularSubspaceInclusion A) = 0 := by
    ext α
    rw [Subsingleton.elim α 0, map_zero]
    rfl
  have hright : integralRelativeToAbsoluteCohomology (n + 1) A = 0 := by
    ext α
    exact Subsingleton.elim _ _
  rw [hleft, LinearMap.exact_zero_iff_injective] at hi
  rw [hright, LinearMap.exact_zero_iff_surjective] at hs
  exact ⟨hi, hs⟩

theorem integralRelativeCohomologyConnecting_bijective_of_contractibleSpace
    {X : Type u} [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) (A : Set X) :
    Function.Bijective (integralRelativeCohomologyConnecting n A) := by
  let _ := integralSingularCohomology_subsingleton_of_contractibleSpace X n hn
  let _ := integralSingularCohomology_subsingleton_of_contractibleSpace X (n + 1)
    (Nat.succ_ne_zero n)
  exact integralRelativeCohomologyConnecting_bijective n A

theorem integralRelativeCohomology_subsingleton_of_contractibleSpace_of_totallyDisconnectedSpace
    {X : Type u} [TopologicalSpace X] [ContractibleSpace X]
    (A : Set X) [TotallyDisconnectedSpace A] (n : ℕ) (hn : 1 < n) :
    Subsingleton (integralRelativeCohomology n A) := by
  have hdegree : n - 1 + 1 = n := by omega
  rw [← hdegree]
  let _ := integralSingularCohomology_subsingleton_of_totallyDisconnectedSpace A (n - 1)
    (by omega)
  have hs := (integralRelativeCohomologyConnecting_bijective_of_contractibleSpace
    (n - 1) (by omega) A).surjective
  have hz (α : integralRelativeCohomology (n - 1 + 1) A) : α = 0 := by
    obtain ⟨β, rfl⟩ := hs α
    rw [Subsingleton.elim β 0, map_zero]
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

open CategoryTheory CategoryTheory.Limits in
theorem integralRelativeToAbsoluteCohomology_zero_injective
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    Function.Injective (integralRelativeToAbsoluteCohomology 0 A) := by
  let _ : Mono ((integralRelativeCochainInclusion A).f 0) := by
    change Mono ((HomologicalComplex.eval (ModuleCat.{u} ℤ) (.up ℕ) 0).map
      (kernel.ι (integralSingularCochainMap (singularSubspaceInclusion A))))
    infer_instance
  have h := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
    (integralRelativeCochainInclusion A) 0 (by intro i; simp)
  exact (ModuleCat.mono_iff_injective _).mp h

theorem integralRelativeCohomology_zero_subsingleton_of_pathConnectedSpace
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (A : Set X) (hA : A.Nonempty) : Subsingleton (integralRelativeCohomology 0 A) := by
  let _ : Nonempty A := hA.to_subtype
  have hi := integralRelativeToAbsoluteCohomology_zero_injective A
  have hj := integralSingularCohomologyMap_zero_injective_of_pathConnectedSpace
    (singularSubspaceInclusion A)
  have hz (α : integralRelativeCohomology 0 A) : α = 0 := by
    apply hi
    apply hj
    rw [map_zero, map_zero]
    exact (integralRelativeCohomology_exact_absolute 0 A
      (integralRelativeToAbsoluteCohomology 0 A α)).mpr ⟨α, rfl⟩
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

theorem integralRelativeToAbsoluteCohomology_bijective
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X)
    [Subsingleton (integralSingularCohomology n A)]
    [Subsingleton (integralSingularCohomology (n + 1) A)] :
    Function.Bijective (integralRelativeToAbsoluteCohomology (n + 1) A) := by
  have hi := integralRelativeCohomology_exact_relative n A
  have hs := integralRelativeCohomology_exact_absolute (n + 1) A
  have hleft : integralRelativeCohomologyConnecting n A = 0 := by
    ext α
    rw [Subsingleton.elim α 0, map_zero]
    rfl
  have hright : integralSingularCohomologyMap (n + 1) (singularSubspaceInclusion A) = 0 := by
    ext α
    exact Subsingleton.elim _ _
  rw [hleft, LinearMap.exact_zero_iff_injective] at hi
  rw [hright, LinearMap.exact_zero_iff_surjective] at hs
  exact ⟨hi, hs⟩

theorem integralRelativeToAbsoluteCohomology_bijective_of_contractibleSpace
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A : Set X) [ContractibleSpace A] :
    Function.Bijective (integralRelativeToAbsoluteCohomology (n + 1) A) := by
  cases n with
  | zero =>
    let _ := integralSingularCohomology_subsingleton_of_contractibleSpace A 1 (by decide)
    have hi := integralRelativeCohomology_exact_relative 0 A
    have hs := integralRelativeCohomology_exact_absolute 1 A
    have hleft : integralRelativeCohomologyConnecting 0 A = 0 := by
      ext α
      let z := integralSingularCohomologyZeroEquiv A α
      have hpre : integralSingularCohomologyMap 0 (singularSubspaceInclusion A)
          (z • integralSingularCohomologyUnit X) = α := by
        rw [map_zsmul, integralSingularCohomologyMap_unit,
          ← integralSingularCohomologyZeroEquiv_symm_apply]
        exact (integralSingularCohomologyZeroEquiv A).symm_apply_apply α
      exact (integralRelativeCohomology_exact_subspace 0 A α).mpr ⟨_, hpre⟩
    have hright : integralSingularCohomologyMap 1 (singularSubspaceInclusion A) = 0 := by
      ext α
      exact Subsingleton.elim _ _
    rw [hleft, LinearMap.exact_zero_iff_injective] at hi
    rw [hright, LinearMap.exact_zero_iff_surjective] at hs
    exact ⟨hi, hs⟩
  | succ n =>
    let _ := integralSingularCohomology_subsingleton_of_contractibleSpace A (n + 1)
      (Nat.succ_ne_zero n)
    let _ := integralSingularCohomology_subsingleton_of_contractibleSpace A (n + 2)
      (by omega)
    exact integralRelativeToAbsoluteCohomology_bijective (n + 1) A

theorem integralRelativeCohomology_one_subsingleton_of_contractibleSpace_of_pathConnectedSpace
    {X : Type u} [TopologicalSpace X] [ContractibleSpace X]
    (A : Set X) [PathConnectedSpace A] : Subsingleton (integralRelativeCohomology 1 A) := by
  let _ := integralSingularCohomology_subsingleton_of_contractibleSpace X 1 (by decide)
  have hs := integralRelativeCohomology_exact_relative 0 A
  have hright : integralRelativeToAbsoluteCohomology 1 A = 0 := by
    ext α
    exact Subsingleton.elim _ _
  rw [hright, LinearMap.exact_zero_iff_surjective] at hs
  have hz (α : integralRelativeCohomology 1 A) : α = 0 := by
    obtain ⟨β, rfl⟩ := hs α
    let z := integralSingularCohomologyZeroEquiv A β
    have hpre : integralSingularCohomologyMap 0 (singularSubspaceInclusion A)
        (z • integralSingularCohomologyUnit X) = β := by
      rw [map_zsmul, integralSingularCohomologyMap_unit,
        ← integralSingularCohomologyZeroEquiv_symm_apply]
      exact (integralSingularCohomologyZeroEquiv A).symm_apply_apply β
    exact (integralRelativeCohomology_exact_subspace 0 A β).mpr ⟨_, hpre⟩
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

end DifferentialGeometry.Topology

end
