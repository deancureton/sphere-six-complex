module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TotallyDisconnectedZero
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ZeroAugmentation
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCapCohomologyConnecting
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainCones
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathCones

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology

universe u

namespace DifferentialGeometry.Topology

section

private theorem cap_zero_vertex {X : Type u} [TopologicalSpace X]
    (φ : LinearMap.ker ((integralSingularCochains X).sc 0).g.hom) (x : X) :
    integralSingularCohomologyCapProduct 0 0
        (moduleHomologyClass ((integralSingularCochains X).sc 0) φ)
        (integralZeroChainClass (integralVertexChain x)) =
      ((show integralSingularCochain 0 X from φ.val) (integralVertexChain x)).down •
        integralZeroChainClass (integralVertexChain x) := by
  change integralSingularCohomologyCapProduct 0 0 _
    (moduleHomologyClass ((integralSingularChains X).sc 0)
      (integralZeroCycleInclusion (integralVertexChain x))) = _
  erw [integralSingularCohomologyCapProduct_class]
  change moduleHomologyClass ((integralSingularChains X).sc 0) _ =
    ((show integralSingularCochain 0 X from φ.val) (integralVertexChain x)).down •
      moduleHomologyClass ((integralSingularChains X).sc 0)
        (integralZeroCycleInclusion (integralVertexChain x))
  rw [← map_zsmul]
  congr 1
  apply Subtype.ext
  change integralSingularCapProduct 0 0 φ.val (integralVertexChain x) =
    ((show integralSingularCochain 0 X from φ.val) (integralVertexChain x)).down • integralVertexChain x
  unfold integralVertexChain
  erw [integralSingularCapProduct_simplex]
  have hid : SimplexCategory.subinterval 0 0 (show 0 + 0 ≤ 0 by omega) = 𝟙 _ := by
    ext j
    rfl
  simp only [hid, op_id]
  rfl

local instance TwoPointCapDuality.dualityCycle_module (S : ShortComplex (ModuleCat.{u} ℤ)) :
    Module ℤ (LinearMap.ker S.g.hom) := (LinearMap.ker S.g.hom).module

private theorem zero_cocycle_class_eq_smul_unit_of_vertex_values
    {X : Type u} [TopologicalSpace X]
    (φ : LinearMap.ker ((integralSingularCochains X).sc 0).g.hom) (n : ℤ)
    (hv : ∀ x : X, (show integralSingularCochain 0 X from φ.val)
      (integralVertexChain x) = ULift.up n) :
    moduleHomologyClass ((integralSingularCochains X).sc 0) φ =
      n • integralSingularCohomologyUnit X := by
  symm
  unfold integralSingularCohomologyUnit
  erw [← map_zsmul]
  congr 1
  apply Subtype.ext
  apply (integralSingularChainBasis 0 X).ext
  intro σ
  rw [integralSingularChainBasis_apply]
  change n • ULift.up (integralSingularAugmentation (integralSimplexChain 0 σ)) =
    (show integralSingularCochain 0 X from φ.val) (integralSimplexChain 0 σ)
  rw [integralSingularAugmentation_simplex, integralSimplexChain_zero_vertex, hv]
  apply ULift.down_injective
  simp

private theorem cap_connecting_vertex_difference
    {X : Type u} [TopologicalSpace X] (A : Set X) (x y : A)
    (φ : LinearMap.ker ((integralSingularCochains A).sc 0).g.hom)
    (c : integralRelativeHomology 1 A)
    (hc : integralRelativeConnecting 0 A c =
      integralZeroChainClass (integralVertexChain y) - integralZeroChainClass (integralVertexChain x)) :
    integralRelativeCohomologyCapToAbsolute A 1 0
        (integralRelativeCohomologyConnecting 0 A
          (moduleHomologyClass ((integralSingularCochains A).sc 0) φ)) c =
      ((show integralSingularCochain 0 A from φ.val) (integralVertexChain y)).down •
          integralZeroChainClass (integralVertexChain y.val) -
        ((show integralSingularCochain 0 A from φ.val) (integralVertexChain x)).down •
          integralZeroChainClass (integralVertexChain x.val) := by
  have h := integralRelativeCohomologyCapToAbsolute_connecting A 0 0
    (moduleHomologyClass ((integralSingularCochains A).sc 0) φ) c
  change integralRelativeCohomologyCapToAbsolute A 1 0
    (integralRelativeCohomologyConnecting 0 A
      (moduleHomologyClass ((integralSingularCochains A).sc 0) φ)) c = _ at h
  rw [hc, map_sub, cap_zero_vertex, cap_zero_vertex, map_sub,
    map_zsmul, map_zsmul, integralZeroChainClass_map, integralZeroChainClass_map,
    integralVertexChain_map, integralVertexChain_map] at h
  exact h

private theorem relative_cohomology_connecting_zero_surjective
    {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X] (A : Set X) :
    Function.Surjective (integralRelativeCohomologyConnecting 0 A) := by
  let _ := integralSingularCohomology_one_subsingleton (X := X)
  intro α
  exact (integralRelativeCohomology_exact_relative 0 A α).mp (Subsingleton.elim _ _)

end

section

private theorem two_point_relative_cap_eq_zero
    {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]
    (A : Set X) (x y : A) (hA : ∀ z : A, z = x ∨ z = y)
    (c : integralRelativeHomology 1 A)
    (hc : integralRelativeConnecting 0 A c =
      integralZeroChainClass (integralVertexChain y) - integralZeroChainClass (integralVertexChain x))
    (α : integralRelativeCohomology 1 A)
    (hα : integralRelativeCohomologyCapToAbsolute A 1 0 α c = 0) : α = 0 := by
  obtain ⟨ψ, rfl⟩ := relative_cohomology_connecting_zero_surjective A α
  obtain ⟨φ, rfl⟩ := moduleHomologyClass_surjective ((integralSingularCochains A).sc 0) ψ
  let f : integralSingularCochain 0 A := φ.val
  have hcap := cap_connecting_vertex_difference A x y φ c hc
  rw [hα] at hcap
  have heval := congrArg integralZeroAugmentation hcap
  rw [map_zero, map_sub, map_zsmul, map_zsmul,
    integralZeroAugmentation_vertex, integralZeroAugmentation_vertex] at heval
  have hxy : (f (integralVertexChain x)).down = (f (integralVertexChain y)).down := by
    change 0 = (f (integralVertexChain y)).down • (1 : ℤ) -
      (f (integralVertexChain x)).down • (1 : ℤ) at heval
    simp only [zsmul_eq_mul, mul_one, Int.cast_id] at heval
    exact (sub_eq_zero.mp heval.symm).symm
  have hv : ∀ z : A, f (integralVertexChain z) = ULift.up (f (integralVertexChain x)).down := by
    intro z
    apply ULift.down_injective
    rcases hA z with rfl | rfl
    · rfl
    · exact hxy.symm
  have hclass := zero_cocycle_class_eq_smul_unit_of_vertex_values φ
    (f (integralVertexChain x)).down hv
  rw [hclass, map_zsmul]
  have hu : integralRelativeCohomologyConnecting 0 A (integralSingularCohomologyUnit A) = 0 :=
    (integralRelativeCohomology_exact_subspace 0 A _).mpr
      ⟨integralSingularCohomologyUnit X, integralSingularCohomologyMap_unit
        (singularSubspaceInclusion A)⟩
  rw [hu, zsmul_zero]

private theorem two_point_relative_cap_injective
    {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]
    (A : Set X) (x y : A) (hA : ∀ z : A, z = x ∨ z = y)
    (c : integralRelativeHomology 1 A)
    (hc : integralRelativeConnecting 0 A c =
      integralZeroChainClass (integralVertexChain y) - integralZeroChainClass (integralVertexChain x)) :
    Function.Injective (fun α : integralRelativeCohomology 1 A =>
      integralRelativeCohomologyCapToAbsolute A 1 0 α c) := by
  intro α β h
  apply sub_eq_zero.mp
  apply two_point_relative_cap_eq_zero A x y hA c hc (α - β)
  erw [map_sub, LinearMap.sub_apply]
  exact sub_eq_zero.mpr h

end

section

private theorem exists_zero_cocycle_vertex_indicator
    {X : Type u} [TopologicalSpace X] [TotallyDisconnectedSpace X] (y : X) :
    ∃ φ : LinearMap.ker ((integralSingularCochains X).sc 0).g.hom,
      (show integralSingularCochain 0 X from φ.val) (integralVertexChain y) = ULift.up 1 ∧
        ∀ z : X, z ≠ y → (show integralSingularCochain 0 X from φ.val)
          (integralVertexChain z) = ULift.up 0 := by
  classical
  let ψ : integralSingularCochain 0 X :=
    (integralSingularChainBasis 0 X).constr ℤ
      (fun σ => ULift.up (if TopCat.toSSetObj₀Equiv σ = y then (1 : ℤ) else 0))
  have hv (z : X) : ψ (integralVertexChain z) = ULift.up (if z = y then (1 : ℤ) else 0) := by
    unfold integralVertexChain
    rw [← integralSingularChainBasis_apply]
    change (integralSingularChainBasis 0 X).constr ℤ _
      ((integralSingularChainBasis 0 X) (TopCat.toSSetObj₀Equiv.symm z)) = _
    rw [Module.Basis.constr_basis, Equiv.apply_symm_apply]
  have hψ : integralSingularCoboundary X 0 1 ψ = 0 := by
    apply LinearMap.ext
    intro b
    change ψ ((integralSingularChains X).d 1 0 b) = 0
    have hb := LinearMap.congr_fun
      (integralBoundary_one_eq_zero_of_totallyDisconnected (X := X)) b
    change (integralSingularChains X).d 1 0 b = 0 at hb
    rw [hb, map_zero]
  have hcycle : ψ ∈ LinearMap.ker ((integralSingularCochains X).sc 0).g.hom := by
    change integralSingularCoboundary X 0 ((ComplexShape.up ℕ).next 0) ψ = 0
    have hn : (ComplexShape.up ℕ).next 0 = 1 := CochainComplex.next ℕ 0
    rwa [hn]
  refine ⟨⟨ψ, hcycle⟩, ?_, ?_⟩
  · simpa only [ite_true] using hv y
  · intro z hz
    simpa only [hz, ite_false] using hv z

private theorem relative_cap_surjective_of_vertex_boundary
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (A : Set X) [TotallyDisconnectedSpace A] (x y : A) (hxy : x ≠ y)
    (c : integralRelativeHomology 1 A)
    (hc : integralRelativeConnecting 0 A c =
      integralZeroChainClass (integralVertexChain y) - integralZeroChainClass (integralVertexChain x)) :
    Function.Surjective (fun α : integralRelativeCohomology 1 A =>
      integralRelativeCohomologyCapToAbsolute A 1 0 α c) := by
  classical
  obtain ⟨φ, hv⟩ := exists_zero_cocycle_vertex_indicator y
  let α := integralRelativeCohomologyConnecting 0 A
    (moduleHomologyClass ((integralSingularCochains A).sc 0) φ)
  have hcap : integralRelativeCohomologyCapToAbsolute A 1 0 α c =
      integralZeroChainClass (integralVertexChain y.val) := by
    have h := cap_connecting_vertex_difference A x y φ c hc
    rw [hv.1, hv.2 x hxy] at h
    simpa only [one_zsmul, zero_zsmul, sub_zero] using h
  intro z
  let n : ℤ := integralZeroAugmentation z
  refine ⟨n • α, ?_⟩
  change integralRelativeCohomologyCapToAbsolute A 1 0 (n • α) c = z
  erw [map_zsmul]
  change n • integralRelativeCohomologyCapToAbsolute A 1 0 α c = z
  rw [hcap]
  apply (integralConnectedZeroAugmentationEquiv (X := X)).injective
  change integralZeroAugmentation (n • integralZeroChainClass (integralVertexChain y.val)) =
    integralZeroAugmentation z
  rw [map_zsmul, integralZeroAugmentation_vertex]
  simp only [zsmul_eq_mul, mul_one, Int.cast_id, n]

end

section

private theorem exists_two_point_relative_cap_bijective
    {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]
    (A : Set X) [TotallyDisconnectedSpace A] (x y : A) (hxy : x ≠ y)
    (hA : ∀ z : A, z = x ∨ z = y) :
    ∃ c : integralRelativeHomology 1 A,
      integralRelativeConnecting 0 A c =
        integralZeroChainClass (integralVertexChain y) - integralZeroChainClass (integralVertexChain x) ∧
      Function.Bijective (fun α : integralRelativeCohomology 1 A =>
        integralRelativeCohomologyCapToAbsolute A 1 0 α c) := by
  let a := integralZeroChainClass (integralVertexChain y) - integralZeroChainClass (integralVertexChain x)
  have hi : integralSingularHomologyMap 0 (singularSubspaceInclusion A) a = 0 := by
    dsimp only [a]
    rw [map_sub, integralZeroChainClass_map, integralZeroChainClass_map,
      integralVertexChain_map, integralVertexChain_map]
    exact sub_eq_zero.mpr (integralZeroVertexClass_eq_of_joined
      ⟨PathConnectedSpace.somePath x.val y.val⟩).symm
  obtain ⟨c, hc⟩ := (integralRelative_exact_subspace 0 A a).mp hi
  exact ⟨c, hc, two_point_relative_cap_injective A x y hA c hc,
    relative_cap_surjective_of_vertex_boundary A x y hxy c hc⟩

private theorem exists_pair_relative_cap_bijective
    {X : Type u} [TopologicalSpace X] [T1Space X] [SimplyConnectedSpace X]
    (x y : X) (hxy : x ≠ y) :
    ∃ c : integralRelativeHomology 1 ({x, y} : Set X),
      integralRelativeConnecting 0 ({x, y} : Set X) c =
        integralZeroChainClass (integralVertexChain (⟨y, by simp⟩ : ({x, y} : Set X))) -
          integralZeroChainClass (integralVertexChain (⟨x, by simp⟩ : ({x, y} : Set X))) ∧
      Function.Bijective (fun α : integralRelativeCohomology 1 ({x, y} : Set X) =>
        integralRelativeCohomologyCapToAbsolute ({x, y} : Set X) 1 0 α c) := by
  let A : Set X := {x, y}
  let a : A := ⟨x, by simp [A]⟩
  let b : A := ⟨y, by simp [A]⟩
  have hab : a ≠ b := fun h => hxy (congrArg Subtype.val h)
  have hA : ∀ z : A, z = a ∨ z = b := by
    intro z
    rcases z.property with hx | hy
    · exact Or.inl (Subtype.ext hx)
    · exact Or.inr (Subtype.ext hy)
  exact exists_two_point_relative_cap_bijective A a b hab hA


end

section

private theorem relative_connecting_zero_injective_of_simplyConnected
    {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X] (A : Set X) :
    Function.Injective (integralRelativeConnecting 0 A) := by
  let _ := integralSingularHomology_one_subsingleton (X := X)
  intro c d h
  apply sub_eq_zero.mp
  have hz : integralRelativeConnecting 0 A (c - d) = 0 := by
    rw [map_sub, h, sub_self]
  obtain ⟨a, ha⟩ := (integralRelative_exact_relative 0 A (c - d)).mp hz
  have ha0 : a = 0 := Subsingleton.elim _ _
  rw [ha0, map_zero] at ha
  exact ha.symm

theorem exists_unique_relative_pair_cap_bijective
    {X : Type u} [TopologicalSpace X] [T1Space X] [SimplyConnectedSpace X]
    (x y : X) (hxy : x ≠ y) :
    ∃! c : integralRelativeHomology 1 ({x, y} : Set X),
      integralRelativeConnecting 0 ({x, y} : Set X) c =
        integralZeroChainClass (integralVertexChain (⟨y, by simp⟩ : ({x, y} : Set X))) -
          integralZeroChainClass (integralVertexChain (⟨x, by simp⟩ : ({x, y} : Set X))) ∧
      Function.Bijective (fun α : integralRelativeCohomology 1 ({x, y} : Set X) =>
        integralRelativeCohomologyCapToAbsolute ({x, y} : Set X) 1 0 α c) := by
  obtain ⟨c, hc, hcap⟩ := exists_pair_relative_cap_bijective x y hxy
  refine ⟨c, ⟨hc, hcap⟩, ?_⟩
  intro d hd
  exact relative_connecting_zero_injective_of_simplyConnected ({x, y} : Set X) (hd.1.trans hc.symm)


end

end DifferentialGeometry.Topology

end
