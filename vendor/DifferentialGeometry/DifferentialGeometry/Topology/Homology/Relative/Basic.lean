module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Relative

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralAbsoluteToRelative_injective_of_subsingleton (n : ℕ) (A : Set X)
    (h : Subsingleton (integralSingularHomology n A)) :
    Function.Injective (integralAbsoluteToRelative n A) := by
  intro a b hab
  have hz : integralAbsoluteToRelative n A (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hex := LinearMap.exact_iff.mp (integralRelative_exact_absolute n A)
  have hmem : a - b ∈ LinearMap.range
      (integralSingularHomologyMap n (singularSubspaceInclusion A)) := by
    rw [← hex]
    exact LinearMap.mem_ker.mpr hz
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hmem
  have hx0 : x = 0 := h.allEq x 0
  rw [hx0, map_zero] at hx
  exact sub_eq_zero.mp hx.symm

theorem integralRelativeConnecting_liftCycles_apply (n : ℕ) (A : Set X)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 2))
    (hz : (z ≫ (cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))).f
        (n + 2)) ≫ (integralRelativeChains A).d (n + 2) (n + 1) = 0)
    (a : integralSingularCoefficients ⟶ (integralSingularChains A).X (n + 1))
    (hac : a ≫ (integralSingularChains A).d (n + 1) n = 0)
    (ha : a ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 1) =
      z ≫ (integralSingularChains X).d (n + 2) (n + 1)) :
    integralRelativeConnecting (n + 1) A
      (((((integralRelativeChains A).liftCycles
          (z ≫ (cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))).f (n + 2))
          (n + 1) ((ComplexShape.down ℕ).next_eq' (by rfl)) hz) ≫
        (integralRelativeChains A).homologyπ (n + 2)) (ULift.up 1)))
      = (((integralSingularChains A).liftCycles a n
          ((ComplexShape.down ℕ).next_eq' (by rfl)) hac) ≫
          (integralSingularChains A).homologyπ (n + 1)) (ULift.up 1) := by
  have h := (integralRelativeChainSequence_shortExact A).δ_eq (n + 2) (n + 1) (by simp)
    (z ≫ (cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))).f (n + 2))
    hz z rfl a ha n ((ComplexShape.down ℕ).next_eq' (by rfl))
  exact congrArg (fun f => f (ULift.up 1)) h

end DifferentialGeometry.Topology
