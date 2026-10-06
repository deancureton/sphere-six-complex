module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathChains

@[expose] public section

/-! # Original zero-chain representatives and their actual homology classes -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Retain the ORIGINAL kernel's integer action on actual zero-cycles. -/
instance integralZeroCyclesModule : Module ℤ (LinearMap.ker ((integralSingularChains X).sc 0).g.hom) :=
  (LinearMap.ker ((integralSingularChains X).sc 0).g.hom).module

/-- Every original zero-chain is a cycle for the actual degree-zero differential. -/
def integralZeroCycleInclusion : (integralSingularChains X).X 0 →ₗ[ℤ]
    LinearMap.ker ((integralSingularChains X).sc 0).g.hom :=
  (LinearMap.id : (integralSingularChains X).X 0 →ₗ[ℤ] (integralSingularChains X).X 0).codRestrict
    (LinearMap.ker ((integralSingularChains X).sc 0).g.hom) (fun c => by
    change (integralSingularChains X).d 0 ((ComplexShape.down ℕ).next 0) c = 0
    rw [ChainComplex.next_nat_zero, (integralSingularChains X).shape 0 0 (by simp)]
    rfl)

/-- The original homology class of an actual zero-chain. -/
def integralZeroChainClass : (integralSingularChains X).X 0 →ₗ[ℤ] integralSingularHomology 0 X :=
  (moduleHomologyClass ((integralSingularChains X).sc 0)).comp integralZeroCycleInclusion

/-- Every element of ORIGINAL H0 is represented by an original zero-chain. -/
theorem integralZeroChainClass_surjective : Function.Surjective (integralZeroChainClass (X := X)) := by
  intro a
  obtain ⟨c, hc⟩ := moduleHomologyClass_surjective ((integralSingularChains X).sc 0) a
  exact ⟨c.val, hc⟩

/-- A zero-chain class vanishes exactly when the SAME chain is an actual boundary. -/
theorem integralZeroChainClass_eq_zero_iff (c : (integralSingularChains X).X 0) :
    integralZeroChainClass c = 0 ↔ ∃ b : (integralSingularChains X).X 1,
      (integralSingularChains X).d 1 0 b = c := by
  have h := moduleHomologyClass_eq_zero_iff ((integralSingularChains X).sc 0) (integralZeroCycleInclusion c)
  change (integralZeroChainClass c = 0 ↔ ∃ b : (integralSingularChains X).X ((ComplexShape.down ℕ).prev 0),
    (integralSingularChains X).d ((ComplexShape.down ℕ).prev 0) 0 b = c) at h
  exact h.trans (congrArg (fun i => ∃ b : (integralSingularChains X).X i,
    (integralSingularChains X).d i 0 b = c) (ChainComplex.prev ℕ 0)).to_iff

/-- Equality of actual zero-chain classes is equality modulo SAME original boundaries. -/
theorem integralZeroChainClass_eq_iff (c d : (integralSingularChains X).X 0) :
    integralZeroChainClass c = integralZeroChainClass d ↔ ∃ b : (integralSingularChains X).X 1,
      (integralSingularChains X).d 1 0 b = c - d := by
  rw [← sub_eq_zero, ← map_sub, integralZeroChainClass_eq_zero_iff]

/-- The ORIGINAL induced H0 map sends a zero-chain class to the class
of the SAME original image chain. -/
theorem integralZeroChainClass_map (f : C(X, Y)) (c : (integralSingularChains X).X 0) :
    integralSingularHomologyMap 0 f (integralZeroChainClass c) =
      integralZeroChainClass ((integralSingularChainMap f).f 0 c) :=
  moduleHomologyClass_map
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) 0).map
      (integralSingularChainMap f)) (integralZeroCycleInclusion c)

end DifferentialGeometry.Topology
