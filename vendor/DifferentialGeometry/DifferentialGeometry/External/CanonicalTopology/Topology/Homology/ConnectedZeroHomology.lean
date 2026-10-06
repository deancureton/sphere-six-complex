module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ZeroHomologyMaps

@[expose] public section

/-! # Actual H0 maps between path-connected spaces are isomorphisms -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [PathConnectedSpace X] [PathConnectedSpace Y]

/-- The SAME original H0 map is an isomorphism for any continuous map
between actual path-connected spaces. Its inverse is induced by a constant
map, and the inverse identities are proved from actual paths on vertices. -/
def integralSingularHomologyZeroMapEquiv (f : C(X, Y)) :
    integralSingularHomology 0 X ≃ₗ[ℤ] integralSingularHomology 0 Y where
  toLinearMap := integralSingularHomologyMap 0 f
  invFun := integralSingularHomologyMap 0 (ContinuousMap.const Y (Classical.arbitrary X))
  left_inv a := by
    let g := ContinuousMap.const Y (Classical.arbitrary X)
    have he := (integralSingularHomologyMap_comp 0 f g).symm.trans
      ((integralSingularHomologyMap_zero_eq_of_joined (g.comp f) (ContinuousMap.id X)
        (fun x => ⟨PathConnectedSpace.somePath _ _⟩)).trans (integralSingularHomologyMap_id 0))
    exact LinearMap.congr_fun he a
  right_inv a := by
    let g := ContinuousMap.const Y (Classical.arbitrary X)
    have he := (integralSingularHomologyMap_comp 0 g f).symm.trans
      ((integralSingularHomologyMap_zero_eq_of_joined (f.comp g) (ContinuousMap.id Y)
        (fun y => ⟨PathConnectedSpace.somePath _ _⟩)).trans (integralSingularHomologyMap_id 0))
    exact LinearMap.congr_fun he a

/-- This proves invertibility of the ORIGINAL categorical homology map
of the SAME original chain map. -/
theorem integralSingularHomologyZeroMap_isIso (f : C(X, Y)) :
    IsIso (HomologicalComplex.homologyMap (integralSingularChainMap f) 0) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (integralSingularHomologyZeroMapEquiv f).bijective

end DifferentialGeometry.Topology
