module

public import SphereSixComplex.Topology.PaperAffineCyclicReducedFiberMappingTorus

/-!
# The normalized finite cyclic cover of a mapping torus
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex.Topology.NormalizedAffineMappingTorusCover

open PaperAffineCyclicReducedFiberMappingTorus

variable {m : ℕ} [NeZero m] {F : Type} [TopologicalSpace F]

/-- The normalized affine cover of a circle mapping torus. -/
public def normalizedAffineCoverToCircleMappingTorus
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) :
    C(UnitAddCircle × F, CircleMappingTorus phi) where
  toFun x := normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph phi hpow
    (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi) x)
  continuous_toFun :=
    (normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph phi hpow).continuous.comp
      continuous_quot_mk

@[simp]
public theorem normalizedAffineCoverToCircleMappingTorus_apply
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (x : UnitAddCircle × F) :
    normalizedAffineCoverToCircleMappingTorus phi hpow x =
      normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph phi hpow
        (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi) x) :=
  rfl

end SphereSixComplex.Topology.NormalizedAffineMappingTorusCover

end

end
