module

public import SphereSixComplex.Prerequisites.Topology.FiniteCyclicProductMappingTorus

/-!
# The normalized finite cyclic cover of a mapping torus
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex.Topology.NormalizedAffineMappingTorusCover

open CyclicMappingTorus

variable {m : ℕ} [NeZero m] {F : Type} [TopologicalSpace F]

/-- The normalized affine cover of a circle mapping torus. -/
public def normalizedAffineCoverToCircleMappingTorus
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) :
    C(UnitAddCircle × F, CircleMappingTorus phi) where
  toFun x := CyclicMappingTorus.normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph phi hpow
    (Quotient.mk (CyclicMappingTorus.normalizedAffineCyclicSetoid (m := m) phi) x)
  continuous_toFun :=
    (CyclicMappingTorus.normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph phi hpow).continuous.comp
      continuous_quot_mk


end SphereSixComplex.Topology.NormalizedAffineMappingTorusCover

end

end
