module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyClasses

@[expose] public section

/-! # Original homology maps on concrete cycle representatives -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace DifferentialGeometry.Topology

variable {R : Type u} [Ring R] {S T : ShortComplex (ModuleCat.{v} R)}

/-- The same middle map takes an actual cycle to an actual cycle. -/
def moduleCycleMap (φ : S ⟶ T) : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
  (φ.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (fun c => by
    have h := congrArg (fun f : S.X₂ ⟶ T.X₃ => f c.val) φ.comm₂₃
    change T.g (φ.τ₂ c.val) = φ.τ₃ (S.g c.val) at h
    rw [show S.g c.val = 0 from c.property, map_zero] at h
    exact h)

/-- The abstract cycles map acts on the same original concrete cycle. -/
theorem moduleCycleMap_cyclesIso (φ : S ⟶ T) (c : LinearMap.ker S.g.hom) :
    ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv c) =
      T.moduleCatCyclesIso.inv (moduleCycleMap φ c) := by
  apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
  have h := congrArg (fun f : S.cycles ⟶ T.X₂ => f (S.moduleCatCyclesIso.inv c))
    (ShortComplex.cyclesMap_i φ)
  have hs := congrArg (fun f : S.moduleCatLeftHomologyData.K ⟶ S.X₂ => f c)
    S.moduleCatCyclesIso_inv_iCycles
  have ht := congrArg (fun f : T.moduleCatLeftHomologyData.K ⟶ T.X₂ => f (moduleCycleMap φ c))
    T.moduleCatCyclesIso_inv_iCycles
  change T.iCycles (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv c)) =
    φ.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv c)) at h
  change S.iCycles (S.moduleCatCyclesIso.inv c) = c.val at hs
  change T.iCycles (T.moduleCatCyclesIso.inv (moduleCycleMap φ c)) = φ.τ₂ c.val at ht
  rw [h, hs, ht]

/-- The ORIGINAL categorical homology map carries a concrete cycle
class to the class of its SAME original image cycle. -/
theorem moduleHomologyClass_map (φ : S ⟶ T) (c : LinearMap.ker S.g.hom) :
    ShortComplex.homologyMap φ (moduleHomologyClass S c) =
      moduleHomologyClass T (moduleCycleMap φ c) := by
  have h := congrArg (fun f : S.cycles ⟶ T.homology => f (S.moduleCatCyclesIso.inv c))
    (ShortComplex.homologyπ_naturality φ)
  change ShortComplex.homologyMap φ (moduleHomologyClass S c) =
    T.homologyπ (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv c)) at h
  rw [h, moduleCycleMap_cyclesIso]
  rfl

end DifferentialGeometry.Topology
