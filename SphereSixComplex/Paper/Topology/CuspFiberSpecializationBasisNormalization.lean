module

public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecialization

/-!
# Basis-free cusp fibre specialization

The specialization matrix currently mixes two logically different facts: the fibre-coinvariant
part of specialization is an isomorphism, and the independently selected cellular homology
coordinates agree with that isomorphism.  This file separates them.  Once the target coordinates
are normalized through the specialization isomorphism, every matrix entry is formal.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex

namespace WangHomologyPresentation

variable {HighRelations High Total LowRelations Low L C : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low] [AddCommGroup L] [AddCommGroup C]




/-- If total specialization is onto, kills a Wang section, and source coinvariants and target
have the same finite free coordinates, then restriction to coinvariants is bijective. -/
public theorem coinvariantsRestriction_bijective_of_surjective_of_section_eq_zero
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.Section) (f : Total →ₗ[ℤ] L) (hf : Function.Surjective f)
    (hsection : f.comp S.lift = 0) [Module.Free ℤ C] [Module.Finite ℤ C]
    (cP : P.Coinvariants ≃ₗ[ℤ] C) (cL : L ≃ₗ[ℤ] C) :
    Function.Bijective (f.comp P.coinvariantsToTotal) := by
  let r := f.comp P.coinvariantsToTotal
  have hrSurjective : Function.Surjective r := by
    intro y
    obtain ⟨t, ht⟩ := hf y
    let z := P.totalToInvariants t
    let t₀ := t - S.lift z
    have ht₀ : P.totalToInvariants t₀ = 0 := by
      change P.totalToInvariants (t - S.lift (P.totalToInvariants t)) = 0
      rw [map_sub]
      have hs := DFunLike.congr_fun S.right_inv (P.totalToInvariants t)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hs
      rw [hs, sub_self]
    obtain ⟨x, hx⟩ := (P.exact_coinvariantsToTotal_totalToInvariants t₀).mp ht₀
    refine ⟨x, ?_⟩
    change f (P.coinvariantsToTotal x) = y
    rw [hx]
    change f (t - S.lift z) = y
    rw [map_sub, ht]
    have hs := DFunLike.congr_fun hsection z
    change f (S.lift z) = 0 at hs
    rw [hs, sub_zero]
  let e : Module.End ℤ C :=
    cL.toLinearMap.comp (r.comp cP.symm.toLinearMap)
  have heSurjective : Function.Surjective e :=
    cL.surjective.comp (hrSurjective.comp cP.symm.surjective)
  have heInjective : Function.Injective e :=
    Module.End.injective_of_surjective ℤ C heSurjective
  refine ⟨?_, hrSurjective⟩
  intro x y hxy
  apply cP.injective
  apply heInjective
  have hex : e (cP x) = cL (r x) := by
    simp only [e, LinearMap.coe_comp, Function.comp_apply]
    have hs : cP.symm.toLinearMap (cP x) = x := cP.symm_apply_apply x
    rw [hs]
    rfl
  have hey : e (cP y) = cL (r y) := by
    simp only [e, LinearMap.coe_comp, Function.comp_apply]
    have hs : cP.symm.toLinearMap (cP y) = y := cP.symm_apply_apply y
    rw [hs]
    rfl
  rw [hex, hey]
  exact congrArg cL hxy

end WangHomologyPresentation

namespace Geometry.CuspPuncturedCollarBridge.CuspFiberSpecializationNormalization

open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M}

/-- The basis-free degree-one map from the radial mapping torus to the cusp filling. -/
public noncomputable def rawDegreeOneTotalSpecialization
    (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    IntegralSingularHomology 1 (CircleMappingTorus G.clutching) →ₗ[ℤ]
      IntegralSingularHomology 1 (ActualLocalCuspFilling W) := by
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 1
    G.toUnnormalizedCuspRadialClutchingData.totalHomotopyEquiv
  exact ((integralSingularHomologyMap 1
      ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩).comp
        e.symm.toAddMonoidHom).toIntLinearMap


/-- The basis-free degree-one map from Wang coinvariants to the cusp filling. -/
public noncomputable def rawDegreeOneFiberSpecialization
    (G : ActualCuspRadialClutchingData W) :
    let _ := G.fiberTopology
    (circleMappingTorusHOnePresentation G.clutching).Coinvariants →ₗ[ℤ]
      IntegralSingularHomology 1 (ActualLocalCuspFilling W) := by
  let _ := G.fiberTopology
  exact (rawDegreeOneTotalSpecialization G).comp
    (circleMappingTorusHOnePresentation G.clutching).coinvariantsToTotal




















end Geometry.CuspPuncturedCollarBridge.CuspFiberSpecializationNormalization

end SphereSixComplex

end

end
