module

public import SphereSixComplex.Paper.Topology.ConstructedA2HigherCellFaces
public import SphereSixComplex.Paper.Topology.ActualCuspCentralModelEquivalence

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def constructedA2CentralCompactMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) (p : actualLocalCuspCentralSubMulAction W) :
    actualLocalCuspCentralSubMulAction W :=
  ⟨compactPhaseLocalAction constructedModel W.localWitness.radius
      (constructedA2EffectivePhaseSection k) p.1, by
    change constructedModel.t (constructedModel.torusAction _ p.1.1) = 0
    rw [constructedModel.t_torusAction, p.2, mul_zero]⟩

public theorem constructedA2CentralCompactMap_equivariant
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    letI := actualLocalCuspQuotientAction W
    ∀ (k : Fin 2 → Circle) (g : Multiplicative ParameterLattice)
      (p : actualLocalCuspCentralSubMulAction W),
      constructedA2CentralCompactMap W k (g • p) =
        g • constructedA2CentralCompactMap W k p := by
  let _ := actualLocalCuspQuotientAction W
  intro k g p
  apply Subtype.ext
  apply Subtype.ext
  change constructedModel.torusAction _ (g • p).1.1 =
    (g • constructedA2CentralCompactMap W k p).1.1
  rw [central_smul_coe, central_smul_coe]
  change constructedModel.torusAction _ (constructedModel.torusAction _ _) =
    constructedModel.torusAction _ (Additive.toMul (constructedModel.fanShear _)
      (constructedModel.torusAction _ _))
  rw [constructedA2EffectivePhase_fanShear_commute]
  rw [← Equiv.Perm.mul_apply, ← map_mul, mul_comm, map_mul, Equiv.Perm.mul_apply]

public def constructedA2CentralCompactOrbitMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) : ActualLocalCuspCentralOrbitQuotient W →
      ActualLocalCuspCentralOrbitQuotient W := by
  let _ := actualLocalCuspQuotientAction W
  refine Quotient.map (constructedA2CentralCompactMap W k) ?_
  intro p q h
  rcases (MulAction.mem_orbit_iff).mp h with ⟨g, hg⟩
  apply MulAction.mem_orbit_iff.mpr
  exact ⟨g, (constructedA2CentralCompactMap_equivariant W k g q).symm.trans
    (congrArg (constructedA2CentralCompactMap W k) hg)⟩

public theorem constructedA2CentralCompactMap_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (fun p : (Fin 2 → Circle) × actualLocalCuspCentralSubMulAction W ↦
      constructedA2CentralCompactMap W p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply (establishedContinuousTorusAction constructedModel).variable_action
  · exact continuous_compactTorusEmbedding.comp
      (constructedA2EffectivePhaseSection_continuous.comp continuous_fst)
  · fun_prop

public theorem constructedA2CentralCompactOrbitMap_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (fun p : (Fin 2 → Circle) × ActualLocalCuspCentralOrbitQuotient W ↦
      constructedA2CentralCompactOrbitMap W p.1 p.2) := by
  let _ := actualLocalCuspQuotientAction W
  apply (isQuotientMap_quotient_mk' (s := MulAction.orbitRel
    (Multiplicative ParameterLattice) (actualLocalCuspCentralSubMulAction W))).continuous_lift_prod_right
  exact continuous_quotient_mk'.comp (constructedA2CentralCompactMap_continuous W)

public theorem constructedA2CentralCompactOrbitMap_effectivePhase
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k l : Fin 2 → Circle) (q : constructedPositiveCentralFiber W.localWitness.radius) :
    constructedA2CentralCompactOrbitMap W k (constructedA2EffectivePhaseCentralOrbit W l q) =
      constructedA2EffectivePhaseCentralOrbit W (k * l) q := by
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply Subtype.ext
  change constructedModel.torusAction _ (constructedModel.torusAction _ _) =
    constructedModel.torusAction _ _
  rw [← Equiv.Perm.mul_apply, ← map_mul]
  congr 2
  ext i
  fin_cases i <;> simp [constructedA2EffectivePhaseSection, compactTorusEmbedding]

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
