module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CorrectedPhaseOrbit
public import SphereSixComplex.Paper.Topology.ActualCuspCentralModelEquivalence

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

namespace Construction

public def centralCompactMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) (p : actualLocalCuspCentralSubMulAction W) :
    actualLocalCuspCentralSubMulAction W :=
  ⟨compactPhaseLocalAction constructedModel W.localWitness.radius
      (effectivePhaseSection k) p.1, by
    change constructedModel.t (constructedModel.torusAction _ p.1.1) = 0
    rw [constructedModel.t_torusAction, p.2, mul_zero]⟩

public theorem centralCompactMap_equivariant
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    letI := actualLocalCuspQuotientAction W
    ∀ (k : Fin 2 → Circle) (g : Multiplicative ParameterLattice)
      (p : actualLocalCuspCentralSubMulAction W),
      centralCompactMap W k (g • p) =
        g • centralCompactMap W k p := by
  let _ := actualLocalCuspQuotientAction W
  intro k g p
  apply Subtype.ext
  apply Subtype.ext
  change constructedModel.torusAction _ (g • p).1.1 =
    (g • centralCompactMap W k p).1.1
  rw [central_smul_coe, central_smul_coe]
  change constructedModel.torusAction _ (constructedModel.torusAction _ _) =
    constructedModel.torusAction _ (Additive.toMul (constructedModel.fanShear _)
      (constructedModel.torusAction _ _))
  rw [effectivePhase_fanShear_commute]
  rw [← Equiv.Perm.mul_apply, ← map_mul, mul_comm, map_mul, Equiv.Perm.mul_apply]

public def centralCompactOrbitMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) : ActualLocalCuspCentralOrbitQuotient W →
      ActualLocalCuspCentralOrbitQuotient W := by
  let _ := actualLocalCuspQuotientAction W
  refine Quotient.map (centralCompactMap W k) ?_
  intro p q h
  rcases (MulAction.mem_orbit_iff).mp h with ⟨g, hg⟩
  apply MulAction.mem_orbit_iff.mpr
  exact ⟨g, (centralCompactMap_equivariant W k g q).symm.trans
    (congrArg (centralCompactMap W k) hg)⟩

public theorem continuous_centralCompactMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (fun p : (Fin 2 → Circle) × actualLocalCuspCentralSubMulAction W ↦
      centralCompactMap W p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have hg : Continuous (fun p : (Fin 2 → Circle) × actualLocalCuspCentralSubMulAction W ↦
      compactTorusEmbedding (effectivePhaseSection p.1)) :=
    continuous_compactTorusEmbedding.comp
      (continuous_effectivePhaseSection.comp continuous_fst)
  have hp : Continuous (fun p : (Fin 2 → Circle) × actualLocalCuspCentralSubMulAction W ↦
      (p.2 : constructedModel.Carrier)) := by fun_prop
  exact Continuous.comp
    (f := fun p : (Fin 2 → Circle) × actualLocalCuspCentralSubMulAction W ↦
      (compactTorusEmbedding (effectivePhaseSection p.1),
        (p.2 : constructedModel.Carrier)))
    (g := fun z : DenseTorus × constructedModel.Carrier ↦ constructedModel.torusAction z.1 z.2)
    (continuous_torusAction constructedModel) (hg.prodMk hp)

public theorem continuous_centralCompactOrbitMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (fun p : (Fin 2 → Circle) × ActualLocalCuspCentralOrbitQuotient W ↦
      centralCompactOrbitMap W p.1 p.2) := by
  let _ := actualLocalCuspQuotientAction W
  apply (isQuotientMap_quotient_mk' (s := MulAction.orbitRel
    (Multiplicative ParameterLattice) (actualLocalCuspCentralSubMulAction W))).continuous_lift_prod_right
  exact continuous_quotient_mk'.comp (continuous_centralCompactMap W)

public theorem centralCompactOrbitMap_effectivePhase
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k l : Fin 2 → Circle) (q : constructedPositiveCentralFiber W.localWitness.radius) :
    centralCompactOrbitMap W k (effectivePhaseCentralOrbit W l q) =
      effectivePhaseCentralOrbit W (k * l) q := by
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply Subtype.ext
  change constructedModel.torusAction _ (constructedModel.torusAction _ _) =
    constructedModel.torusAction _ _
  rw [← Equiv.Perm.mul_apply, ← map_mul]
  congr 2
  ext i
  fin_cases i <;> simp [effectivePhaseSection, compactTorusEmbedding]

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric
