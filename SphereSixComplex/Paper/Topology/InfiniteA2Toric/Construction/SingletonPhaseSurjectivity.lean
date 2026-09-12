module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.SingletonPhaseProduct

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.CuspPhaseEstimates

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem actualCentral_support_smul
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (g : Multiplicative ParameterLattice) (p : actualLocalCuspCentralSubMulAction W) :
    componentSupport constructedModel
        (((g • p : actualLocalCuspCentralSubMulAction W) :
          localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
      (fun v ↦ v + shearVector g.toAdd) '' componentSupport constructedModel
        ((p : localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) := by
  let _ := actualLocalCuspQuotientAction W
  let C :=
    NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N constructedModel W.localWitness.radius W.localWitness.radius_pos
        W.localWitness.radius_le
  change componentSupport constructedModel
    ((C.toCuspActionData.psiMap g.toAdd p.1).1) = _
  rw [← C.psiMap_eq_generic, C.psiMap_coe]
  exact componentSupport_phase_fanShear _ _ _

public theorem zeroSupport_mem_singletonPhaseImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : actualLocalCuspCentralSubMulAction W)
    (hp : componentSupport constructedModel (p.1.1 : Carrier) = {0}) :
    Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p ∈ singletonPhaseImage W := by
  let _ := actualLocalCuspQuotientAction W
  let q : constructedPositiveCentralFiber W.localWitness.radius :=
    ⟨constructedLocalModulusRetraction W.localWitness.radius p.1, by
      change constructedModel.t (constructedLocalModulusRetraction W.localWitness.radius p.1) = 0
      rw [constructedLocalModulusRetraction_t, p.property]
      simp⟩
  obtain ⟨phi, hphi⟩ := constructedLocalModulusRetraction_polar_surjective
    W.localWitness.radius p.1
  have hsupport : componentSupport constructedModel (q.1.1.1 : Carrier) =
      componentSupport constructedModel (p.1.1 : Carrier) := by
    ext v
    have h := constructedModel.torusAction_centralComponent
      (compactTorusEmbedding phi) v (q.1.1.1 : constructedModel.Carrier)
    rw [hphi] at h
    exact h.symm
  have hq := hsupport.trans hp
  let qcell : constructedPositiveCentralCell W.localWitness.radius 0 :=
    ⟨q, by
      change 0 ∈ componentSupport constructedModel (q.1.1.1 : Carrier)
      rw [hq]
      simp⟩
  let k : Fin 2 → Circle := fun j ↦ phi j.castSucc
  have hn := (positiveCentralCell_zeroRay_phase_eq_iff
    W.localWitness.radius_pos qcell hq (effectivePhaseSection k) phi).mpr
      ⟨rfl, rfl⟩
  have heq : effectivePhaseCentralPoint W k q = p :=
    Subtype.ext (Subtype.ext (hn.trans hphi))
  refine ⟨(⟨qcell, hq⟩, k), ?_⟩
  change Quotient.mk _ (effectivePhaseCentralPoint W k q) = _
  rw [heq]

/-- The geometric singleton stratum is defined by any representative having one component
in its toric support, independently of a parametrization. -/
public def actualSingletonStratum
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set (ActualLocalCuspCentralOrbitQuotient W) :=
  {x | ∃ p : actualLocalCuspCentralSubMulAction W,
    Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p = x ∧
      (componentSupport constructedModel (p.1.1 : Carrier)).ncard = 1}

public theorem singletonPhaseImage_eq_actualSingletonStratum
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    singletonPhaseImage W = actualSingletonStratum W := by
  let _ := actualLocalCuspQuotientAction W
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨effectivePhaseCentralPoint W p.2 p.1.1.1, rfl, ?_⟩
    rw [effectivePhaseCentralPoint_support, p.1.property]
    simp
  · rintro ⟨p, rfl, hp⟩
    obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp hp
    obtain ⟨lambda, hlambda⟩ := shearVector_surjective (-v)
    let g := Multiplicative.ofAdd lambda
    let q : actualLocalCuspCentralSubMulAction W := g • p
    have hq : componentSupport constructedModel (q.1.1 : Carrier) = {0} := by
      rw [actualCentral_support_smul, hv]
      simp [g, hlambda]
    have heq : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
        (actualLocalCuspCentralSubMulAction W)) q = Quotient.mk _ p := by
      apply Quotient.sound
      change MulAction.orbitRel (Multiplicative ParameterLattice)
        (actualLocalCuspCentralSubMulAction W) q p
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨g, rfl⟩
    rw [← heq]
    exact zeroSupport_mem_singletonPhaseImage W q hq

/-- The polar parametrization is onto the full geometric singleton-support stratum in the
actual quotient. -/
public def actualSingletonPhaseHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    SingletonPhaseCell W.localWitness.radius ≃ₜ
      actualSingletonStratum W :=
  (singletonPhaseHomeomorph W).trans
    (Homeomorph.setCongr (singletonPhaseImage_eq_actualSingletonStratum W))

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction

end
