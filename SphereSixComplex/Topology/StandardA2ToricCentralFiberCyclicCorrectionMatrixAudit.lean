module

public import SphereSixComplex.Topology.StandardA2ToricCentralFiberCyclicQuotientSymmetry
public import SphereSixComplex.Topology.ActualCuspStraighteningRetraction

/-!
# Audit of cyclic covariance for the cusp correction matrix

The toric cyclic symmetry descends through the analytic deck action precisely when the frozen
correction matrix intertwines the induced transformations of phase and parameter coordinates.
-/

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open
  SphereSixComplex.Geometry.CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def a2CyclicComplexLinear (u : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![-u 0 - u 1, u 0]

/-- The explicit matrix-level condition sufficient for cyclic covariance of the frozen analytic
phase coefficients. -/
public def CyclicCorrectionCovariant
    (N : NormalizedFuchsianCuspCoordinate E D) : Prop :=
  ∀ lambda : ParameterLattice,
    a2CyclicComplexLinear
        ((N.correctionMatrix 0).mulVec (fun j ↦ (lambda j : ℂ))) =
      (N.correctionMatrix 0).mulVec
        (fun j ↦ (a2CyclicParameter lambda j : ℂ))

public theorem phaseCoefficient_cyclic_of_correction_covariant
    (hN : CyclicCorrectionCovariant N) (lambda : ParameterLattice) :
    a2CyclicPhase (N.phaseCoefficient lambda 0) =
      N.phaseCoefficient (a2CyclicParameter lambda) 0 := by
  have h := hN lambda
  ext i
  fin_cases i
  · have hi := congrFun h 0
    change -((N.correctionMatrix 0).mulVec (fun j ↦ (lambda j : ℂ))) 0 -
        ((N.correctionMatrix 0).mulVec (fun j ↦ (lambda j : ℂ))) 1 =
      ((N.correctionMatrix 0).mulVec
        (fun j ↦ (a2CyclicParameter lambda j : ℂ))) 0 at hi
    change (Complex.exp
          (2 * Real.pi * Complex.I *
            (N.correctionMatrix 0).mulVec (fun j ↦ (lambda j : ℂ)) 0))⁻¹ *
        (Complex.exp
          (2 * Real.pi * Complex.I *
            (N.correctionMatrix 0).mulVec (fun j ↦ (lambda j : ℂ)) 1))⁻¹ =
      Complex.exp
        (2 * Real.pi * Complex.I *
          (N.correctionMatrix 0).mulVec
            (fun j ↦ (a2CyclicParameter lambda j : ℂ)) 0)
    rw [← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add]
    apply congrArg Complex.exp
    rw [← hi]
    ring_nf
  · have hi := congrFun h 1
    change ((N.correctionMatrix 0).mulVec (fun j ↦ (lambda j : ℂ))) 0 =
      ((N.correctionMatrix 0).mulVec
        (fun j ↦ (a2CyclicParameter lambda j : ℂ))) 1 at hi
    change Complex.exp
        (2 * Real.pi * Complex.I *
          (N.correctionMatrix 0).mulVec (fun j ↦ (lambda j : ℂ)) 0) =
      Complex.exp
        (2 * Real.pi * Complex.I *
          (N.correctionMatrix 0).mulVec
            (fun j ↦ (a2CyclicParameter lambda j : ℂ)) 1)
    exact congrArg (fun z : ℂ ↦ Complex.exp (2 * Real.pi * Complex.I * z)) hi

public theorem cyclicCorrectionCovariant_of_correctionMatrix_zero
    (hzero : N.correctionMatrix 0 = 0) : CyclicCorrectionCovariant N := by
  intro lambda
  rw [hzero]
  ext i
  fin_cases i <;> simp [a2CyclicComplexLinear]

public theorem phaseCoefficient_cyclic_of_correctionMatrix_zero
    (hzero : N.correctionMatrix 0 = 0) (lambda : ParameterLattice) :
    a2CyclicPhase (N.phaseCoefficient lambda 0) =
      N.phaseCoefficient (a2CyclicParameter lambda) 0 :=
  phaseCoefficient_cyclic_of_correction_covariant
    (cyclicCorrectionCovariant_of_correctionMatrix_zero hzero) lambda

/-- Under correction-matrix covariance, cyclic rotation conjugates the frozen central deck map
by the induced order-three automorphism of the parameter lattice. -/
public theorem a2CyclicCarrier_frozenCentralDeck
    (hN : CyclicCorrectionCovariant N) (lambda : ParameterLattice) (p : Carrier) :
    a2CyclicCarrier
        (carrierTorusActionFun (phaseEmbedding (N.phaseCoefficient lambda 0))
          (carrierFanShearFun lambda p)) =
      carrierTorusActionFun
        (phaseEmbedding (N.phaseCoefficient (a2CyclicParameter lambda) 0))
        (carrierFanShearFun (a2CyclicParameter lambda) (a2CyclicCarrier p)) := by
  rw [a2CyclicCarrier_phaseAction_fanShear,
    phaseCoefficient_cyclic_of_correction_covariant hN]

public theorem a2CyclicLocalCarrier_frozenLocalPsiMap
    (hN : CyclicCorrectionCovariant N) (r : ℝ) (lambda : ParameterLattice)
    (p : LocalCarrier constructedModel r) :
    a2CyclicLocalCarrierHomeomorph r
        (frozenLocalPsiMap N constructedModel r lambda p) =
      frozenLocalPsiMap N constructedModel r (a2CyclicParameter lambda)
        (a2CyclicLocalCarrierHomeomorph r p) := by
  apply Subtype.ext
  change a2CyclicCarrier
      (carrierTorusActionFun (phaseEmbedding (N.phaseCoefficient lambda 0))
        (carrierFanShearFun lambda p.1)) =
    carrierTorusActionFun
      (phaseEmbedding (N.phaseCoefficient (a2CyclicParameter lambda) 0))
      (carrierFanShearFun (a2CyclicParameter lambda) (a2CyclicCarrier p.1))
  exact a2CyclicCarrier_frozenCentralDeck hN lambda p.1

/-- On the height-zero fibre, the cyclic carrier rotation conjugates the actual analytic deck
map by the same parameter automorphism. -/
public theorem a2CyclicLocalCarrier_actualCentralPsiMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (hN : CyclicCorrectionCovariant N) (lambda : ParameterLattice)
    (p : LocalCarrier constructedModel W.localWitness.radius)
    (hp : constructedModel.t p = 0) :
    let C := restrictedActualLocalPhaseCoefficients N constructedModel
      W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
    a2CyclicLocalCarrierHomeomorph W.localWitness.radius (C.psiMap lambda p) =
      C.psiMap (a2CyclicParameter lambda)
        (a2CyclicLocalCarrierHomeomorph W.localWitness.radius p) := by
  let C := restrictedActualLocalPhaseCoefficients N constructedModel
    W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  change a2CyclicLocalCarrierHomeomorph W.localWitness.radius (C.psiMap lambda p) =
    C.psiMap (a2CyclicParameter lambda)
      (a2CyclicLocalCarrierHomeomorph W.localWitness.radius p)
  have hactual : C.psiMap lambda p =
      frozenLocalPsiMap N constructedModel W.localWitness.radius lambda p := by
    apply Subtype.ext
    rw [C.psiMap_coe, frozenLocalPsiMap_coe, hp]
    rfl
  have hp' : constructedModel.t
      (a2CyclicLocalCarrierHomeomorph W.localWitness.radius p) = 0 := by
    rw [a2CyclicLocalCarrierHomeomorph_coe,
      constructedModel_t_a2CyclicConstructedCarrier]
    exact hp
  have hactual' : C.psiMap (a2CyclicParameter lambda)
      (a2CyclicLocalCarrierHomeomorph W.localWitness.radius p) =
        frozenLocalPsiMap N constructedModel W.localWitness.radius
          (a2CyclicParameter lambda)
          (a2CyclicLocalCarrierHomeomorph W.localWitness.radius p) := by
    apply Subtype.ext
    rw [C.psiMap_coe, frozenLocalPsiMap_coe, hp']
    rfl
  rw [hactual, hactual']
  exact a2CyclicLocalCarrier_frozenLocalPsiMap hN _ _ _

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end
