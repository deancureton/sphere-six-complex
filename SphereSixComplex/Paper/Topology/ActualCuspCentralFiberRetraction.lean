module

public import SphereSixComplex.Paper.Geometry.CuspPuncturedCollarBridge
public import SphereSixComplex.Prerequisites.Topology.EquivariantStrongDeformationRetraction
public import SphereSixComplex.Prerequisites.Topology.MayerVietoris

/-!
# Equivariant descent for the cusp-filling retraction

Proposition 7.2 requires an explicit equivariant strong deformation retraction of the toric
prequotient onto its central fibre.  The present toric model does not yet contain the polar-part,
honeycomb, or stabilizer data from which that retraction is constructed.  This file therefore
does not assert its existence.  It proves the reusable quotient-descent theorem and records the
exact datum whose construction would instantiate the theorem for the actual cusp filling.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap

namespace SphereSixComplex

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  (W : ActualPuncturedCuspCollarWitness N M)

/-- The prequotient central fibre in the actual local cusp carrier. -/
public def actualLocalCuspCentralFiber : Set (localCarrier M W.localWitness.radius) :=
  {p | M.t p = 0}

/-- The action used definitionally by `actualLocalCuspFilling`. -/
@[instance_reducible] public noncomputable def actualLocalCuspQuotientAction :
    MulAction (Multiplicative ParameterLattice) (localCarrier M W.localWitness.radius) :=
  let C :=
    NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  C.toCuspActionData.psiAction

/-- Continuity of the actual phase-corrected lattice action. -/
public theorem actualLocalPsiContinuousConstSMul :
    letI := actualLocalCuspQuotientAction W
    ContinuousConstSMul (Multiplicative ParameterLattice)
      (localCarrier M W.localWitness.radius) := by
  let C :=
    NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ := actualLocalCuspQuotientAction W
  exact ⟨by
    intro lambda
    rw [show lambda = Multiplicative.ofAdd (Multiplicative.toAdd lambda) from rfl]
    change Continuous (C.toCuspActionData.psiMap
      (Multiplicative.toAdd lambda))
    exact (C.genericPsiMap_holomorphic _).continuous⟩

/-- An equivariant strong deformation retraction onto the actual central fiber. -/
public abbrev ActualLocalCuspCentralFiberRetractionData :=
  letI := actualLocalCuspQuotientAction W
  EquivariantStrongDeformationRetraction
    (Multiplicative ParameterLattice) (localCarrier M W.localWitness.radius)
      (actualLocalCuspCentralFiber W)

namespace ActualLocalCuspCentralFiberRetractionData

variable (R : ActualLocalCuspCentralFiberRetractionData W)

/-- The central fibre after passage to the actual local cusp quotient. -/
public noncomputable def quotientCentralFiber : Set (ActualLocalCuspFilling W) := by
  letI := actualLocalCuspQuotientAction W
  exact EquivariantStrongDeformationRetraction.quotientCore R

/-- The quotient retraction supplied conditionally by the prequotient toric retraction. -/
public noncomputable def quotientRetract : C(ActualLocalCuspFilling W, ActualLocalCuspFilling W) := by
  letI := actualLocalCuspQuotientAction W
  exact EquivariantStrongDeformationRetraction.quotientRetract R

/-- The quotient strong deformation homotopy supplied by the prequotient toric retraction. -/
public noncomputable def quotientHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id (ActualLocalCuspFilling W))
      (quotientRetract W R) := by
  letI := actualLocalCuspQuotientAction W
  letI := actualLocalPsiContinuousConstSMul W
  exact EquivariantStrongDeformationRetraction.quotientHomotopy R

public theorem quotientRetract_mem (q : ActualLocalCuspFilling W) :
    quotientRetract W R q ∈ quotientCentralFiber W R := by
  let _ := actualLocalCuspQuotientAction W
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (localCarrier M W.localWitness.radius) := actualLocalPsiContinuousConstSMul W
  exact EquivariantStrongDeformationRetraction.quotientRetract_mem R q

public theorem quotientRetract_fixed (q : ActualLocalCuspFilling W)
    (hq : q ∈ quotientCentralFiber W R) : quotientRetract W R q = q := by
  let _ := actualLocalCuspQuotientAction W
  exact EquivariantStrongDeformationRetraction.quotientRetract_fixed R q hq

/-- The quotient retraction with its codomain restricted to the central fibre. -/
public noncomputable def quotientRetractToCentralFiber :
    C(ActualLocalCuspFilling W, quotientCentralFiber W R) where
  toFun q := ⟨quotientRetract W R q, quotientRetract_mem W R q⟩
  continuous_toFun := (quotientRetract W R).continuous.subtype_mk _

/-- Inclusion of the quotient central fibre into the actual local cusp filling. -/
public noncomputable def quotientCentralFiberInclusion :
    C(quotientCentralFiber W R, ActualLocalCuspFilling W) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val


/-- The homotopy equivalence produced by the descended strong deformation retraction. -/
public noncomputable def quotientCentralFiberHomotopyEquiv :
    ActualLocalCuspFilling W ≃ₕ quotientCentralFiber W R where
  toFun := quotientRetractToCentralFiber W R
  invFun := quotientCentralFiberInclusion W R
  left_inv := by
    change (quotientRetract W R).Homotopic (ContinuousMap.id (ActualLocalCuspFilling W))
    exact ⟨(quotientHomotopy W R).symm⟩
  right_inv := by
    have h : (quotientRetractToCentralFiber W R).comp
        (quotientCentralFiberInclusion W R) =
        ContinuousMap.id (quotientCentralFiber W R) := by
      apply ContinuousMap.ext
      intro q
      apply Subtype.ext
      exact quotientRetract_fixed W R q q.2
    rw [h]

/-- Specialization is an isomorphism on integral singular homology. -/
public noncomputable def specializationHomologyEquiv (k : ℕ) :
    IntegralSingularHomology k (ActualLocalCuspFilling W) ≃+
      IntegralSingularHomology k (quotientCentralFiber W R) :=
  integralSingularHomologyEquivOfHomotopyEquiv k (quotientCentralFiberHomotopyEquiv W R)






end ActualLocalCuspCentralFiberRetractionData

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex
