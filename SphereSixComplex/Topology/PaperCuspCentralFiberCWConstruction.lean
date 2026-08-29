module

public import SphereSixComplex.Topology.ActualCuspCentralFiberRetraction
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# The central-fibre orbit quotient

The phase-corrected lattice action preserves the prequotient central fibre.  Restricting the
action to that invariant subspace and then taking its orbit quotient gives exactly the quotient
central fibre already defined as a subspace of the local cusp filling.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- The prequotient central fibre as an invariant subspace of the actual cusp action. -/
public noncomputable def actualLocalCuspCentralSubMulAction
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := actualLocalCuspQuotientAction W
    SubMulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) := by
  letI := actualLocalCuspQuotientAction W
  refine { carrier := actualLocalCuspCentralFiber W, smul_mem' := ?_ }
  intro g p hp
  change M.t ((g • p : LocalCarrier M W.localWitness.radius) : M.Carrier) = 0
  let C :=
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  change M.t ((C.toCuspActionData W.localWitness.fixedPoint).psiMap
    (Multiplicative.toAdd g) p : LocalCarrier M W.localWitness.radius) = 0
  rw [← C.psiMap_eq_generic, C.psiMap_preserves_t]
  exact hp

/-- The orbit quotient of the actual prequotient central fibre. -/
public noncomputable abbrev ActualLocalCuspCentralOrbitQuotient
    (W : ActualPuncturedCuspCollarWitness N M) :=
  letI := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  letI : MulAction (Multiplicative ParameterLattice) S := inferInstance
  Quotient (MulAction.orbitRel (Multiplicative ParameterLattice) S)

/-- The restricted central-fibre quotient map into the full local cusp filling. -/
public noncomputable def actualLocalCuspCentralOrbitMap
    (W : ActualPuncturedCuspCollarWitness N M) :
    ActualLocalCuspCentralOrbitQuotient W → actualLocalCuspFilling W := by
  letI := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  letI : MulAction (Multiplicative ParameterLattice) S := inferInstance
  exact Quotient.lift
    (fun x : S => Quotient.mk (MulAction.orbitRel
      (Multiplicative ParameterLattice) (LocalCarrier M W.localWitness.radius)) x.1)
    (by
      intro x y h
      apply Quotient.sound
      rw [SubMulAction.orbitRel_of_subMul] at h
      exact h)

public theorem actualLocalCuspCentralOrbitMap_injective
    (W : ActualPuncturedCuspCollarWitness N M) :
    Function.Injective (actualLocalCuspCentralOrbitMap W) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  intro a b
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      intro h
      apply Quotient.sound
      rw [SubMulAction.orbitRel_of_subMul]
      change (Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
        (LocalCarrier M W.localWitness.radius)) x.1) =
        Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
          (LocalCarrier M W.localWitness.radius)) y.1 at h
      exact @Quotient.exact _ (MulAction.orbitRel (Multiplicative ParameterLattice)
        (LocalCarrier M W.localWitness.radius)) x.1 y.1 h

/-- The central orbit quotient has the subspace topology inherited from the full cusp filling. -/
public theorem actualLocalCuspCentralOrbitMap_isEmbedding
    (W : ActualPuncturedCuspCollarWitness N M) :
    Topology.IsEmbedding (actualLocalCuspCentralOrbitMap W) := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) := actualLocalPsiContinuousConstSMul W
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice) S :=
    ⟨fun g => ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩
  apply isEmbedding_of_isOpenQuotientMap_of_isInducing
    (f := (Subtype.val : S → LocalCarrier M W.localWitness.radius))
    (p := Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice) S))
    (q := Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius)))
  · rfl
  · exact Topology.IsInducing.subtypeVal
  · exact isQuotientMap_quotient_mk'
  · exact MulAction.isOpenQuotientMap_quotientMk
  · exact actualLocalCuspCentralOrbitMap_injective W
  · rintro x ⟨_, ⟨z, rfl⟩, hx⟩
    refine ⟨⟨x, ?_⟩, rfl⟩
    have horbit : MulAction.orbitRel (Multiplicative ParameterLattice)
        (LocalCarrier M W.localWitness.radius) x z :=
      @Quotient.exact _ (MulAction.orbitRel (Multiplicative ParameterLattice)
        (LocalCarrier M W.localWitness.radius)) x z hx.symm
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
    obtain ⟨g, rfl⟩ := horbit
    exact S.smul_mem' g z.property

public theorem actualLocalCuspCentralOrbitMap_mem_quotientCentralFiber
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W)
    (q : ActualLocalCuspCentralOrbitQuotient W) :
    actualLocalCuspCentralOrbitMap W q ∈ R.quotientCentralFiber W := by
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨x.1, x.2, rfl⟩

/-- The central orbit quotient map with codomain restricted to the quotient central fibre. -/
public noncomputable def actualLocalCuspCentralOrbitCoreMap
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    ActualLocalCuspCentralOrbitQuotient W → R.quotientCentralFiber W :=
  Set.codRestrict (actualLocalCuspCentralOrbitMap W) _
    (actualLocalCuspCentralOrbitMap_mem_quotientCentralFiber W R)

public theorem actualLocalCuspCentralOrbitCoreMap_surjective
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    Function.Surjective (actualLocalCuspCentralOrbitCoreMap W R) := by
  intro q
  obtain ⟨x, hx, heq⟩ := q.2
  let _ := actualLocalCuspQuotientAction W
  let S := actualLocalCuspCentralSubMulAction W
  let _ : MulAction (Multiplicative ParameterLattice) S := inferInstance
  refine ⟨Quotient.mk _ (⟨x, hx⟩ : S), ?_⟩
  apply Subtype.ext
  exact heq

/-- The quotient central fibre is canonically the orbit quotient of the invariant central
subspace, with its quotient topology. -/
public noncomputable def actualLocalCuspCentralOrbitCoreHomeomorph
    (W : ActualPuncturedCuspCollarWitness N M)
    (R : ActualLocalCuspCentralFiberRetractionData W) :
    ActualLocalCuspCentralOrbitQuotient W ≃ₜ R.quotientCentralFiber W :=
  (actualLocalCuspCentralOrbitMap_isEmbedding W).codRestrict _
      (actualLocalCuspCentralOrbitMap_mem_quotientCentralFiber W R)
    |>.toHomeomorphOfSurjective (actualLocalCuspCentralOrbitCoreMap_surjective W R)

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end
