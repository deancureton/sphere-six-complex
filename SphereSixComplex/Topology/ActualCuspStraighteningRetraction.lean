module

public import SphereSixComplex.Geometry.EstablishedContinuousTorusAction
public import SphereSixComplex.Topology.ActualCuspCentralFiberRetraction

/-!
# Straightening the actual cusp action

The homeomorphism of Lemma 7.5 conjugates the actual deck action to the action with its complex
phase frozen at the central parameter.  This file makes that action and conjugacy explicit.  It
does not assume or assert the remaining phase-spreading deformation retraction for the frozen
action.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.CuspStraighteningRetraction

open SphereSixComplex.Periods
open CuspFilling CuspLocalPhaseAction CuspPuncturedCollarBridge
open CuspPeriodExpansion CuspStraighteningAlgebra CuspStraighteningExtension
open CuspStraighteningHomeomorph CuspToricPhaseAction
open StandardInfiniteA2ToricModel
open CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate

/-- The deck map with the complex phase coefficient frozen at the central parameter. -/
public def frozenLocalPsiMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (lambda : ParameterLattice) : LocalCarrier M r → LocalCarrier M r :=
  fun p ↦ localPhaseActionEquiv M r (N.phaseCoefficient lambda 0)
    (localFanShearEquiv M r lambda p)

@[simp]
public theorem frozenLocalPsiMap_coe
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (lambda : ParameterLattice) (p : LocalCarrier M r) :
    ((frozenLocalPsiMap N M r lambda p : LocalCarrier M r) : M.Carrier) =
      ToricModel.phaseAction M (N.phaseCoefficient lambda 0)
        (Additive.toMul (M.fanShear lambda) p) :=
  rfl

public theorem frozenLocalPsiMap_zero
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (p : LocalCarrier M r) : frozenLocalPsiMap N M r 0 p = p := by
  apply Subtype.ext
  simp [frozenLocalPsiMap, N.phaseCoefficient_zero]

public theorem frozenLocalPsiMap_add
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (lambda mu : ParameterLattice) (p : LocalCarrier M r) :
    frozenLocalPsiMap N M r (lambda + mu) p =
      frozenLocalPsiMap N M r lambda (frozenLocalPsiMap N M r mu p) := by
  apply Subtype.ext
  simp only [frozenLocalPsiMap_coe, N.phaseCoefficient_add, AddMonoidHom.map_add]
  change ToricModel.phaseAction M
      (N.phaseCoefficient lambda 0 * N.phaseCoefficient mu 0)
      ((Additive.toMul (M.fanShear lambda) * Additive.toMul (M.fanShear mu)) p) = _
  rw [map_mul, Equiv.Perm.mul_apply, ToricModel.fanShear_phase_commute,
    Equiv.Perm.mul_apply]

/-- The frozen maps form the lattice action conjugate to the actual cusp action. -/
@[instance_reducible]
public def frozenLocalCuspAction
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ) :
    MulAction (Multiplicative ParameterLattice) (LocalCarrier M r) where
  smul g p := frozenLocalPsiMap N M r (Multiplicative.toAdd g) p
  one_smul p := frozenLocalPsiMap_zero N M r p
  mul_smul g h p := frozenLocalPsiMap_add N M r
    (Multiplicative.toAdd g) (Multiplicative.toAdd h) p

/-- Every fixed frozen deck transformation is continuous. -/
public theorem frozenLocalCuspContinuousConstSMul
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ) :
    letI := frozenLocalCuspAction N M r
    ContinuousConstSMul (Multiplicative ParameterLattice) (LocalCarrier M r) := by
  let _ := frozenLocalCuspAction N M r
  constructor
  intro g
  apply Continuous.subtype_mk
  exact (M.torusAction_holomorphic
      (phaseEmbedding (N.phaseCoefficient (Multiplicative.toAdd g) 0))).continuous.comp
    ((M.fanShear_holomorphic (Multiplicative.toAdd g)).continuous.comp
      continuous_subtype_val)

/-- Straightening conjugates the actual local deck maps to the frozen deck maps. -/
public theorem pointStraightening_actualPsiMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (lambda : ParameterLattice) (p : LocalCarrier M W.localWitness.radius) :
    let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_le
    pointStraightening W (C.psiMap lambda p) =
      frozenLocalPsiMap N M W.localWitness.radius lambda (pointStraightening W p) := by
  let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_le
  change pointStraightening W (C.psiMap lambda p) =
    frozenLocalPsiMap N M W.localWitness.radius lambda (pointStraightening W p)
  by_cases hp : M.t p = 0
  · have hpsi : M.t (C.psiMap lambda p) = 0 := by
      rw [C.psiMap_preserves_t, hp]
    rw [pointStraightening_of_t_eq_zero W p hp,
      pointStraightening_of_t_eq_zero W (C.psiMap lambda p) hpsi]
    apply Subtype.ext
    rw [C.psiMap_coe, frozenLocalPsiMap_coe, hp]
    rfl
  · have hpsi : M.t (C.psiMap lambda p) ≠ 0 := by
      rw [C.psiMap_preserves_t]
      exact hp
    rw [pointStraightening_of_t_ne_zero W (C.psiMap lambda p) hpsi,
      pointStraightening_of_t_ne_zero W p hp]
    apply Subtype.ext
    exact puncturedPointStraightening_psiMap W lambda p hp

/-- The same conjugation formula for the generic action map used definitionally by the
quotient. -/
public theorem pointStraightening_genericPsiMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (lambda : ParameterLattice) (p : LocalCarrier M W.localWitness.radius) :
    let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_le
    pointStraightening W
        ((C.toCuspActionData W.localWitness.fixedPoint).psiMap lambda p) =
      frozenLocalPsiMap N M W.localWitness.radius lambda (pointStraightening W p) := by
  let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_le
  change pointStraightening W
      ((C.toCuspActionData W.localWitness.fixedPoint).psiMap lambda p) = _
  rw [← C.psiMap_eq_generic W.localWitness.fixedPoint,
    pointStraightening_actualPsiMap W]

/-- The orbit relation for the frozen local action. -/
public noncomputable def frozenLocalCuspOrbitRel
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ) :
    Setoid (LocalCarrier M r) :=
  letI := frozenLocalCuspAction N M r
  MulAction.orbitRel (Multiplicative ParameterLattice) _

/-- The local quotient for the action with phase frozen at the central parameter. -/
public noncomputable abbrev FrozenLocalCuspFilling
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ) :=
  Quotient (frozenLocalCuspOrbitRel N M r)

/-- Straightening respects the actual and frozen orbit relations. -/
public theorem pointStraightening_respects_orbitRel
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) {a b : LocalCarrier M W.localWitness.radius}
    (hab : actualLocalPsiOrbitRel W a b) :
    frozenLocalCuspOrbitRel N M W.localWitness.radius
      (pointStraightening W a) (pointStraightening W b) := by
  let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_le
  let _ := actualLocalCuspQuotientAction W
  change MulAction.orbitRel (Multiplicative ParameterLattice)
    (LocalCarrier M W.localWitness.radius) a b at hab
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab
  obtain ⟨g, hg⟩ := hab
  have hg' : C.psiMap (Multiplicative.toAdd g) b = a :=
    (C.psiMap_eq_generic W.localWitness.fixedPoint _ _).trans hg
  let _ := frozenLocalCuspAction N M W.localWitness.radius
  change MulAction.orbitRel (Multiplicative ParameterLattice)
    (LocalCarrier M W.localWitness.radius)
      (pointStraightening W a) (pointStraightening W b)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨g, ?_⟩
  change frozenLocalPsiMap N M W.localWitness.radius
    (Multiplicative.toAdd g) (pointStraightening W b) = pointStraightening W a
  rw [← pointStraightening_actualPsiMap W (Multiplicative.toAdd g) b, hg']

/-- Unstraightening respects the frozen and actual orbit relations. -/
public theorem actualPsiMap_pointUnstraightening
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (lambda : ParameterLattice) (p : LocalCarrier M W.localWitness.radius) :
    let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_le
    C.psiMap lambda (pointUnstraightening W p) =
      pointUnstraightening W (frozenLocalPsiMap N M W.localWitness.radius lambda p) := by
  let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_le
  change C.psiMap lambda (pointUnstraightening W p) =
    pointUnstraightening W (frozenLocalPsiMap N M W.localWitness.radius lambda p)
  apply Function.LeftInverse.injective (pointUnstraightening_pointStraightening W)
  rw [pointStraightening_actualPsiMap W, pointStraightening_pointUnstraightening,
    pointStraightening_pointUnstraightening]

/-- The straightening homeomorphism descends from the actual filling quotient to the frozen
quotient. -/
public noncomputable def quotientStraighteningHomeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    actualLocalCuspFilling W ≃ₜ FrozenLocalCuspFilling N M W.localWitness.radius :=
  let J := StandardInfiniteA2ToricModel.Established.establishedContinuousTorusAction M
  Homeomorph.Quotient.congr (pointStraighteningHomeomorph J W) fun x y ↦ by
    let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_le
    unfold frozenLocalCuspOrbitRel
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      have hg' : (C.toCuspActionData W.localWitness.fixedPoint).psiMap
          (Multiplicative.toAdd g) y = x := hg
      change frozenLocalPsiMap N M W.localWitness.radius (Multiplicative.toAdd g)
        (pointStraightening W y) = pointStraightening W x
      rw [← pointStraightening_genericPsiMap W, hg']
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      have hg' : frozenLocalPsiMap N M W.localWitness.radius
          (Multiplicative.toAdd g) (pointStraightening W y) = pointStraightening W x := hg
      apply Function.LeftInverse.injective (pointUnstraightening_pointStraightening W)
      change pointStraightening W
        ((C.toCuspActionData W.localWitness.fixedPoint).psiMap
          (Multiplicative.toAdd g) y) = pointStraightening W x
      rw [pointStraightening_genericPsiMap W]
      exact hg'

end SphereSixComplex.Geometry.CuspStraighteningRetraction
