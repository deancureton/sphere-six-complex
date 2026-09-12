module

public import SphereSixComplex.Paper.Geometry.CuspPeriodExpansion
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The phase-corrected action on a local cusp neighbourhood

The cusp coefficients are holomorphic only on their convergence disc.  Accordingly this file
restricts the standard toric model to the open set where the height character lies in that disc.
All algebraic and quotient constructions are performed on this open complex submanifold.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric

namespace CuspLocalPhaseAction

/-- The open part of the toric model lying over the radius-`r` cusp disc. -/
public def cuspNeighborhood (M : Model) (r : ℝ) : TopologicalSpace.Opens M.Carrier where
  carrier := M.t ⁻¹' Metric.ball 0 r
  is_open' := Metric.isOpen_ball.preimage M.t_holomorphic.continuous

/-- The carrier of the local toric cusp model. -/
public abbrev localCarrier (M : Model) (r : ℝ) := cuspNeighborhood M r

@[simp]
public theorem mem_cuspNeighborhood_iff (M : Model) (r : ℝ) (p : M.Carrier) :
    p ∈ cuspNeighborhood M r ↔ M.t p ∈ Metric.ball 0 r :=
  Iff.rfl

/-- The height character restricted to the local carrier. -/
public def localT (M : Model) (r : ℝ) (p : localCarrier M r) : ℂ :=
  M.t p

/-- A fan shear restricted to the invariant cusp neighbourhood. -/
public def localFanShearEquiv (M : Model) (r : ℝ) (lambda : ParameterLattice) :
    Equiv.Perm (localCarrier M r) :=
  Equiv.subtypeEquiv (Additive.toMul (M.fanShear lambda)) fun p ↦ by
    change M.t p ∈ Metric.ball 0 r ↔
      M.t (Additive.toMul (M.fanShear lambda) p) ∈ Metric.ball 0 r
    rw [M.fanShear_preserves_t]


@[simp]
public theorem localFanShearEquiv_coe
    (M : Model) (r : ℝ) (lambda : ParameterLattice) (p : localCarrier M r) :
    ((localFanShearEquiv M r lambda p : localCarrier M r) : M.Carrier) =
      Additive.toMul (M.fanShear lambda) p :=
  rfl

/-- The restricted fan shears still form an additive family of permutations. -/
public def localFanShear (M : Model) (r : ℝ) :
    ParameterLattice →+ Additive (Equiv.Perm (localCarrier M r)) where
  toFun lambda := Additive.ofMul (localFanShearEquiv M r lambda)
  map_zero' := by
    apply Additive.toMul.injective
    ext p
    simp [localFanShearEquiv]
  map_add' lambda mu := by
    apply Additive.toMul.injective
    ext p
    simp [localFanShearEquiv, map_add, Equiv.Perm.mul_apply]

/-- A constant phase translation restricted to the invariant cusp neighbourhood. -/
public def localPhaseActionEquiv (M : Model) (r : ℝ) (c : Phase) :
    Equiv.Perm (localCarrier M r) :=
  Equiv.subtypeEquiv (CuspToricPhaseAction.ToricModel.phaseAction M c) fun p ↦ by
    change M.t p ∈ Metric.ball 0 r ↔
      M.t (CuspToricPhaseAction.ToricModel.phaseAction M c p) ∈ Metric.ball 0 r
    rw [CuspToricPhaseAction.ToricModel.phaseAction_preserves_t]

@[simp]
public theorem localPhaseActionEquiv_coe
    (M : Model) (r : ℝ) (c : Phase) (p : localCarrier M r) :
    ((localPhaseActionEquiv M r c p : localCarrier M r) : M.Carrier) =
      CuspToricPhaseAction.ToricModel.phaseAction M c p :=
  rfl

/-- The restricted phase translations form a group action. -/
public def localPhaseAction (M : Model) (r : ℝ) :
    Phase →* Equiv.Perm (localCarrier M r) where
  toFun c := localPhaseActionEquiv M r c
  map_one' := by
    ext p
    simp [localPhaseActionEquiv]
  map_mul' c d := by
    ext p
    simp [localPhaseActionEquiv, Equiv.Perm.mul_apply]

/-- The variable phase twist on the local carrier. -/
public def localPhaseTwist (M : Model) (r : ℝ)
    (phase : ParameterLattice → ℂ → Phase) (lambda : ParameterLattice) :
    localCarrier M r → localCarrier M r := fun p ↦
  localPhaseActionEquiv M r (phase lambda (M.t p)) p

/-- Exact phase data on one cusp disc.  The standard joint toric-action theorem turns
coefficientwise holomorphicity into holomorphicity of the variable phase twist on the
corresponding open toric submanifold. -/
public structure LocalHolomorphicPhaseCoefficients (r : ℝ) where
  radius_pos : 0 < r
  phase : ParameterLattice → ℂ → Phase
  phase_zero : ∀ q, phase 0 q = 1
  phase_add : ∀ lambda mu q, phase (lambda + mu) q = phase lambda q * phase mu q
  coefficient_holomorphicOn : ∀ lambda i,
    DifferentiableOn ℂ (fun q ↦ (phase lambda q i : ℂ)) (Metric.ball 0 r)

namespace LocalHolomorphicPhaseCoefficients

variable {M : Model} {r : ℝ} (C : LocalHolomorphicPhaseCoefficients r)

/-- Each variable phase coordinate is holomorphic after composition with the height character on
the local carrier. -/
public theorem phase_comp_t_holomorphic
    (lambda : ParameterLattice) (i : Fin 2) :
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞
      (fun p : localCarrier M r ↦ (C.phase lambda (M.t p) i : ℂ)) := by
  have hphase : ContMDiffOn (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ∞ (fun q ↦ (C.phase lambda q i : ℂ))
      (Metric.ball 0 r) :=
    contMDiffOn_iff_contDiffOn.mpr
      ((C.coefficient_holomorphicOn lambda i).contDiffOn Metric.isOpen_ball)
  have ht : ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞ (fun p : localCarrier M r ↦ M.t p) :=
    M.t_holomorphic.comp contMDiff_subtype_val
  exact hphase.comp_contMDiff ht fun p ↦ p.property

/-- The standard jointly holomorphic toric action makes the variable phase twist holomorphic on
the cusp neighbourhood. -/
public theorem localPhaseTwist_holomorphic (lambda : ParameterLattice) :
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (localPhaseTwist M r C.phase lambda) := by
  rw [← ContMDiff.subtypeVal_comp_iff (cuspNeighborhood M r)]
  change ContMDiff (modelWithCornersSelf ℂ ComplexModel)
    (modelWithCornersSelf ℂ ComplexModel) ∞
    (fun p : localCarrier M r ↦ M.torusAction
      (phaseEmbedding (C.phase lambda (M.t p))) (p : M.Carrier))
  apply M.variableTorusAction_holomorphic
  intro i
  fin_cases i
  · exact C.phase_comp_t_holomorphic lambda 0
  · exact C.phase_comp_t_holomorphic lambda 1
  · exact contMDiff_const

/-- The local phase-corrected map. -/
public def psiMap (lambda : ParameterLattice) (p : localCarrier M r) : localCarrier M r :=
  localPhaseTwist M r C.phase lambda (localFanShearEquiv M r lambda p)

@[simp]
public theorem psiMap_coe (lambda : ParameterLattice) (p : localCarrier M r) :
    ((C.psiMap lambda p : localCarrier M r) : M.Carrier) =
      CuspToricPhaseAction.ToricModel.phaseAction M (C.phase lambda (M.t p))
        (Additive.toMul (M.fanShear lambda) p) := by
  simp [psiMap, localPhaseTwist, M.fanShear_preserves_t]

/-- The local phase-corrected maps preserve the height character and hence the cusp disc. -/
public theorem psiMap_preserves_t (lambda : ParameterLattice) (p : localCarrier M r) :
    M.t (C.psiMap lambda p) = M.t p := by
  rw [psiMap_coe, CuspToricPhaseAction.ToricModel.phaseAction_preserves_t,
    M.fanShear_preserves_t]

@[simp]
public theorem psiMap_zero (p : localCarrier M r) : C.psiMap 0 p = p := by
  apply Subtype.ext
  simp [psiMap_coe, C.phase_zero]

/-- The local phase-corrected maps form the lattice action. -/
public theorem psiMap_add
    (lambda mu : ParameterLattice) (p : localCarrier M r) :
    C.psiMap (lambda + mu) p = C.psiMap lambda (C.psiMap mu p) := by
  apply Subtype.ext
  simp only [psiMap_coe]
  rw [C.phase_add, AddMonoidHom.map_add]
  change CuspToricPhaseAction.ToricModel.phaseAction M
      (C.phase lambda (M.t p) * C.phase mu (M.t p))
      ((Additive.toMul (M.fanShear lambda) *
        Additive.toMul (M.fanShear mu)) p) = _
  rw [map_mul, Equiv.Perm.mul_apply,
    CuspToricPhaseAction.ToricModel.fanShear_phase_commute, Equiv.Perm.mul_apply]
  rw [CuspToricPhaseAction.ToricModel.phaseAction_preserves_t,
    M.fanShear_preserves_t]

/-- Restricted fan shears are biholomorphic on the open cusp submanifold. -/
public theorem localFanShear_holomorphic (lambda : ParameterLattice) :
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (localFanShearEquiv M r lambda) := by
  rw [← ContMDiff.subtypeVal_comp_iff (cuspNeighborhood M r)]
  change ContMDiff (modelWithCornersSelf ℂ ComplexModel)
    (modelWithCornersSelf ℂ ComplexModel) ∞
    (fun p : localCarrier M r ↦ Additive.toMul (M.fanShear lambda) (p : M.Carrier))
  exact (M.fanShear_holomorphic lambda).comp contMDiff_subtype_val

/-- The local phase-corrected maps are holomorphic. -/
public theorem psiMap_holomorphic (lambda : ParameterLattice) :
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (C.psiMap (M := M) lambda) := by
  exact (C.localPhaseTwist_holomorphic lambda).comp
    (localFanShear_holomorphic (M := M) (r := r) lambda)

/-- Every point has trivial stabilizer under the phase-corrected action. -/
public def IsFree : Prop :=
  ∀ lambda (p : localCarrier M r), C.psiMap lambda p = p → lambda = 0


/-- The local algebraic action data obtained from the restricted fan and phase actions. -/
public def toCuspActionData :
    CuspActionData (localCarrier M r) Phase where
  t := localT M r
  toricShear := localFanShear M r
  phaseAction := localPhaseAction M r
  phase := C.phase
  phase_zero := C.phase_zero
  phase_add := C.phase_add
  shear_preserves_t lambda p := by
    simp [localT, localFanShear, localFanShearEquiv, M.fanShear_preserves_t]
  phase_preserves_t c p := by
    change M.t (CuspToricPhaseAction.ToricModel.phaseAction M c (p : M.Carrier)) = M.t p
    exact CuspToricPhaseAction.ToricModel.phaseAction_preserves_t M c p
  shear_phase_commute lambda c p := by
    apply Subtype.ext
    exact CuspToricPhaseAction.ToricModel.fanShear_phase_commute M lambda c p


@[simp]
public theorem psiMap_eq_generic
    (lambda : ParameterLattice) (p : localCarrier M r) :
    C.psiMap lambda p = (C.toCuspActionData (M := M)).psiMap lambda p := by
  apply Subtype.ext
  simp [psiMap, localPhaseTwist, CuspActionData.psiMap, toCuspActionData,
    localT, localFanShear, localPhaseAction, M.fanShear_preserves_t]

/-- Holomorphicity in the generic local action package. -/
public theorem genericPsiMap_holomorphic
    (lambda : ParameterLattice) :
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      ((C.toCuspActionData (M := M)).psiMap lambda) := by
  convert C.psiMap_holomorphic lambda using 1
  funext p
  exact (C.psiMap_eq_generic lambda p).symm

public theorem isCancelSMul (F : C.IsFree (M := M)) :
    letI := (C.toCuspActionData (M := M)).psiAction
    IsCancelSMul (Multiplicative ParameterLattice) (localCarrier M r) := by
  apply (C.toCuspActionData (M := M)).isCancelSMul
  intro lambda p hp
  rw [← C.psiMap_eq_generic] at hp
  exact F lambda p hp

/-- The remaining compact-overlap estimate on the restricted cusp carrier. -/
public def CompactOverlapEstimate : Prop :=
  ∀ K L : Set (localCarrier M r), IsCompact K → IsCompact L →
    {lambda : ParameterLattice | (C.psiMap lambda '' K ∩ L).Nonempty}.Finite

/-- The fixed-point and compact-overlap estimates give a free properly discontinuous action on
the local cusp carrier. -/
public theorem properlyDiscontinuous
    (H : C.CompactOverlapEstimate (M := M)) :
    letI := (C.toCuspActionData (M := M)).psiAction
    ProperlyDiscontinuousSMul
      (Multiplicative ParameterLattice) (localCarrier M r) := by
  apply (C.toCuspActionData (M := M)).properlyDiscontinuous
  intro K L hK hL
  simpa only [← C.psiMap_eq_generic] using H K L hK hL

/-- The local cusp quotient map is a quotient covering map. -/
public theorem quotient_isQuotientCoveringMap (F : C.IsFree (M := M))
    (H : C.CompactOverlapEstimate (M := M)) :
    letI := (C.toCuspActionData (M := M)).psiAction
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel
        (Multiplicative ParameterLattice) (localCarrier M r)))
      (Multiplicative ParameterLattice) := by
  let _ : LocallyCompactSpace M.Carrier :=
    ChartedSpace.locallyCompactSpace ComplexModel M.Carrier
  let _ : LocallyCompactSpace (localCarrier M r) :=
    (cuspNeighborhood M r).isOpen.locallyCompactSpace
  apply CuspFilling.quotient_isQuotientCoveringMap (C.toCuspActionData (M := M)) (C.isCancelSMul F)
  · intro lambda
    convert (C.psiMap_holomorphic lambda).continuous using 1
    funext p
    exact (C.psiMap_eq_generic lambda p).symm
  · intro K L hK hL
    simpa only [← C.psiMap_eq_generic] using H K L hK hL


/-- The local cusp quotient is a complex manifold once the same two fixed-point estimates and
compact-overlap estimate used in the global formulation are supplied on the restricted carrier. -/
public theorem quotient_isManifold (F : C.IsFree (M := M))
    (H : C.CompactOverlapEstimate (M := M)) :
    letI := (C.toCuspActionData (M := M)).psiAction
    let hf := C.quotient_isQuotientCoveringMap F H
    letI : ChartedSpace ComplexModel
      (MulAction.orbitRel.Quotient
        (Multiplicative ParameterLattice) (localCarrier M r)) :=
      hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
    IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (MulAction.orbitRel.Quotient
        (Multiplicative ParameterLattice) (localCarrier M r)) := by
  let _ := (C.toCuspActionData (M := M)).psiAction
  let _ : LocallyCompactSpace M.Carrier :=
    ChartedSpace.locallyCompactSpace ComplexModel M.Carrier
  let _ : LocallyCompactSpace (localCarrier M r) :=
    (cuspNeighborhood M r).isOpen.locallyCompactSpace
  let hf := C.quotient_isQuotientCoveringMap F H
  let _ : ContinuousConstSMul
      (Multiplicative ParameterLattice) (localCarrier M r) :=
    ⟨fun gamma ↦ (C.genericPsiMap_holomorphic (Multiplicative.toAdd gamma)).continuous⟩
  let _ : ChartedSpace ComplexModel
      (MulAction.orbitRel.Quotient
        (Multiplicative ParameterLattice) (localCarrier M r)) :=
    hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
  apply CuspFilling.quotient_isManifold (modelWithCornersSelf ℂ ComplexModel) hf
  intro gamma
  exact C.genericPsiMap_holomorphic (Multiplicative.toAdd gamma)

end LocalHolomorphicPhaseCoefficients

end CuspLocalPhaseAction

end SphereSixComplex.Geometry
