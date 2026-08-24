module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

/-!
# Phase-corrected action on the standard cusp toric model

This file instantiates the algebraic part of `CuspActionData` from the standard toric model and
exact holomorphic phase coefficients.  The paper-specific fixed-point and compact-overlap
estimates remain explicit hypotheses.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

namespace SphereSixComplex.Geometry.CuspToricPhaseAction

/-- The two-dimensional phase subgroup of the dense torus. -/
public abbrev Phase := Fin 2 → ℂˣ

/-- Embed the phase subgroup into the dense three-torus with third coordinate one. -/
public def phaseEmbedding : Phase →* DenseTorus where
  toFun c := ![c 0, c 1, 1]
  map_one' := by
    ext i
    fin_cases i <;> rfl
  map_mul' c d := by
    ext i
    fin_cases i <;> simp

@[simp]
public theorem phaseEmbedding_apply_zero (c : Phase) : phaseEmbedding c 0 = c 0 :=
  rfl

@[simp]
public theorem phaseEmbedding_apply_one (c : Phase) : phaseEmbedding c 1 = c 1 :=
  rfl

@[simp]
public theorem phaseEmbedding_apply_two (c : Phase) : phaseEmbedding c 2 = 1 :=
  rfl

/-- Integral fan shears commute with multiplication by the phase subgroup on the dense torus. -/
public theorem denseTorusShear_phase_commute
    (lambda : ParameterLattice) (c : Phase) (x : DenseTorus) :
    denseTorusShear lambda (phaseEmbedding c * x) =
      phaseEmbedding c * denseTorusShear lambda x := by
  ext i
  fin_cases i <;> simp [denseTorusShear, mul_assoc]

namespace ToricModel

variable (M : Model)

/-- The phase subgroup action obtained by restricting the toric action. -/
public def phaseAction : Phase →* Equiv.Perm M.Carrier :=
  M.torusAction.comp phaseEmbedding

@[simp]
public theorem phaseAction_apply (c : Phase) (p : M.Carrier) :
    phaseAction M c p = M.torusAction (phaseEmbedding c) p :=
  rfl

/-- The restricted phase action preserves the height character. -/
public theorem phaseAction_preserves_t (c : Phase) (p : M.Carrier) :
    M.t (phaseAction M c p) = M.t p := by
  rw [phaseAction_apply, M.t_torusAction, phaseEmbedding_apply_two]
  simp

/-- Fan shears and phase multiplication agree on the dense torus. -/
public theorem fanShear_phase_commute_on_torus
    (lambda : ParameterLattice) (c : Phase) (x : DenseTorus) :
    Additive.toMul (M.fanShear lambda)
        (phaseAction M c (M.torusEmbedding x)) =
      phaseAction M c
        (Additive.toMul (M.fanShear lambda) (M.torusEmbedding x)) := by
  rw [phaseAction_apply, phaseAction_apply, M.torusAction_torus,
    M.fanShear_torus, M.fanShear_torus, M.torusAction_torus,
    denseTorusShear_phase_commute]

/-- Fan shears commute globally with the phase subgroup.  The equality is extended from the
dense torus because both sides are continuous and the toric variety is Hausdorff. -/
public theorem fanShear_phase_commute
    (lambda : ParameterLattice) (c : Phase) (p : M.Carrier) :
    Additive.toMul (M.fanShear lambda) (phaseAction M c p) =
      phaseAction M c (Additive.toMul (M.fanShear lambda) p) := by
  let f : M.Carrier → M.Carrier := fun q ↦
    Additive.toMul (M.fanShear lambda) (phaseAction M c q)
  let g : M.Carrier → M.Carrier := fun q ↦
    phaseAction M c (Additive.toMul (M.fanShear lambda) q)
  have hf : Continuous f := by
    dsimp [f, phaseAction]
    exact
    (M.fanShear_holomorphic lambda).continuous.comp
      (M.torusAction_holomorphic (phaseEmbedding c)).continuous
  have hg : Continuous g := by
    dsimp [g, phaseAction]
    exact (M.torusAction_holomorphic (phaseEmbedding c)).continuous.comp
      (M.fanShear_holomorphic lambda).continuous
  have hfg : f ∘ M.torusEmbedding = g ∘ M.torusEmbedding := by
    funext x
    exact fanShear_phase_commute_on_torus M lambda c x
  exact congrFun (M.torus_dense.equalizer hf hg hfg) p

end ToricModel

/-- Exact phase coefficients used in the cusp correction.  In addition to coefficientwise
holomorphicity, `twist_holomorphic` records the directly usable chartwise consequence for the
variable torus translation.  This is an explicit analytic input, not an axiom. -/
public structure ExactHolomorphicPhaseCoefficients (M : Model) where
  phase : ParameterLattice → ℂ → Phase
  phase_zero : ∀ z, phase 0 z = 1
  phase_add : ∀ lambda mu z,
    phase (lambda + mu) z = phase lambda z * phase mu z
  coefficient_holomorphic : ∀ lambda i,
    Differentiable ℂ (fun z ↦ (phase lambda z i : ℂ))
  twist_holomorphic : ∀ lambda,
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (fun p : M.Carrier ↦ ToricModel.phaseAction M (phase lambda (M.t p)) p)

namespace ExactHolomorphicPhaseCoefficients

variable {M : Model} (C : ExactHolomorphicPhaseCoefficients M)

/-- The two fixed-point estimates isolated from the algebraic and holomorphic construction. -/
public structure FixedPointEstimates : Prop where
  offCentral : ∀ lambda p, M.t p ≠ 0 →
    ToricModel.phaseAction M (C.phase lambda (M.t p))
        (Additive.toMul (M.fanShear lambda) p) = p →
      lambda = 0
  central : ∀ lambda p, M.t p = 0 →
    ToricModel.phaseAction M (C.phase lambda (M.t p))
        (Additive.toMul (M.fanShear lambda) p) = p →
      lambda = 0

/-- Instantiate the generic cusp-action package once the two paper-specific fixed-point
estimates have been proved. -/
public def toCuspActionData (F : C.FixedPointEstimates) :
    CuspActionData M.Carrier Phase where
  t := M.t
  toricShear := M.fanShear
  phaseAction := ToricModel.phaseAction M
  phase := C.phase
  phase_zero := C.phase_zero
  phase_add := C.phase_add
  shear_preserves_t := M.fanShear_preserves_t
  phase_preserves_t := ToricModel.phaseAction_preserves_t M
  shear_phase_commute := ToricModel.fanShear_phase_commute M
  fixed_off_central := F.offCentral
  fixed_central := F.central

/-- The specialized phase-corrected map. -/
public def psiMap (lambda : ParameterLattice) (p : M.Carrier) : M.Carrier :=
  ToricModel.phaseAction M (C.phase lambda (M.t p))
    (Additive.toMul (M.fanShear lambda) p)

@[simp]
public theorem psiMap_eq_generic (F : C.FixedPointEstimates)
    (lambda : ParameterLattice) (p : M.Carrier) :
    C.psiMap lambda p = (C.toCuspActionData F).psiMap lambda p :=
  rfl

/-- The phase-corrected maps form an additive action. -/
public theorem psiMap_add
    (lambda mu : ParameterLattice) (p : M.Carrier) :
    C.psiMap (lambda + mu) p = C.psiMap lambda (C.psiMap mu p) := by
  have ht : M.t (ToricModel.phaseAction M (C.phase mu (M.t p))
      (Additive.toMul (M.fanShear mu) p)) = M.t p := by
    rw [ToricModel.phaseAction_preserves_t, M.fanShear_preserves_t]
  simp only [psiMap, C.phase_add]
  rw [ht, AddMonoidHom.map_add]
  change ToricModel.phaseAction M (C.phase lambda (M.t p) * C.phase mu (M.t p))
      ((Additive.toMul (M.fanShear lambda) *
        Additive.toMul (M.fanShear mu)) p) = _
  rw [map_mul, Equiv.Perm.mul_apply, ToricModel.fanShear_phase_commute]
  rw [Equiv.Perm.mul_apply]

/-- The phase-corrected maps preserve the height character. -/
public theorem psiMap_preserves_t
    (lambda : ParameterLattice) (p : M.Carrier) :
    M.t (C.psiMap lambda p) = M.t p := by
  rw [psiMap, ToricModel.phaseAction_preserves_t, M.fanShear_preserves_t]

/-- Holomorphicity of the phase-corrected map follows from holomorphicity of the fan shear and
of the exact variable phase twist. -/
public theorem psiMap_holomorphic (lambda : ParameterLattice) :
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (C.psiMap lambda) := by
  have h := (C.twist_holomorphic lambda).comp (M.fanShear_holomorphic lambda)
  change ContMDiff (modelWithCornersSelf ℂ ComplexModel)
    (modelWithCornersSelf ℂ ComplexModel) ∞
    (fun p : M.Carrier ↦ ToricModel.phaseAction M (C.phase lambda (M.t p))
      (Additive.toMul (M.fanShear lambda) p))
  simpa only [Function.comp_def, M.fanShear_preserves_t] using h

/-- Every phase-corrected map is continuous. -/
public theorem psiMap_continuous (lambda : ParameterLattice) :
    Continuous (C.psiMap lambda) :=
  (C.psiMap_holomorphic lambda).continuous

/-- The remaining compact-overlap estimate used to prove proper discontinuity. -/
public def CompactOverlapEstimate : Prop :=
  ∀ K L : Set M.Carrier, IsCompact K → IsCompact L →
    {lambda : ParameterLattice |
      (C.psiMap lambda '' K ∩ L).Nonempty}.Finite

/-- A proved compact-overlap estimate supplies the generic proper-discontinuity conclusion. -/
public theorem properlyDiscontinuous (F : C.FixedPointEstimates)
    (H : C.CompactOverlapEstimate) :
    letI := (C.toCuspActionData F).psiAction
    ProperlyDiscontinuousSMul (Multiplicative ParameterLattice) M.Carrier := by
  apply (C.toCuspActionData F).properlyDiscontinuous
  intro K L hK hL
  change {lambda : ParameterLattice |
    (C.psiMap lambda '' K ∩ L).Nonempty}.Finite
  exact H K L hK hL

end ExactHolomorphicPhaseCoefficients

end SphereSixComplex.Geometry.CuspToricPhaseAction
