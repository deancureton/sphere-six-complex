module

public import SphereSixComplex.Paper.Geometry.StandardInfiniteA2ToricModel

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
open SphereSixComplex.Geometry.InfiniteA2Toric

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


end SphereSixComplex.Geometry.CuspToricPhaseAction
