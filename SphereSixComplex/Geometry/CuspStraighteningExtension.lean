module

public import SphereSixComplex.Geometry.CuspStraighteningAlgebra
import Mathlib.Topology.ContinuousMap.Units

/-!
# Point-level cusp straightening

This file reconstructs the point-level map of Lemma 7.5 on the punctured toric carrier from the
straightened logarithmic position.  The formula is the paper's complex torus multiplier
`exp (-2 π i (C(t) - C(0)) B_t⁻¹ y)`.  No extension across the central fibre is asserted here.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.Geometry.CuspStraighteningExtension

open SphereSixComplex.Periods
open CuspFilling CuspFillingRadialCompactness CuspLocalPhaseAction
open CuspPeriodExpansion CuspPuncturedCollarBridge CuspStraighteningAlgebra
open CuspToricPhaseAction
open StandardInfiniteA2ToricModel StandardInfiniteA2ToricQuantitativeRegions
open CuspPhaseEstimates.CuspPeriodExpansion
open CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate

/-- The vector `B_t⁻¹ y` in the paper's straightening formula. -/
public noncomputable def straighteningRealParameter
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) : Fin 2 → ℝ :=
  realFanShearInverse
    (puncturedActualInverseDisplacement W p (rescaledPosition M p.1))

/-- The complex exponent `-2πi(C(t)-C(0))B_t⁻¹y`. -/
public noncomputable def straighteningExponent
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) : Fin 2 → ℂ :=
  fun i ↦ -2 * Real.pi * Complex.I *
    ((N.correctionMatrix (M.t p.1) - N.correctionMatrix 0).mulVec
      (fun j ↦ straighteningRealParameter W p j)) i

/-- The paper's point-level torus multiplier. -/
public noncomputable def straighteningPhase
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) : Phase :=
  fun i ↦ CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exponentialUnit
    (straighteningExponent W p i)

/-- The point-level straightening on the punctured local toric carrier. -/
public noncomputable def puncturedPointStraightening
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) :
    PuncturedLocalCarrier W :=
  ⟨⟨M.torusEmbedding
      (phaseEmbedding (straighteningPhase W p) * torusCoordinates M p.1), by
        change M.t (M.torusEmbedding
          (phaseEmbedding (straighteningPhase W p) * torusCoordinates M p.1)) ∈
            Metric.ball 0 W.localWitness.radius
        rw [M.t_torus, Pi.mul_apply, phaseEmbedding_apply_two,
          one_mul, torusCoordinates_last M p.2]
        exact p.1.property⟩, by
      change M.t (M.torusEmbedding
        (phaseEmbedding (straighteningPhase W p) * torusCoordinates M p.1)) ≠ 0
      rw [M.t_torus, Pi.mul_apply, phaseEmbedding_apply_two,
        one_mul, torusCoordinates_last M p.2]
      exact p.2⟩

/-- The reconstructed point has exactly the paper's multiplier in dense-torus coordinates. -/
public theorem torusCoordinates_puncturedPointStraightening
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) :
    torusCoordinates M (puncturedPointStraightening W p).1 =
      phaseEmbedding (straighteningPhase W p) * torusCoordinates M p.1 := by
  apply torusCoordinates_unique M (puncturedPointStraightening W p).2
  rfl

/-- The real parameter in the complex multiplier varies continuously off the central fibre. -/
public theorem continuous_straighteningRealParameter
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (straighteningRealParameter W) := by
  have hinverse : Continuous (fun p : PuncturedLocalCarrier W ↦
      puncturedActualInverseDisplacement W p (rescaledPosition M p.1)) :=
    (continuous_actualDisplacementMatrix_inv W).matrix_mulVec
      (continuous_puncturedRescaledPosition W)
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : PuncturedLocalCarrier W ↦
      -puncturedActualInverseDisplacement W p (rescaledPosition M p.1) 1)
    exact ((continuous_apply 1).comp hinverse).neg
  · change Continuous (fun p : PuncturedLocalCarrier W ↦
      puncturedActualInverseDisplacement W p (rescaledPosition M p.1) 0)
    exact (continuous_apply 0).comp hinverse

/-- The complex straightening exponent varies continuously off the central fibre. -/
public theorem continuous_straighteningExponent
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (straighteningExponent W) := by
  have ht : Continuous (fun p : PuncturedLocalCarrier W ↦ M.t p.1) :=
    M.t_holomorphic.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hcorrection (i j : Fin 2) : Continuous
      (fun p : PuncturedLocalCarrier W ↦ N.correctionMatrix (M.t p.1) i j) :=
    (N.correctionMatrix_entry_holomorphic i j).continuousOn.comp_continuous ht fun p ↦
      mem_ball_zero_iff.mpr
        ((mem_ball_zero_iff.mp p.1.property).trans_le W.localWitness.radius_le)
  apply continuous_pi
  intro i
  change Continuous (fun p : PuncturedLocalCarrier W ↦ -2 * Real.pi * Complex.I *
    ((N.correctionMatrix (M.t p.1) - N.correctionMatrix 0).mulVec
      (fun j ↦ straighteningRealParameter W p j)) i)
  apply continuous_const.mul
  have hmul : Continuous (fun p : PuncturedLocalCarrier W ↦
      (N.correctionMatrix (M.t p.1) - N.correctionMatrix 0).mulVec
        (fun j ↦ straighteningRealParameter W p j)) := by
    apply Continuous.matrix_mulVec
    · apply continuous_matrix
      intro j k
      exact (hcorrection j k).sub continuous_const
    · apply continuous_pi
      intro j
      exact Complex.continuous_ofReal.comp
        ((continuous_apply j).comp (continuous_straighteningRealParameter W))
  exact (continuous_apply i).comp hmul

/-- The multiplier is continuous as a map into the two-dimensional phase torus. -/
public theorem continuous_straighteningPhase
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (straighteningPhase W) := by
  apply continuous_pi
  intro i
  change Continuous (fun p : PuncturedLocalCarrier W ↦
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exponentialUnit
      (straighteningExponent W p i))
  let f : C(PuncturedLocalCarrier W, ℂ) :=
    ⟨fun p ↦ Complex.exp (straighteningExponent W p i),
      Complex.continuous_exp.comp
        ((continuous_apply i).comp (continuous_straighteningExponent W))⟩
  have hunit : ∀ p, IsUnit (f p) := fun p ↦
    isUnit_iff_ne_zero.mpr (Complex.exp_ne_zero _)
  apply (ContinuousMap.continuous_isUnit_unit hunit).congr
  intro p
  apply Units.ext
  change ↑(hunit p).unit = Complex.exp (straighteningExponent W p i)
  exact (hunit p).unit_spec

/-- The point-level straightening is continuous away from the central fibre. -/
public theorem continuous_puncturedPointStraightening
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (puncturedPointStraightening W) := by
  let _ := denseTorusCharts
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have hphase : Continuous (fun p : PuncturedLocalCarrier W ↦
      phaseEmbedding (straighteningPhase W p)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun p : PuncturedLocalCarrier W ↦ straighteningPhase W p 0)
      exact (continuous_apply 0).comp (continuous_straighteningPhase W)
    · change Continuous (fun p : PuncturedLocalCarrier W ↦ straighteningPhase W p 1)
      exact (continuous_apply 1).comp (continuous_straighteningPhase W)
    · change Continuous (fun _ : PuncturedLocalCarrier W ↦ (1 : ℂˣ))
      exact continuous_const
  exact M.torusEmbedding_holomorphic.continuous.comp
    (hphase.mul (puncturedTorusCoordinates W).continuous)

/-- Under an actual deck transformation, `B_t⁻¹y` translates by the lattice parameter. -/
public theorem straighteningRealParameter_psiMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (lambda : ParameterLattice)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p ≠ 0) :
    let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_le
    straighteningRealParameter W
        ⟨C.psiMap lambda p, C.psiMap_preserves_t lambda p ▸ hp⟩ =
      straighteningRealParameter W ⟨p, hp⟩ + realParameter lambda := by
  let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_le
  let d : Fin 2 → ℝ := fun i ↦ (shearVector lambda i : ℝ)
  let p' : PuncturedLocalCarrier W :=
    ⟨C.psiMap lambda p, C.psiMap_preserves_t lambda p ▸ hp⟩
  let A := actualDisplacementEquiv W p hp
  let A' := actualDisplacementEquiv W p'.1 p'.2
  have hA : A' = A := by
    apply LinearEquiv.ext
    intro x
    rw [actualDisplacementEquiv_apply, actualDisplacementEquiv_apply,
      C.psiMap_preserves_t]
  have hdisp : rescaledPosition M p'.1 =
      rescaledPosition M p + effectiveFanDisplacement N (M.t p) d := by
    have hsub :=
      CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.rescaledPosition_psiMap_sub
        N M W.localWitness.radius_lt_one C rfl lambda p hp
    have heff := effectiveFanDisplacement_shearVector N (M.t p) lambda
    dsimp only [p']
    calc
      rescaledPosition M (C.psiMap lambda p) =
          (rescaledPosition M (C.psiMap lambda p) - rescaledPosition M p) +
            rescaledPosition M p := by abel
      _ = effectiveFanDisplacement N (M.t p) d + rescaledPosition M p := by
        rw [hsub, heff]
      _ = rescaledPosition M p + effectiveFanDisplacement N (M.t p) d := add_comm _ _
  dsimp only
  change straighteningRealParameter W p' =
    straighteningRealParameter W ⟨p, hp⟩ + realParameter lambda
  rw [straighteningRealParameter, straighteningRealParameter]
  rw [← actualDisplacementEquiv_symm_apply, ← actualDisplacementEquiv_symm_apply]
  change realFanShearInverse (A'.symm (rescaledPosition M p'.1)) =
    realFanShearInverse (A.symm (rescaledPosition M p)) + realParameter lambda
  rw [hA, hdisp, map_add]
  have hd : A.symm (effectiveFanDisplacement N (M.t p) d) = d := by
    change A.symm (A d) = d
    exact A.symm_apply_apply d
  rw [hd, realFanShearInverse_add, realFanShearInverse_shearVector]

/-- The variable complex multiplier converts the actual phase coefficient to its value frozen at
the central parameter. -/
public theorem straighteningPhase_mul_phaseCoefficient
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (lambda : ParameterLattice)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p ≠ 0) :
    let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_le
    straighteningPhase W
        ⟨C.psiMap lambda p, C.psiMap_preserves_t lambda p ▸ hp⟩ *
        N.phaseCoefficient lambda (M.t p) =
      N.phaseCoefficient lambda 0 * straighteningPhase W ⟨p, hp⟩ := by
  let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_le
  let p' : PuncturedLocalCarrier W :=
    ⟨C.psiMap lambda p, C.psiMap_preserves_t lambda p ▸ hp⟩
  have hparameter := straighteningRealParameter_psiMap W lambda p hp
  change straighteningRealParameter W p' = _ at hparameter
  funext i
  apply Units.ext
  simp only [Pi.mul_apply, straighteningPhase,
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exponentialUnit,
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseCoefficient, Units.val_mul,
    Units.val_mk0, ← Complex.exp_add]
  congr 1
  rw [straighteningExponent, straighteningExponent, hparameter]
  simp only [Pi.add_apply, Complex.ofReal_add,
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.realParameter]
  rw [C.psiMap_preserves_t]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply]
  have hcast (j : Fin 2) : (((lambda j : ℝ) : ℂ)) = (lambda j : ℂ) := by norm_num
  rw [hcast 0, hcast 1]
  ring

/-- The point-level straightening conjugates the actual deck map to the deck map with complex
twist frozen at the central parameter. -/
public theorem puncturedPointStraightening_psiMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (lambda : ParameterLattice)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p ≠ 0) :
    let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_le
    ((puncturedPointStraightening W
        ⟨C.psiMap lambda p, C.psiMap_preserves_t lambda p ▸ hp⟩).1 : M.Carrier) =
      ToricModel.phaseAction M (N.phaseCoefficient lambda 0)
        (Additive.toMul (M.fanShear lambda)
          ((puncturedPointStraightening W ⟨p, hp⟩).1 : M.Carrier)) := by
  let C := restrictedActualLocalPhaseCoefficients N M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_le
  let p' : PuncturedLocalCarrier W :=
    ⟨C.psiMap lambda p, C.psiMap_preserves_t lambda p ▸ hp⟩
  have hphase := straighteningPhase_mul_phaseCoefficient W lambda p hp
  change straighteningPhase W p' * N.phaseCoefficient lambda (M.t p) = _ at hphase
  change M.torusEmbedding
      (phaseEmbedding (straighteningPhase W p') * torusCoordinates M p'.1) =
    ToricModel.phaseAction M (N.phaseCoefficient lambda 0)
      (Additive.toMul (M.fanShear lambda)
        (M.torusEmbedding
          (phaseEmbedding (straighteningPhase W ⟨p, hp⟩) * torusCoordinates M p)))
  rw [CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.torusCoordinates_psiMap
      N M C rfl lambda p hp,
    ToricModel.phaseAction_apply, M.fanShear_torus, M.torusAction_torus,
    denseTorusShear_phase_commute]
  congr 1
  calc
    phaseEmbedding (straighteningPhase W p') *
        (phaseEmbedding (N.phaseCoefficient lambda (M.t p)) *
          denseTorusShear lambda (torusCoordinates M p)) =
      phaseEmbedding
          (straighteningPhase W p' * N.phaseCoefficient lambda (M.t p)) *
            denseTorusShear lambda (torusCoordinates M p) := by
        simp only [map_mul, mul_assoc]
    _ = phaseEmbedding
          (N.phaseCoefficient lambda 0 * straighteningPhase W ⟨p, hp⟩) *
            denseTorusShear lambda (torusCoordinates M p) := by rw [hphase]
    _ = phaseEmbedding (N.phaseCoefficient lambda 0) *
        (phaseEmbedding (straighteningPhase W ⟨p, hp⟩) *
          denseTorusShear lambda (torusCoordinates M p)) := by
        simp only [map_mul, mul_assoc]

/-- The inverse displacement has operator norm at most two in the coordinate `ℓ¹` norm. -/
public theorem realL1_puncturedActualInverseDisplacement_le
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W)
    (y : Fin 2 → ℝ) :
    realL1 (puncturedActualInverseDisplacement W p y) ≤ 2 * realL1 y := by
  let d := puncturedActualInverseDisplacement W p y
  have hright : effectiveFanDisplacement N (M.t p.1) d = y :=
    effectiveFanDisplacement_puncturedActualInverseDisplacement W p y
  have hcorrection := actual_effectiveFanDisplacement_correction_l1_le W p.1 p.2 d
  have htriangle : realL1 d ≤
      realL1 y + realL1 (effectiveFanDisplacement N (M.t p.1) d - d) := by
    have h0 := abs_sub (y 0) ((effectiveFanDisplacement N (M.t p.1) d - d) 0)
    have h1 := abs_sub (y 1) ((effectiveFanDisplacement N (M.t p.1) d - d) 1)
    rw [← hright]
    simp only [realL1, Pi.sub_apply, add_sub_sub_cancel]
    linarith
  dsimp only [d] at htriangle hcorrection ⊢
  nlinarith [realL1_nonneg y]

/-- On every standard shrunken affine chart, the parameter `B_t⁻¹y` is uniformly bounded. -/
public theorem straighteningRealParameter_bounded_on_region
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    let R := standardBoundedPolydiscRegions M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_lt_one
    ∀ a, ∃ B : ℝ, ∀ p : PuncturedLocalCarrier W,
      p.1 ∈ R.region a → realL1 (straighteningRealParameter W p) ≤ B := by
  let R := standardBoundedPolydiscRegions M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_lt_one
  intro a
  obtain ⟨B, hB⟩ := R.position_bounded a
  refine ⟨2 * B, fun p hp ↦ ?_⟩
  rw [straighteningRealParameter, realL1_realFanShearInverse]
  exact (realL1_puncturedActualInverseDisplacement_le W p _).trans
    (mul_le_mul_of_nonneg_left (hB p.1 hp p.2) (by norm_num))

end SphereSixComplex.Geometry.CuspStraighteningExtension
