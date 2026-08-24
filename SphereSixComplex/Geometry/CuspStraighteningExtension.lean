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
open scoped Topology

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
    let c := effectiveFanDisplacement N (M.t p.1) d - d
    have hd0 : d 0 = y 0 - c 0 := by
      dsimp only [c]
      rw [← hright]
      simp
    have hd1 : d 1 = y 1 - c 1 := by
      dsimp only [c]
      rw [← hright]
      simp
    rw [realL1, realL1, realL1, hd0, hd1]
    linarith [abs_sub (y 0) (c 0), abs_sub (y 1) (c 1)]
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
  dsimp only
  let R := standardBoundedPolydiscRegions M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_lt_one
  intro a
  obtain ⟨B, hB⟩ := R.position_bounded a
  refine ⟨2 * B, fun p hp ↦ ?_⟩
  rw [straighteningRealParameter, realL1_realFanShearInverse]
  exact (realL1_puncturedActualInverseDisplacement_le W p _).trans
    (mul_le_mul_of_nonneg_left (hB p.1 hp p.2) (by norm_num))

/-- The straightening exponent extended by zero on the central fibre. -/
public noncomputable def extendedStraighteningExponent
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) : Fin 2 → ℂ :=
  if hp : M.t p = 0 then 0 else straighteningExponent W ⟨p, hp⟩

/-- The complex multiplier extended by the identity on the central fibre. -/
public noncomputable def extendedStraighteningPhase
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) : Phase :=
  fun i ↦ CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exponentialUnit
    (extendedStraighteningExponent W p i)

@[simp]
public theorem extendedStraighteningPhase_of_t_eq_zero
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p = 0) :
    extendedStraighteningPhase W p = 1 := by
  ext i
  simp [extendedStraighteningPhase, extendedStraighteningExponent, hp,
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exponentialUnit]

@[simp]
public theorem extendedStraighteningPhase_of_t_ne_zero
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p ≠ 0) :
    extendedStraighteningPhase W p = straighteningPhase W ⟨p, hp⟩ := by
  ext i
  simp [extendedStraighteningPhase, extendedStraighteningExponent, hp, straighteningPhase]

/-- On a shrunken standard chart, the extended exponent tends to zero at every central point. -/
public theorem continuousAt_extendedStraighteningExponent_of_mem_region
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a : CuspPhaseEstimates.ToricRegionIndex)
    (p₀ : LocalCarrier M W.localWitness.radius)
    (hp₀ : M.t p₀ = 0)
    (hregion : p₀ ∈ (standardBoundedPolydiscRegions M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_lt_one).region a) :
    ContinuousAt (extendedStraighteningExponent W) p₀ := by
  let R := standardBoundedPolydiscRegions M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_lt_one
  obtain ⟨B, hB⟩ := straighteningRealParameter_bounded_on_region W a
  have heventually : ∀ᶠ p : LocalCarrier M W.localWitness.radius in 𝓝 p₀,
      p ∈ R.region a := (R.region a).isOpen.mem_nhds hregion
  have ht : Continuous (fun p : LocalCarrier M W.localWitness.radius ↦ M.t p) :=
    M.t_holomorphic.continuous.comp continuous_subtype_val
  have hcorrection (i j : Fin 2) : Continuous
      (fun p : LocalCarrier M W.localWitness.radius ↦
        N.correctionMatrix (M.t p) i j) :=
    (N.correctionMatrix_entry_holomorphic i j).continuousOn.comp_continuous ht fun p ↦
      mem_ball_zero_iff.mpr
        ((mem_ball_zero_iff.mp p.property).trans_le W.localWitness.radius_le)
  let v (j : Fin 2) (p : LocalCarrier M W.localWitness.radius) : ℂ :=
    if hp : M.t p = 0 then 0 else straighteningRealParameter W ⟨p, hp⟩ j
  have hv_bounded (j : Fin 2) : Filter.IsBoundedUnder (· ≤ ·) (𝓝 p₀) (norm ∘ v j) := by
    apply Filter.isBoundedUnder_of_eventually_le (a := |B|)
    filter_upwards [heventually] with p hpregion
    dsimp only [Function.comp_apply, v]
    split_ifs with hp
    · simp
    · rw [Complex.norm_real, Real.norm_eq_abs]
      have hcoord : |straighteningRealParameter W ⟨p, hp⟩ j| ≤
          realL1 (straighteningRealParameter W ⟨p, hp⟩) := by
        fin_cases j <;> simp [realL1]
      exact hcoord.trans ((hB ⟨p, hp⟩ hpregion).trans (le_abs_self B))
  have hdelta (i j : Fin 2) : Filter.Tendsto
      (fun p : LocalCarrier M W.localWitness.radius ↦
        N.correctionMatrix (M.t p) i j - N.correctionMatrix 0 i j)
      (𝓝 p₀) (𝓝 0) := by
    have h : ContinuousAt (fun p : LocalCarrier M W.localWitness.radius ↦
        N.correctionMatrix (M.t p) i j - N.correctionMatrix 0 i j) p₀ :=
      (hcorrection i j).continuousAt.sub continuousAt_const
    change Filter.Tendsto _ (𝓝 p₀) (𝓝 ((fun p : LocalCarrier M W.localWitness.radius ↦
      N.correctionMatrix (M.t p) i j - N.correctionMatrix 0 i j) p₀)) at h
    simpa only [hp₀, sub_self] using h
  apply continuousAt_pi.mpr
  intro i
  have h0 := (hdelta i 0).zero_mul_isBoundedUnder_le (hv_bounded 0)
  have h1 := (hdelta i 1).zero_mul_isBoundedUnder_le (hv_bounded 1)
  have hsum : Filter.Tendsto (fun p : LocalCarrier M W.localWitness.radius ↦
      (N.correctionMatrix (M.t p) i 0 - N.correctionMatrix 0 i 0) * v 0 p +
      (N.correctionMatrix (M.t p) i 1 - N.correctionMatrix 0 i 1) * v 1 p)
      (𝓝 p₀) (𝓝 0) := by simpa using h0.add h1
  have hmul := Filter.Tendsto.const_mul (-2 * Real.pi * Complex.I) hsum
  have hmul0 : Filter.Tendsto (fun p : LocalCarrier M W.localWitness.radius ↦
      (-2 * Real.pi * Complex.I) *
        ((N.correctionMatrix (M.t p) i 0 - N.correctionMatrix 0 i 0) * v 0 p +
        (N.correctionMatrix (M.t p) i 1 - N.correctionMatrix 0 i 1) * v 1 p))
      (𝓝 p₀) (𝓝 0) := by simpa using hmul
  have hvalue : extendedStraighteningExponent W p₀ i = 0 := by
    simp [extendedStraighteningExponent, hp₀]
  rw [show ContinuousAt (fun p ↦ extendedStraighteningExponent W p i) p₀ =
      Filter.Tendsto (fun p ↦ extendedStraighteningExponent W p i)
        (𝓝 p₀) (𝓝 (extendedStraighteningExponent W p₀ i)) from rfl, hvalue]
  apply hmul0.congr'
  filter_upwards with p
  by_cases hp : M.t p = 0
  · simp [extendedStraighteningExponent, hp, v]
  · simp only [extendedStraighteningExponent, hp, ↓reduceDIte, straighteningExponent,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply, v]

/-- The exponential-unit construction preserves continuity at a point. -/
private theorem continuousAt_exponentialUnit {X : Type*} [TopologicalSpace X]
    (f : X → ℂ) (x : X) (hf : ContinuousAt f x) :
    ContinuousAt
      (fun y ↦ CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exponentialUnit (f y)) x := by
  rw [Units.isEmbedding_val₀.isInducing.continuousAt_iff]
  exact Complex.continuous_exp.continuousAt.comp hf

/-- On a shrunken chart, the extended multiplier tends to the identity at every central point. -/
public theorem continuousAt_extendedStraighteningPhase_of_mem_region
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a : CuspPhaseEstimates.ToricRegionIndex)
    (p₀ : LocalCarrier M W.localWitness.radius)
    (hp₀ : M.t p₀ = 0)
    (hregion : p₀ ∈ (standardBoundedPolydiscRegions M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_lt_one).region a) :
    ContinuousAt (extendedStraighteningPhase W) p₀ := by
  apply continuousAt_pi.mpr
  intro i
  exact continuousAt_exponentialUnit
    (fun p ↦ extendedStraighteningExponent W p i) p₀
    ((continuous_apply i).continuousAt.comp
      (continuousAt_extendedStraighteningExponent_of_mem_region W a p₀ hp₀ hregion))

/-- A local lift to the punctured carrier, used only near a fixed noncentral point. -/
private noncomputable def puncturedLiftAt
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p₀ : LocalCarrier M W.localWitness.radius) (hp₀ : M.t p₀ ≠ 0)
    (p : LocalCarrier M W.localWitness.radius) : PuncturedLocalCarrier W :=
  if hp : M.t p ≠ 0 then ⟨p, hp⟩ else ⟨p₀, hp₀⟩

private theorem continuousAt_puncturedLiftAt
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p₀ : LocalCarrier M W.localWitness.radius) (hp₀ : M.t p₀ ≠ 0) :
    ContinuousAt (puncturedLiftAt W p₀ hp₀) p₀ := by
  rw [show ContinuousAt (puncturedLiftAt W p₀ hp₀) p₀ =
      Filter.Tendsto (puncturedLiftAt W p₀ hp₀) (𝓝 p₀)
        (𝓝 (puncturedLiftAt W p₀ hp₀ p₀)) from rfl,
    tendsto_subtype_rng]
  have ht : Continuous (fun p : LocalCarrier M W.localWitness.radius ↦ M.t p) :=
    M.t_holomorphic.continuous.comp continuous_subtype_val
  have heventually : ∀ᶠ p : LocalCarrier M W.localWitness.radius in 𝓝 p₀, M.t p ≠ 0 :=
    (isOpen_compl_singleton.preimage ht).mem_nhds hp₀
  apply continuousAt_id.congr
  filter_upwards [heventually] with p hp
  simp [puncturedLiftAt, hp]

/-- Away from the central fibre, the extended multiplier agrees locally with the punctured one. -/
public theorem continuousAt_extendedStraighteningPhase_of_t_ne_zero
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p₀ : LocalCarrier M W.localWitness.radius) (hp₀ : M.t p₀ ≠ 0) :
    ContinuousAt (extendedStraighteningPhase W) p₀ := by
  have hpunctured : ContinuousAt
      (fun p ↦ straighteningPhase W (puncturedLiftAt W p₀ hp₀ p)) p₀ :=
    (continuous_straighteningPhase W).continuousAt.comp
      (continuousAt_puncturedLiftAt W p₀ hp₀)
  have ht : Continuous (fun p : LocalCarrier M W.localWitness.radius ↦ M.t p) :=
    M.t_holomorphic.continuous.comp continuous_subtype_val
  have heventually : ∀ᶠ p : LocalCarrier M W.localWitness.radius in 𝓝 p₀, M.t p ≠ 0 :=
    (isOpen_compl_singleton.preimage ht).mem_nhds hp₀
  apply hpunctured.congr
  filter_upwards [heventually] with p hp
  have hlift : puncturedLiftAt W p₀ hp₀ p = ⟨p, hp⟩ := by
    apply Subtype.ext
    simp [puncturedLiftAt, hp]
  rw [hlift, extendedStraighteningPhase_of_t_ne_zero W p hp]

/-- The paper's multiplier, extended by the identity at `t = 0`, is continuous everywhere. -/
public theorem continuous_extendedStraighteningPhase
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (extendedStraighteningPhase W) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : M.t p = 0
  · let R := standardBoundedPolydiscRegions M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_lt_one
    obtain ⟨a, ha⟩ := R.cover p
    exact continuousAt_extendedStraighteningPhase_of_mem_region W a p hp ha
  · exact continuousAt_extendedStraighteningPhase_of_t_ne_zero W p hp

/-- The standard topological interface for the algebraic torus action.  This is deliberately
separate from the paper-specific cusp data: the straightening argument needs joint continuity,
not only continuity for each fixed torus element. -/
public structure ContinuousTorusAction (M : Model) : Prop where
  joint_continuous : Continuous
    (fun z : DenseTorus × M.Carrier ↦ M.torusAction z.1 z.2)

namespace ContinuousTorusAction

variable {M : Model}

/-- A continuously varying torus element acts continuously on a continuously varying point. -/
public theorem variable_action (J : ContinuousTorusAction M) {X : Type*} [TopologicalSpace X]
    {g : X → DenseTorus} {p : X → M.Carrier}
    (hg : Continuous g) (hp : Continuous p) :
    Continuous (fun x ↦ M.torusAction (g x) (p x)) :=
  J.joint_continuous.comp (hg.prodMk hp)

end ContinuousTorusAction

/-- The point-level straightening on the entire local toric carrier.  At `t = 0` its multiplier
is one, so this definition is literally the identity on the central fibre. -/
public noncomputable def pointStraightening
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) :
    LocalCarrier M W.localWitness.radius :=
  ⟨M.torusAction (phaseEmbedding (extendedStraighteningPhase W p)) p, by
    change M.t (M.torusAction (phaseEmbedding (extendedStraighteningPhase W p)) p) ∈
      Metric.ball 0 W.localWitness.radius
    have ht : M.t (M.torusAction (phaseEmbedding (extendedStraighteningPhase W p)) p) =
        M.t p := by
      rw [M.t_torusAction, phaseEmbedding_apply_two]
      norm_num
    exact ht.symm ▸ p.property⟩

@[simp]
public theorem pointStraightening_of_t_eq_zero
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p = 0) :
    pointStraightening W p = p := by
  apply Subtype.ext
  simp [pointStraightening, extendedStraighteningPhase_of_t_eq_zero W p hp]

/-- Off the central fibre, the whole-carrier definition agrees with the dense-torus formula. -/
public theorem pointStraightening_of_t_ne_zero
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p ≠ 0) :
    pointStraightening W p = (puncturedPointStraightening W ⟨p, hp⟩).1 := by
  apply Subtype.ext
  change M.torusAction (phaseEmbedding (extendedStraighteningPhase W p)) p =
    M.torusEmbedding
      (phaseEmbedding (straighteningPhase W ⟨p, hp⟩) * torusCoordinates M p)
  rw [extendedStraighteningPhase_of_t_ne_zero W p hp]
  calc
    M.torusAction (phaseEmbedding (straighteningPhase W ⟨p, hp⟩)) p =
        M.torusAction (phaseEmbedding (straighteningPhase W ⟨p, hp⟩))
          (M.torusEmbedding (torusCoordinates M p)) := by
            rw [torusEmbedding_torusCoordinates M hp]
    _ = _ := M.torusAction_torus _ _

/-- The phase embedding of the extended multiplier is continuous. -/
public theorem continuous_extendedStraighteningDenseTorusPhase
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (fun p ↦ phaseEmbedding (extendedStraighteningPhase W p)) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p ↦ extendedStraighteningPhase W p 0)
    exact (continuous_apply (0 : Fin 2)).comp (continuous_extendedStraighteningPhase W)
  · change Continuous (fun p ↦ extendedStraighteningPhase W p 1)
    exact (continuous_apply (1 : Fin 2)).comp (continuous_extendedStraighteningPhase W)
  · exact continuous_const

/-- Joint continuity of the standard torus action turns the chartwise multiplier limit into
continuity of the identity extension on the whole cusp carrier. -/
public theorem continuous_pointStraightening
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (J : ContinuousTorusAction M)
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (pointStraightening W) := by
  change Continuous (fun p : LocalCarrier M W.localWitness.radius ↦
    (⟨M.torusAction (phaseEmbedding (extendedStraighteningPhase W p)) p, _⟩ :
      LocalCarrier M W.localWitness.radius))
  exact (J.variable_action (continuous_extendedStraighteningDenseTorusPhase W)
    continuous_subtype_val).subtype_mk _

end SphereSixComplex.Geometry.CuspStraighteningExtension
