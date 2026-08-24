module

public import SphereSixComplex.Geometry.CuspStraighteningExtension
import Mathlib.Topology.ContinuousMap.Units

/-!
# Inverse of the cusp straightening

This file develops the inverse formula from Lemma 7.5.  Its first step is purely quantitative:
the same small-cusp estimate that makes the actual displacement invertible also makes the
displacement with correction matrix frozen at zero invertible.
-/

@[expose] public section

noncomputable section

open Matrix
open scoped Topology

namespace SphereSixComplex.Geometry.CuspStraighteningHomeomorph

open SphereSixComplex.Periods
open CuspFilling CuspFillingRadialCompactness CuspLocalPhaseAction
open CuspPeriodExpansion CuspPuncturedCollarBridge
open CuspStraighteningAlgebra CuspStraighteningExtension
open CuspToricPhaseAction
open StandardInfiniteA2ToricModel StandardInfiniteA2ToricQuantitativeRegions
open CuspPhaseEstimates.CuspPeriodExpansion
open CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate

/-- The zero fibre contains the origin of every standard affine toric chart. -/
private theorem exists_centralLocalCarrier (M : Model) {r : ℝ} (hr : 0 < r) :
    ∃ p : LocalCarrier M r, M.t p = 0 := by
  let e := M.toricChart false 0
  let z : e.target := ⟨0, by
    change (0 : ComplexModel) ∈ (M.toricChart false 0).target
    rw [M.toricChart_target]
    trivial⟩
  let q : e.source := e.toOpenPartialHomeomorph.toHomeomorphSourceTarget.symm z
  have hchart : M.toricChart false 0 q = 0 := by
    exact congrArg Subtype.val
      (e.toOpenPartialHomeomorph.toHomeomorphSourceTarget.apply_symm_apply z)
  have ht : M.t (q : M.Carrier) = 0 := by
    rw [M.toricChart_t false 0 q q.property, hchart]
    simp
  refine ⟨⟨q, ?_⟩, ht⟩
  rw [mem_cuspNeighborhood_iff, ht]
  exact Metric.mem_ball_self hr

/-- The witness's uniform phase-log bound also applies to the matrix frozen at zero. -/
public theorem frozenPhaseLogMatrix_entry_bound
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (i j : Fin 2) :
    |phaseLogMatrix N 0 i j| ≤ W.localWitness.phaseBound := by
  obtain ⟨p, hp⟩ := exists_centralLocalCarrier M W.localWitness.radius_pos
  simpa only [hp] using W.localWitness.phaseLogMatrix_entry_bound p i j

/-- The frozen correction is at most one quarter of the input in each coordinate. -/
public theorem frozenEffectiveFanDisplacement_correction_coord_le
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p ≠ 0)
    (d : Fin 2 → ℝ) (i : Fin 2) :
    |(phaseLogMatrix N 0).mulVec (realFanShearInverse d) i / Real.log ‖M.t p‖| ≤
      (1 / 4 : ℝ) * realL1 d := by
  have hnorm_pos : 0 < ‖M.t p‖ := norm_pos_iff.mpr hp
  have hnorm_lt : ‖M.t p‖ < 1 :=
    (mem_ball_zero_iff.mp p.property).trans W.localWitness.radius_lt_one
  have habslog_pos : 0 < |Real.log ‖M.t p‖| :=
    abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hnorm_pos (ne_of_lt hnorm_lt))
  have hvec := phaseLog_mulVec_real_le N
    (frozenPhaseLogMatrix_entry_bound W) (realFanShearInverse d) i
  rw [realL1_realFanShearInverse] at hvec
  rw [abs_div]
  apply (div_le_iff₀ habslog_pos).2
  have hdom := W.localWitness.phaseLog_dominates p hp
  nlinarith [realL1_nonneg d, W.localWitness.phaseBound_nonneg]

/-- The frozen displacement differs from the identity by at most one half in `ℓ¹`. -/
public theorem frozenEffectiveFanDisplacement_correction_l1_le
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p ≠ 0)
    (d : Fin 2 → ℝ) :
    realL1 (frozenEffectiveFanDisplacement N (M.t p) d - d) ≤
      (1 / 2 : ℝ) * realL1 d := by
  have h0 := frozenEffectiveFanDisplacement_correction_coord_le W p hp d 0
  have h1 := frozenEffectiveFanDisplacement_correction_coord_le W p hp d 1
  simp only [realL1, frozenEffectiveFanDisplacement, Pi.sub_apply, Pi.add_apply,
    add_sub_cancel_left]
  calc
    _ ≤ (1 / 4 : ℝ) * realL1 d + (1 / 4 : ℝ) * realL1 d := add_le_add h0 h1
    _ = (1 / 2 : ℝ) * realL1 d := by ring

/-- On the punctured collar, the frozen displacement matrix is nonsingular. -/
public theorem frozenDisplacementMatrix_det_ne_zero
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) :
    (frozenDisplacementMatrix N (M.t p.1)).det ≠ 0 := by
  have hinj : Function.Injective (frozenDisplacementMatrix N (M.t p.1)).mulVec := by
    intro x y hxy
    let d := x - y
    have hzero : frozenDisplacementMatrix N (M.t p.1) *ᵥ d = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hbound := frozenEffectiveFanDisplacement_correction_l1_le W p.1 p.2 d
    have heq : frozenEffectiveFanDisplacement N (M.t p.1) d - d = -d := by
      rw [← frozenDisplacementMatrix_mulVec, hzero, zero_sub]
    have hl1eq : realL1 (frozenEffectiveFanDisplacement N (M.t p.1) d - d) =
        realL1 d := by rw [heq, realL1_neg]
    have hd0 : realL1 d = 0 := by
      rw [hl1eq] at hbound
      nlinarith [realL1_nonneg d]
    exact sub_eq_zero.mp ((realL1_eq_zero_iff d).mp hd0)
  exact isUnit_iff_ne_zero.mp
    ((frozenDisplacementMatrix N (M.t p.1)).isUnit_iff_isUnit_det.mp
      (Matrix.mulVec_injective_iff_isUnit.mp hinj))

/-- The explicit inverse of the frozen displacement. -/
public noncomputable def puncturedFrozenInverseDisplacement
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : PuncturedLocalCarrier W) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (frozenDisplacementMatrix N (M.t p.1))⁻¹ *ᵥ x

/-- Matrix inversion gives a right inverse to the frozen displacement. -/
public theorem frozenEffectiveFanDisplacement_puncturedFrozenInverseDisplacement
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : PuncturedLocalCarrier W) (x : Fin 2 → ℝ) :
    frozenEffectiveFanDisplacement N (M.t p.1)
      (puncturedFrozenInverseDisplacement W p x) = x := by
  rw [← frozenDisplacementMatrix_mulVec]
  change frozenDisplacementMatrix N (M.t p.1) *ᵥ
    ((frozenDisplacementMatrix N (M.t p.1))⁻¹ *ᵥ x) = x
  rw [Matrix.mulVec_mulVec]
  rw [(frozenDisplacementMatrix N (M.t p.1)).mul_nonsing_inv]
  · exact Matrix.one_mulVec x
  · exact isUnit_iff_ne_zero.mpr (frozenDisplacementMatrix_det_ne_zero W p)

/-- The inverse frozen displacement has operator norm at most two in coordinate `ℓ¹`. -/
public theorem realL1_puncturedFrozenInverseDisplacement_le
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : PuncturedLocalCarrier W) (y : Fin 2 → ℝ) :
    realL1 (puncturedFrozenInverseDisplacement W p y) ≤ 2 * realL1 y := by
  let d := puncturedFrozenInverseDisplacement W p y
  have hright : frozenEffectiveFanDisplacement N (M.t p.1) d = y :=
    frozenEffectiveFanDisplacement_puncturedFrozenInverseDisplacement W p y
  have hcorrection := frozenEffectiveFanDisplacement_correction_l1_le W p.1 p.2 d
  have htriangle : realL1 d ≤
      realL1 y + realL1 (frozenEffectiveFanDisplacement N (M.t p.1) d - d) := by
    let c := frozenEffectiveFanDisplacement N (M.t p.1) d - d
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

/-- The logarithmic modulus of the straightening multiplier is the difference of the actual and
frozen phase-log matrices. -/
public theorem log_norm_straighteningPhase
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : PuncturedLocalCarrier W) (i : Fin 2) :
    Real.log ‖((straighteningPhase W p i : ℂˣ) : ℂ)‖ =
      -((phaseLogMatrix N (M.t p.1) - phaseLogMatrix N 0).mulVec
        (straighteningRealParameter W p)) i := by
  simp only [straighteningPhase,
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exponentialUnit,
    Units.val_mk0, Complex.norm_exp, Real.log_exp, straighteningExponent,
    phaseLogMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply]
  fin_cases i <;>
    simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The punctured point formula has exactly the straightened rescaled position. -/
public theorem rescaledPosition_puncturedPointStraightening
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) :
    rescaledPosition M (puncturedPointStraightening W p).1 =
      explicitPuncturedStraightenedPosition W p := by
  ext i
  have ht : M.t (puncturedPointStraightening W p).1 = M.t p.1 := by
    change M.t (M.torusEmbedding
      (phaseEmbedding (straighteningPhase W p) * torusCoordinates M p.1)) = M.t p.1
    rw [M.t_torus, Pi.mul_apply, phaseEmbedding_apply_two, one_mul,
      torusCoordinates_last M p.2]
  have hcoord := congrFun (torusCoordinates_puncturedPointStraightening W p) i.castSucc
  change Real.log ‖((torusCoordinates M (puncturedPointStraightening W p).1
      i.castSucc : ℂˣ) : ℂ)‖ / Real.log ‖M.t (puncturedPointStraightening W p).1‖ = _
  rw [hcoord, ht]
  have hphasecast : phaseEmbedding (straighteningPhase W p) i.castSucc =
      straighteningPhase W p i := by fin_cases i <;> rfl
  simp only [Pi.mul_apply, Units.val_mul, hphasecast]
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (Units.ne_zero _))
      (norm_ne_zero_iff.mpr (Units.ne_zero _)),
    log_norm_straighteningPhase W p i]
  rw [explicitPuncturedStraightenedPosition, frozenDisplacementMatrix_mulVec,
    frozenEffectiveFanDisplacement, straighteningRealParameter]
  simp only [Pi.add_apply]
  have hlog : Real.log ‖M.t p.1‖ ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.mpr p.2)
      (ne_of_lt ((mem_ball_zero_iff.mp p.1.property).trans W.localWitness.radius_lt_one))
  have hright := congrFun
    (effectiveFanDisplacement_puncturedActualInverseDisplacement W p
      (rescaledPosition M p.1)) i
  simp only [effectiveFanDisplacement, Pi.add_apply, rescaledPosition] at hright
  field_simp at hright
  field_simp
  have hsub : ((phaseLogMatrix N (M.t p.1) - phaseLogMatrix N 0).mulVec
      (realFanShearInverse
        (puncturedActualInverseDisplacement W p (rescaledPosition M p.1)))) i =
      (phaseLogMatrix N (M.t p.1)).mulVec
          (realFanShearInverse
            (puncturedActualInverseDisplacement W p (rescaledPosition M p.1))) i -
        (phaseLogMatrix N 0).mulVec
          (realFanShearInverse
            (puncturedActualInverseDisplacement W p (rescaledPosition M p.1))) i := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply]
    ring
  rw [hsub]
  linarith

/-- Matrix inversion is continuous along the nonsingular frozen displacement family. -/
public theorem continuous_frozenDisplacementMatrix_inv
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (fun p : PuncturedLocalCarrier W ↦
      (frozenDisplacementMatrix N (M.t p.1))⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hunit : IsUnit (frozenDisplacementMatrix N (M.t p.1)).det :=
    isUnit_iff_ne_zero.mpr (frozenDisplacementMatrix_det_ne_zero W p)
  have hinverse : ContinuousAt Ring.inverse
      (frozenDisplacementMatrix N (M.t p.1)).det := by
    have h := NormedRing.inverse_continuousAt hunit.unit
    simpa only [← Ring.inverse_unit, hunit.unit_spec] using h
  have hmatrix : ContinuousAt
      (fun p : PuncturedLocalCarrier W ↦ frozenDisplacementMatrix N (M.t p.1)) p :=
    (continuous_frozenDisplacementMatrix W).continuousAt
  exact (continuousAt_matrix_inv _ hinverse).tendsto.comp hmatrix.tendsto

/-- The real parameter in the inverse formula, namely `B₀,t⁻¹ y`. -/
public noncomputable def inverseStraighteningRealParameter
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) : Fin 2 → ℝ :=
  realFanShearInverse
    (puncturedFrozenInverseDisplacement W p (rescaledPosition M p.1))

/-- The exponent in the paper's inverse formula. -/
public noncomputable def inverseStraighteningExponent
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) : Fin 2 → ℂ :=
  fun i ↦ 2 * Real.pi * Complex.I *
    ((N.correctionMatrix (M.t p.1) - N.correctionMatrix 0).mulVec
      (fun j ↦ inverseStraighteningRealParameter W p j)) i

/-- The inverse point-level torus multiplier. -/
public noncomputable def inverseStraighteningPhase
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) : Phase :=
  fun i ↦ CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exponentialUnit
    (inverseStraighteningExponent W p i)

/-- The inverse formula on the punctured carrier. -/
public noncomputable def puncturedPointUnstraightening
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) :
    PuncturedLocalCarrier W :=
  ⟨⟨M.torusEmbedding
      (phaseEmbedding (inverseStraighteningPhase W p) * torusCoordinates M p.1), by
        change M.t (M.torusEmbedding
          (phaseEmbedding (inverseStraighteningPhase W p) * torusCoordinates M p.1)) ∈
            Metric.ball 0 W.localWitness.radius
        rw [M.t_torus, Pi.mul_apply, phaseEmbedding_apply_two, one_mul,
          torusCoordinates_last M p.2]
        exact p.1.property⟩, by
      change M.t (M.torusEmbedding
        (phaseEmbedding (inverseStraighteningPhase W p) * torusCoordinates M p.1)) ≠ 0
      rw [M.t_torus, Pi.mul_apply, phaseEmbedding_apply_two, one_mul,
        torusCoordinates_last M p.2]
      exact p.2⟩

/-- The inverse real parameter is continuous away from the central fibre. -/
public theorem continuous_inverseStraighteningRealParameter
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (inverseStraighteningRealParameter W) := by
  have hinverse : Continuous (fun p : PuncturedLocalCarrier W ↦
      puncturedFrozenInverseDisplacement W p (rescaledPosition M p.1)) :=
    (continuous_frozenDisplacementMatrix_inv W).matrix_mulVec
      (continuous_puncturedRescaledPosition W)
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : PuncturedLocalCarrier W ↦
      -puncturedFrozenInverseDisplacement W p (rescaledPosition M p.1) 1)
    exact ((continuous_apply 1).comp hinverse).neg
  · change Continuous (fun p : PuncturedLocalCarrier W ↦
      puncturedFrozenInverseDisplacement W p (rescaledPosition M p.1) 0)
    exact (continuous_apply 0).comp hinverse

/-- The inverse multiplier is continuous away from the central fibre. -/
public theorem continuous_inverseStraighteningPhase
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (inverseStraighteningPhase W) := by
  have ht : Continuous (fun p : PuncturedLocalCarrier W ↦ M.t p.1) :=
    M.t_holomorphic.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hcorrection (i j : Fin 2) : Continuous
      (fun p : PuncturedLocalCarrier W ↦ N.correctionMatrix (M.t p.1) i j) :=
    (N.correctionMatrix_entry_holomorphic i j).continuousOn.comp_continuous ht fun p ↦
      mem_ball_zero_iff.mpr
        ((mem_ball_zero_iff.mp p.1.property).trans_le W.localWitness.radius_le)
  have hexponent : Continuous (inverseStraighteningExponent W) := by
    apply continuous_pi
    intro i
    apply continuous_const.mul
    apply (continuous_apply i).comp
    exact (by
      apply Continuous.matrix_mulVec
      · apply continuous_matrix
        intro j k
        exact (hcorrection j k).sub continuous_const
      · apply continuous_pi
        intro j
        exact Complex.continuous_ofReal.comp
          ((continuous_apply j).comp (continuous_inverseStraighteningRealParameter W)))
  apply continuous_pi
  intro i
  let f : C(PuncturedLocalCarrier W, ℂ) :=
    ⟨fun p ↦ Complex.exp (inverseStraighteningExponent W p i),
      Complex.continuous_exp.comp ((continuous_apply i).comp hexponent)⟩
  have hunit : ∀ p, IsUnit (f p) := fun p ↦
    isUnit_iff_ne_zero.mpr (Complex.exp_ne_zero _)
  apply (ContinuousMap.continuous_isUnit_unit hunit).congr
  intro p
  apply Units.ext
  change ↑(hunit p).unit = Complex.exp (inverseStraighteningExponent W p i)
  exact (hunit p).unit_spec

/-- On every shrunken affine chart, the inverse real parameter is uniformly bounded. -/
public theorem inverseStraighteningRealParameter_bounded_on_region
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    let R := standardBoundedPolydiscRegions M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_lt_one
    ∀ a, ∃ B : ℝ, ∀ p : PuncturedLocalCarrier W,
      p.1 ∈ R.region a → realL1 (inverseStraighteningRealParameter W p) ≤ B := by
  dsimp only
  let R := standardBoundedPolydiscRegions M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_lt_one
  intro a
  obtain ⟨B, hB⟩ := R.position_bounded a
  refine ⟨2 * B, fun p hp ↦ ?_⟩
  rw [inverseStraighteningRealParameter, realL1_realFanShearInverse]
  exact (realL1_puncturedFrozenInverseDisplacement_le W p _).trans
    (mul_le_mul_of_nonneg_left (hB p.1 hp p.2) (by norm_num))

/-- The inverse exponent extended by zero on the central fibre. -/
public noncomputable def extendedInverseStraighteningExponent
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) : Fin 2 → ℂ :=
  if hp : M.t p = 0 then 0 else inverseStraighteningExponent W ⟨p, hp⟩

/-- The inverse multiplier extended by the identity on the central fibre. -/
public noncomputable def extendedInverseStraighteningPhase
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) : Phase :=
  fun i ↦ CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exponentialUnit
    (extendedInverseStraighteningExponent W p i)

@[simp]
public theorem extendedInverseStraighteningPhase_of_t_eq_zero
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p = 0) :
    extendedInverseStraighteningPhase W p = 1 := by
  ext i
  simp [extendedInverseStraighteningPhase, extendedInverseStraighteningExponent, hp,
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exponentialUnit]

@[simp]
public theorem extendedInverseStraighteningPhase_of_t_ne_zero
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) (hp : M.t p ≠ 0) :
    extendedInverseStraighteningPhase W p = inverseStraighteningPhase W ⟨p, hp⟩ := by
  ext i
  simp [extendedInverseStraighteningPhase, extendedInverseStraighteningExponent, hp,
    inverseStraighteningPhase]

/-- On a standard chart, the inverse exponent tends to zero at every central point. -/
public theorem continuousAt_extendedInverseStraighteningExponent_of_mem_region
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a : CuspPhaseEstimates.ToricRegionIndex)
    (p₀ : LocalCarrier M W.localWitness.radius) (hp₀ : M.t p₀ = 0)
    (hregion : p₀ ∈ (standardBoundedPolydiscRegions M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_lt_one).region a) :
    ContinuousAt (extendedInverseStraighteningExponent W) p₀ := by
  let R := standardBoundedPolydiscRegions M W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_lt_one
  obtain ⟨B, hB⟩ := inverseStraighteningRealParameter_bounded_on_region W a
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
    if hp : M.t p = 0 then 0 else inverseStraighteningRealParameter W ⟨p, hp⟩ j
  have hv_bounded (j : Fin 2) : Filter.IsBoundedUnder (· ≤ ·) (𝓝 p₀) (norm ∘ v j) := by
    apply Filter.isBoundedUnder_of_eventually_le (a := |B|)
    filter_upwards [heventually] with p hpregion
    dsimp only [Function.comp_apply, v]
    split_ifs with hp
    · simp
    · rw [Complex.norm_real, Real.norm_eq_abs]
      have hcoord : |inverseStraighteningRealParameter W ⟨p, hp⟩ j| ≤
          realL1 (inverseStraighteningRealParameter W ⟨p, hp⟩) := by
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
  have hmul := Filter.Tendsto.const_mul (2 * Real.pi * Complex.I) hsum
  have hmul0 : Filter.Tendsto (fun p : LocalCarrier M W.localWitness.radius ↦
      (2 * Real.pi * Complex.I) *
        ((N.correctionMatrix (M.t p) i 0 - N.correctionMatrix 0 i 0) * v 0 p +
        (N.correctionMatrix (M.t p) i 1 - N.correctionMatrix 0 i 1) * v 1 p))
      (𝓝 p₀) (𝓝 0) := by simpa using hmul
  have hvalue : extendedInverseStraighteningExponent W p₀ i = 0 := by
    simp [extendedInverseStraighteningExponent, hp₀]
  rw [show ContinuousAt (fun p ↦ extendedInverseStraighteningExponent W p i) p₀ =
      Filter.Tendsto (fun p ↦ extendedInverseStraighteningExponent W p i)
        (𝓝 p₀) (𝓝 (extendedInverseStraighteningExponent W p₀ i)) from rfl, hvalue]
  apply hmul0.congr'
  filter_upwards with p
  by_cases hp : M.t p = 0
  · simp [extendedInverseStraighteningExponent, hp, v]
  · simp only [extendedInverseStraighteningExponent, hp, ↓reduceDIte,
      inverseStraighteningExponent, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.sub_apply, v]

end SphereSixComplex.Geometry.CuspStraighteningHomeomorph
