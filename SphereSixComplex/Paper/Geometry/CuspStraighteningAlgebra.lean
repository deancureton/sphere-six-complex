module

public import SphereSixComplex.Paper.Geometry.CuspFillingRadialCompactness

/-!
# Algebra of the cusp straightening map

This file formalizes the punctured-fibre linear algebra in Lemma 7.5.  It conjugates the actual
rescaled-position displacement to the displacement obtained by freezing the correction matrix at
the central parameter.  It does not define a map on the central fibre and makes no continuity
claim there.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.Geometry.CuspStraighteningAlgebra

open SphereSixComplex.Periods
open CuspFilling CuspFillingRadialCompactness CuspLocalPhaseAction
open CuspPeriodExpansion CuspPuncturedCollarBridge
open InfiniteA2Toric InfiniteA2Toric.QuantitativeRegions
open CuspPeriodExpansion
open CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate

/-- The displacement with the correction matrix frozen at the central parameter. -/
public noncomputable def frozenEffectiveFanDisplacement
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (q : ℂ) (d : Fin 2 → ℝ) : Fin 2 → ℝ :=
  d + fun i ↦
    (NormalizedFuchsianCuspCoordinate.phaseLogMatrix N 0).mulVec (realFanShearInverse d) i / Real.log ‖q‖


/-- The actual displacement equivalence, exposed here so its underlying linear map can be used in
the straightening algebra. -/
public noncomputable def actualDisplacementEquiv
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : localCarrier M W.localWitness.radius) (hp : M.t p ≠ 0) :
    (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearEquiv.ofInjectiveEndo (effectiveFanDisplacementLinearMap N (M.t p)) (by
    intro x y hxy
    let d := x - y
    have hzero : effectiveFanDisplacementLinearMap N (M.t p) d = 0 := by
      rw [map_sub, hxy, sub_self]
    have hbound := actual_effectiveFanDisplacement_correction_l1_le W p hp d
    have heq : effectiveFanDisplacement N (M.t p) d - d = -d := by
      change effectiveFanDisplacementLinearMap N (M.t p) d - d = -d
      rw [hzero, zero_sub]
    have hl1eq : realL1 (effectiveFanDisplacement N (M.t p) d - d) = realL1 d := by
      rw [heq]
      exact realL1_neg d
    have hd0 : realL1 d = 0 := by
      rw [hl1eq] at hbound
      nlinarith [realL1_nonneg d]
    exact sub_eq_zero.mp ((realL1_eq_zero_iff d).mp hd0))

@[simp]
public theorem actualDisplacementEquiv_apply
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : localCarrier M W.localWitness.radius) (hp : M.t p ≠ 0) (d : Fin 2 → ℝ) :
    actualDisplacementEquiv W p hp d = effectiveFanDisplacement N (M.t p) d :=
  rfl



/-- The punctured part of the actual local cusp carrier. -/
public abbrev PuncturedLocalCarrier
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :=
  {p : localCarrier M W.localWitness.radius // M.t p ≠ 0}

/-- Dense-torus coordinates are continuous on the punctured local carrier. -/
public noncomputable def puncturedTorusCoordinates
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    C(PuncturedLocalCarrier W, DenseTorus) where
  toFun p := torusCoordinates M p.1
  continuous_toFun := by
    let e := M.torus_openEmbedding.isEmbedding.toHomeomorph
    let rangePoint : PuncturedLocalCarrier W → Set.range M.torusEmbedding := fun p ↦
      ⟨p.1, torusCoordinates M p.1, torusEmbedding_torusCoordinates M p.2⟩
    have hrange : Continuous rangePoint := by
      exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have hcontinuous : Continuous (fun p ↦ e.symm (rangePoint p)) :=
      e.symm.continuous.comp hrange
    apply hcontinuous.congr
    intro p
    apply M.torus_openEmbedding.injective
    rw [torusEmbedding_torusCoordinates M p.2]
    exact congrArg Subtype.val (e.apply_symm_apply (rangePoint p))

@[simp]
public theorem puncturedTorusCoordinates_apply
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) :
    puncturedTorusCoordinates W p = torusCoordinates M p.1 :=
  rfl

/-- Rescaled logarithmic position is continuous away from the central fibre. -/
public theorem continuous_puncturedRescaledPosition
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (fun p : PuncturedLocalCarrier W ↦ rescaledPosition M p.1) := by
  apply continuous_pi
  intro i
  have hcoord : Continuous (fun p : PuncturedLocalCarrier W ↦
      ((puncturedTorusCoordinates W p i.castSucc : ℂˣ) : ℂ)) := by
    fun_prop
  have hcoord' : Continuous (fun p : PuncturedLocalCarrier W ↦
      ((torusCoordinates M p.1 i.castSucc : ℂˣ) : ℂ)) := by
    simpa only [puncturedTorusCoordinates_apply] using hcoord
  have ht : Continuous (fun p : PuncturedLocalCarrier W ↦ M.t p.1) :=
    M.t_holomorphic.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hlog_ne : ∀ p : PuncturedLocalCarrier W, Real.log ‖M.t p.1‖ ≠ 0 := by
    intro p
    have hnorm_pos : 0 < ‖M.t p.1‖ := norm_pos_iff.mpr p.2
    have hnorm_lt : ‖M.t p.1‖ < 1 :=
      (mem_ball_zero_iff.mp p.1.property).trans W.localWitness.radius_lt_one
    exact Real.log_ne_zero_of_pos_of_ne_one hnorm_pos (ne_of_lt hnorm_lt)
  change Continuous (fun p : PuncturedLocalCarrier W ↦
    Real.log ‖((torusCoordinates M p.1 i.castSucc : ℂˣ) : ℂ)‖ / Real.log ‖M.t p.1‖)
  have hnum : Continuous (fun p : PuncturedLocalCarrier W ↦
      Real.log ‖((torusCoordinates M p.1 i.castSucc : ℂˣ) : ℂ)‖) := by
    exact hcoord'.norm.log fun _ ↦ norm_ne_zero_iff.mpr (Units.ne_zero _)
  have hden : Continuous (fun p : PuncturedLocalCarrier W ↦ Real.log ‖M.t p.1‖) := by
    exact ht.norm.log fun p ↦ norm_ne_zero_iff.mpr p.2
  exact hnum.div hden hlog_ne

/-- Matrix of the actual rescaled-position displacement in the standard coordinate basis. -/
public noncomputable def actualDisplacementMatrix
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (q : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + NormalizedFuchsianCuspCoordinate.phaseLogMatrix N q 0 1 / Real.log ‖q‖,
      -NormalizedFuchsianCuspCoordinate.phaseLogMatrix N q 0 0 / Real.log ‖q‖;
    NormalizedFuchsianCuspCoordinate.phaseLogMatrix N q 1 1 / Real.log ‖q‖,
      1 - NormalizedFuchsianCuspCoordinate.phaseLogMatrix N q 1 0 / Real.log ‖q‖]

@[simp]
public theorem actualDisplacementMatrix_mulVec
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (q : ℂ) (d : Fin 2 → ℝ) :
    actualDisplacementMatrix N q *ᵥ d = effectiveFanDisplacement N q d := by
  ext i
  fin_cases i <;>
    simp [actualDisplacementMatrix, effectiveFanDisplacement, realFanShearInverse,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- On the punctured collar, the actual displacement matrix is nonsingular. -/
public theorem actualDisplacementMatrix_det_ne_zero
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) :
    (actualDisplacementMatrix N (M.t p.1)).det ≠ 0 := by
  have hinj : Function.Injective (actualDisplacementMatrix N (M.t p.1)).mulVec := by
    intro x y hxy
    apply (actualDisplacementEquiv W p.1 p.2).injective
    rw [actualDisplacementEquiv_apply, actualDisplacementEquiv_apply]
    simpa only [actualDisplacementMatrix_mulVec] using hxy
  exact isUnit_iff_ne_zero.mp
    ((actualDisplacementMatrix N (M.t p.1)).isUnit_iff_isUnit_det.mp
      (Matrix.mulVec_injective_iff_isUnit.mp hinj))

/-- The correction matrix, hence the phase-log matrix, varies continuously on the local cusp
carrier. -/
public theorem continuous_puncturedPhaseLogMatrix_entry
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (i j : Fin 2) :
    Continuous (fun p : PuncturedLocalCarrier W ↦ NormalizedFuchsianCuspCoordinate.phaseLogMatrix N (M.t p.1) i j) := by
  have ht : Continuous (fun p : PuncturedLocalCarrier W ↦ M.t p.1) :=
    M.t_holomorphic.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hcorrection : Continuous
      (fun p : PuncturedLocalCarrier W ↦ N.correctionMatrix (M.t p.1) i j) :=
    (N.correctionMatrix_entry_holomorphic i j).continuousOn.comp_continuous ht fun p ↦
      mem_ball_zero_iff.mpr
        ((mem_ball_zero_iff.mp p.1.property).trans_le W.localWitness.radius_le)
  apply (continuous_const.mul (Complex.continuous_im.comp hcorrection)).congr
  intro p
  rfl

/-- The actual displacement matrices form a continuous family on the punctured collar. -/
public theorem continuous_actualDisplacementMatrix
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (fun p : PuncturedLocalCarrier W ↦ actualDisplacementMatrix N (M.t p.1)) := by
  have ht : Continuous (fun p : PuncturedLocalCarrier W ↦ M.t p.1) :=
    M.t_holomorphic.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hlog : Continuous (fun p : PuncturedLocalCarrier W ↦ Real.log ‖M.t p.1‖) :=
    ht.norm.log fun p ↦ norm_ne_zero_iff.mpr p.2
  have hlog_ne : ∀ p : PuncturedLocalCarrier W, Real.log ‖M.t p.1‖ ≠ 0 := by
    intro p
    exact Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.mpr p.2)
      (ne_of_lt ((mem_ball_zero_iff.mp p.1.property).trans W.localWitness.radius_lt_one))
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j
  · change Continuous (fun p : PuncturedLocalCarrier W ↦
      1 + NormalizedFuchsianCuspCoordinate.phaseLogMatrix N (M.t p.1) 0 1 / Real.log ‖M.t p.1‖)
    exact continuous_const.add
      ((continuous_puncturedPhaseLogMatrix_entry W 0 1).div hlog hlog_ne)
  · change Continuous (fun p : PuncturedLocalCarrier W ↦
      -NormalizedFuchsianCuspCoordinate.phaseLogMatrix N (M.t p.1) 0 0 / Real.log ‖M.t p.1‖)
    exact (continuous_puncturedPhaseLogMatrix_entry W 0 0).neg.div hlog hlog_ne
  · change Continuous (fun p : PuncturedLocalCarrier W ↦
      NormalizedFuchsianCuspCoordinate.phaseLogMatrix N (M.t p.1) 1 1 / Real.log ‖M.t p.1‖)
    exact (continuous_puncturedPhaseLogMatrix_entry W 1 1).div hlog hlog_ne
  · change Continuous (fun p : PuncturedLocalCarrier W ↦
      1 - NormalizedFuchsianCuspCoordinate.phaseLogMatrix N (M.t p.1) 1 0 / Real.log ‖M.t p.1‖)
    exact continuous_const.sub
      ((continuous_puncturedPhaseLogMatrix_entry W 1 0).div hlog hlog_ne)

/-- Matrix inversion is continuous along the nonsingular actual displacement family. -/
public theorem continuous_actualDisplacementMatrix_inv
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (fun p : PuncturedLocalCarrier W ↦
      (actualDisplacementMatrix N (M.t p.1))⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hunit : IsUnit (actualDisplacementMatrix N (M.t p.1)).det :=
    isUnit_iff_ne_zero.mpr (actualDisplacementMatrix_det_ne_zero W p)
  have hinverse : ContinuousAt Ring.inverse (actualDisplacementMatrix N (M.t p.1)).det := by
    have h := NormedRing.inverse_continuousAt hunit.unit
    simpa only [← Ring.inverse_unit, hunit.unit_spec] using h
  have hmatrix : ContinuousAt
      (fun p : PuncturedLocalCarrier W ↦ actualDisplacementMatrix N (M.t p.1)) p :=
    (continuous_actualDisplacementMatrix W).continuousAt
  have hinvMatrix : ContinuousAt
      (fun p : PuncturedLocalCarrier W ↦ (actualDisplacementMatrix N (M.t p.1))⁻¹) p :=
    (continuousAt_matrix_inv _ hinverse).tendsto.comp hmatrix.tendsto
  exact hinvMatrix

/-- The explicit inverse actual displacement, expressed by nonsingular matrix inversion. -/
public noncomputable def puncturedActualInverseDisplacement
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : PuncturedLocalCarrier W) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (actualDisplacementMatrix N (M.t p.1))⁻¹ *ᵥ x


/-- The explicit matrix inverse is a right inverse to the actual displacement. -/
public theorem effectiveFanDisplacement_puncturedActualInverseDisplacement
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : PuncturedLocalCarrier W) (x : Fin 2 → ℝ) :
    effectiveFanDisplacement N (M.t p.1) (puncturedActualInverseDisplacement W p x) = x := by
  rw [← actualDisplacementMatrix_mulVec]
  change actualDisplacementMatrix N (M.t p.1) *ᵥ
    ((actualDisplacementMatrix N (M.t p.1))⁻¹ *ᵥ x) = x
  rw [Matrix.mulVec_mulVec]
  rw [(actualDisplacementMatrix N (M.t p.1)).mul_nonsing_inv]
  · exact Matrix.one_mulVec x
  · exact isUnit_iff_ne_zero.mpr (actualDisplacementMatrix_det_ne_zero W p)

/-- The abstract inverse used in the conjugation theorem is the explicit matrix inverse. -/
public theorem actualDisplacementEquiv_symm_apply
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : PuncturedLocalCarrier W) (x : Fin 2 → ℝ) :
    (actualDisplacementEquiv W p.1 p.2).symm x =
      puncturedActualInverseDisplacement W p x := by
  apply (actualDisplacementEquiv W p.1 p.2).injective
  rw [LinearEquiv.apply_symm_apply, actualDisplacementEquiv_apply,
    effectiveFanDisplacement_puncturedActualInverseDisplacement]

/-- Matrix of the displacement with the phase correction frozen at the central parameter. -/
public noncomputable def frozenDisplacementMatrix
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (q : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + NormalizedFuchsianCuspCoordinate.phaseLogMatrix N 0 0 1 / Real.log ‖q‖,
      -NormalizedFuchsianCuspCoordinate.phaseLogMatrix N 0 0 0 / Real.log ‖q‖;
    NormalizedFuchsianCuspCoordinate.phaseLogMatrix N 0 1 1 / Real.log ‖q‖,
      1 - NormalizedFuchsianCuspCoordinate.phaseLogMatrix N 0 1 0 / Real.log ‖q‖]

@[simp]
public theorem frozenDisplacementMatrix_mulVec
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (q : ℂ) (d : Fin 2 → ℝ) :
    frozenDisplacementMatrix N q *ᵥ d = frozenEffectiveFanDisplacement N q d := by
  ext i
  fin_cases i <;>
    simp [frozenDisplacementMatrix, frozenEffectiveFanDisplacement, realFanShearInverse,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The frozen displacement matrices are continuous on the punctured collar. -/
public theorem continuous_frozenDisplacementMatrix
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (fun p : PuncturedLocalCarrier W ↦ frozenDisplacementMatrix N (M.t p.1)) := by
  have ht : Continuous (fun p : PuncturedLocalCarrier W ↦ M.t p.1) :=
    M.t_holomorphic.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hlog : Continuous (fun p : PuncturedLocalCarrier W ↦ Real.log ‖M.t p.1‖) :=
    ht.norm.log fun p ↦ norm_ne_zero_iff.mpr p.2
  have hlog_ne : ∀ p : PuncturedLocalCarrier W, Real.log ‖M.t p.1‖ ≠ 0 := by
    intro p
    exact Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.mpr p.2)
      (ne_of_lt ((mem_ball_zero_iff.mp p.1.property).trans W.localWitness.radius_lt_one))
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j
  · change Continuous (fun p : PuncturedLocalCarrier W ↦
      1 + NormalizedFuchsianCuspCoordinate.phaseLogMatrix N 0 0 1 / Real.log ‖M.t p.1‖)
    exact continuous_const.add (continuous_const.div hlog hlog_ne)
  · change Continuous (fun p : PuncturedLocalCarrier W ↦
      -NormalizedFuchsianCuspCoordinate.phaseLogMatrix N 0 0 0 / Real.log ‖M.t p.1‖)
    exact continuous_const.div hlog hlog_ne
  · change Continuous (fun p : PuncturedLocalCarrier W ↦
      NormalizedFuchsianCuspCoordinate.phaseLogMatrix N 0 1 1 / Real.log ‖M.t p.1‖)
    exact continuous_const.div hlog hlog_ne
  · change Continuous (fun p : PuncturedLocalCarrier W ↦
      1 - NormalizedFuchsianCuspCoordinate.phaseLogMatrix N 0 1 0 / Real.log ‖M.t p.1‖)
    exact continuous_const.sub (continuous_const.div hlog hlog_ne)

/-- The fully explicit punctured-fibre straightened rescaled position. -/
public noncomputable def explicitPuncturedStraightenedPosition
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (p : PuncturedLocalCarrier W) : Fin 2 → ℝ :=
  frozenDisplacementMatrix N (M.t p.1) *ᵥ
    puncturedActualInverseDisplacement W p (rescaledPosition M p.1)




end SphereSixComplex.Geometry.CuspStraighteningAlgebra
