module

public import SphereSixComplex.Paper.Topology.ConstructedPositiveInteriorTorus
public import SphereSixComplex.Paper.Topology.ConstructedCuspPositiveProjection
public import SphereSixComplex.Paper.Topology.CuspFiniteFiberCoordinateTori

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open ComplexTorus CuspToricPhaseAction
open SphereSixComplex.Periods CuspFilling CuspLocalPhaseAction CuspPuncturedCollarBridge
open CuspPeriodExpansion CuspStraighteningRetraction CuspStraighteningAlgebra
open CuspStraighteningExtension
open CuspStraighteningHomeomorph StandardInfiniteA2ToricQuantitativeRegions
open CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate
open StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {r : ℝ}

theorem constructedModulus_torusCoordinates_norm
    (p : LocalCarrier constructedModel r) (hp : constructedModel.t p ≠ 0) (i : Fin 3) :
    ‖(torusCoordinates constructedModel (constructedLocalModulusRetraction r p) i : ℂ)‖ =
      ‖(torusCoordinates constructedModel p i : ℂ)‖ := by
  have hq : constructedModel.t (constructedLocalModulusRetraction r p) ≠ 0 := by
    rw [constructedLocalModulusRetraction_t]
    simpa using hp
  obtain ⟨phi, hphi⟩ := constructedLocalModulusRetraction_polar_surjective r p
  have hc : torusCoordinates constructedModel p = compactTorusEmbedding phi *
      torusCoordinates constructedModel (constructedLocalModulusRetraction r p) := by
    apply torusCoordinates_unique constructedModel hp
    rw [← constructedModel.torusAction_torus,
      torusEmbedding_torusCoordinates constructedModel hq]
    exact hphi
  rw [hc]
  change _ = ‖((compactTorusEmbedding phi i : ℂ) *
    (torusCoordinates constructedModel (constructedLocalModulusRetraction r p) i : ℂ))‖
  simp only [norm_mul]
  have hphiNorm : ‖(compactTorusEmbedding phi i : ℂ)‖ = 1 := by
    exact Circle.norm_coe (phi i)
  rw [hphiNorm, one_mul]

theorem constructedModulus_rescaledPosition
    (p : LocalCarrier constructedModel r) (hp : constructedModel.t p ≠ 0) :
    rescaledPosition constructedModel (constructedLocalModulusRetraction r p) =
      rescaledPosition constructedModel p := by
  ext i
  simp only [rescaledPosition, constructedModulus_torusCoordinates_norm p hp,
    constructedLocalModulusRetraction_t, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]

def constructedPuncturedModulus
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (p : PuncturedLocalCarrier W) :
    constructedA2PositiveOffCentral W.localWitness.radius :=
  ⟨constructedLocalModulusRetraction W.localWitness.radius p.1, by
    change constructedModel.t (constructedLocalModulusRetraction W.localWitness.radius p.1) ≠ 0
    rw [constructedLocalModulusRetraction_t]
    simpa using p.2⟩

theorem positiveInteriorLogProduct_modulus
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (p : PuncturedLocalCarrier W) :
    (positiveInteriorLogProduct W (constructedPuncturedModulus W p)).1 =
      inverseStraighteningRealParameter W p := by
  rw [positiveInteriorLogProduct_first]
  change CuspFillingRadialCompactness.realFanShearInverse
    ((frozenDisplacementMatrix N
      (constructedModel.t (constructedLocalModulusRetraction W.localWitness.radius p.1)))⁻¹ *ᵥ
      rescaledPosition constructedModel
        (constructedLocalModulusRetraction W.localWitness.radius p.1)) = _
  rw [constructedModulus_rescaledPosition p.1 p.2, constructedLocalModulusRetraction_t]
  simp only [frozenDisplacementMatrix, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  rfl

theorem positiveInteriorLogProduct_straightened_modulus
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (p : PuncturedLocalCarrier W) :
    (positiveInteriorLogProduct W
      (constructedPuncturedModulus W (puncturedPointStraightening W p))).1 =
      CuspStraighteningExtension.straighteningRealParameter W p := by
  rw [positiveInteriorLogProduct_modulus,
    inverseStraighteningRealParameter_puncturedPointStraightening]

theorem rescaledPosition_localCuspExponentialPoint
    (M : Model) (zeta : ComplexTorus.ComplexTwoSpace) (s : ℂ)
    (hs : cuspQ s ∈ Metric.ball (0 : ℂ) r) :
    rescaledPosition M (localCuspExponentialPoint M r zeta s hs) =
      fun i ↦ (-2 * Real.pi * (zeta i).im) / Real.log ‖cuspQ s‖ := by
  have hp : M.t (localCuspExponentialPoint M r zeta s hs) ≠ 0 := by
    rw [localCuspExponentialPoint_t]
    exact Complex.exp_ne_zero _
  have hc : torusCoordinates M (localCuspExponentialPoint M r zeta s hs) =
      denseCuspExponential zeta s := torusCoordinates_unique M hp rfl
  ext i
  simp only [rescaledPosition, hc, localCuspExponentialPoint_t]
  congr 1
  fin_cases i <;>
    simp [denseCuspExponential, CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exponentialUnit,
      Complex.norm_exp, Complex.mul_re, Complex.mul_im, Real.log_exp]

def exponentialStraighteningCoordinate
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (s : ℂ)
    (hs : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius)
    (zeta : ComplexTorus.ComplexTwoSpace) : Fin 2 → ℝ :=
  straighteningRealParameter W
    ⟨localCuspExponentialPoint constructedModel W.localWitness.radius zeta s hs, by
      rw [localCuspExponentialPoint_t]
      exact Complex.exp_ne_zero _⟩

theorem exponentialStraighteningCoordinate_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (s : ℂ)
    (hs : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius)
    (zeta : ComplexTorus.ComplexTwoSpace) :
    exponentialStraighteningCoordinate W s hs zeta =
      CuspFillingRadialCompactness.realFanShearInverse
        ((actualDisplacementMatrix N (cuspQ s))⁻¹ *ᵥ
          (fun i ↦ (-2 * Real.pi * (zeta i).im) / Real.log ‖cuspQ s‖)) := by
  unfold exponentialStraighteningCoordinate straighteningRealParameter
    puncturedActualInverseDisplacement
  rw [localCuspExponentialPoint_t, rescaledPosition_localCuspExponentialPoint]

theorem exponentialStraighteningCoordinate_add
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (s : ℂ)
    (hs : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius)
    (zeta eta : ComplexTorus.ComplexTwoSpace) :
    exponentialStraighteningCoordinate W s hs (zeta + eta) =
      exponentialStraighteningCoordinate W s hs zeta +
        exponentialStraighteningCoordinate W s hs eta := by
  simp only [exponentialStraighteningCoordinate_eq, Pi.add_apply, Complex.add_im,
    mul_add, add_div]
  rw [show (fun i ↦ -2 * Real.pi * (zeta i).im / Real.log ‖cuspQ s‖ +
      -2 * Real.pi * (eta i).im / Real.log ‖cuspQ s‖) =
    (fun i ↦ -2 * Real.pi * (zeta i).im / Real.log ‖cuspQ s‖) +
      (fun i ↦ -2 * Real.pi * (eta i).im / Real.log ‖cuspQ s‖) from rfl,
    Matrix.mulVec_add, CuspFillingRadialCompactness.realFanShearInverse_add]

theorem exponentialStraighteningCoordinate_smul
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (s : ℂ)
    (hs : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius)
    (c : ℝ) (zeta : ComplexTorus.ComplexTwoSpace) :
    exponentialStraighteningCoordinate W s hs (c • zeta) =
      c • exponentialStraighteningCoordinate W s hs zeta := by
  rw [exponentialStraighteningCoordinate_eq, exponentialStraighteningCoordinate_eq]
  have h : (fun i ↦ -2 * Real.pi * ((c • zeta) i).im / Real.log ‖cuspQ s‖) =
      c • (fun i ↦ -2 * Real.pi * (zeta i).im / Real.log ‖cuspQ s‖) := by
    ext i
    simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, smul_eq_mul]
    ring
  rw [h, Matrix.mulVec_smul, CuspFillingRadialCompactness.realFanShearInverse_smul]

theorem exponentialStraighteningCoordinate_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (s : ℂ)
    (hs : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius) :
    exponentialStraighteningCoordinate W s hs 0 = 0 := by
  simp [exponentialStraighteningCoordinate_eq,
    CuspFillingRadialCompactness.realFanShearInverse]

theorem exponentialStraighteningCoordinate_period
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height)
    (hsr : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius)
    (lambda : ParameterLattice) :
    exponentialStraighteningCoordinate W s hsr
      (periodVector (actualCuspCollarPeriodParameter N s) (firstPeriodCoefficients lambda)) =
      realParameter lambda := by
  let p := localCuspExponentialPoint constructedModel W.localWitness.radius 0 s hsr
  have hp : constructedModel.t p ≠ 0 := by
    rw [localCuspExponentialPoint_t]
    exact Complex.exp_ne_zero _
  have he := localCuspExponentialPoint_period_equivariant N constructedModel
    W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le s hs hsr 0 lambda
  dsimp only at he
  rw [add_zero] at he
  have ht := straighteningRealParameter_psiMap W lambda p hp
  dsimp only at ht
  simp only [p, he] at ht
  change exponentialStraighteningCoordinate W s hsr
      ((periodBlock (actualCuspCollarPeriodParameter N s)).mulVec (fun i ↦ (lambda i : ℂ))) =
    exponentialStraighteningCoordinate W s hsr 0 + realParameter lambda at ht
  rw [exponentialStraighteningCoordinate_zero, zero_add] at ht
  rw [periodVector_firstPeriodCoefficients]
  exact ht

theorem exponentialStraighteningCoordinate_firstTwoPeriods
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height)
    (hsr : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius) (a b : ℝ) :
    exponentialStraighteningCoordinate W s hsr
      (a • periodVector (actualCuspCollarPeriodParameter N s) (Pi.single 0 1) +
        b • periodVector (actualCuspCollarPeriodParameter N s) (Pi.single 1 1)) = ![a, b] := by
  rw [exponentialStraighteningCoordinate_add, exponentialStraighteningCoordinate_smul,
    exponentialStraighteningCoordinate_smul]
  have h0 : (Pi.single 0 1 : IntegerPeriods) = firstPeriodCoefficients (Pi.single 0 1) := by
    ext i
    fin_cases i <;> rfl
  have h1 : (Pi.single 1 1 : IntegerPeriods) = firstPeriodCoefficients (Pi.single 1 1) := by
    ext i
    fin_cases i <;> rfl
  rw [h0, h1, exponentialStraighteningCoordinate_period W s hs,
    exponentialStraighteningCoordinate_period W s hs]
  ext i
  fin_cases i <;> simp [realParameter]

theorem constructedCuspPositiveProjection_punctured
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (p : PuncturedLocalCarrier W) :
    constructedCuspPositiveProjection W (Quotient.mk _ p.1) =
      (constructedPositiveInteriorProjection W
        (constructedPuncturedModulus W (puncturedPointStraightening W p))).1 := by
  change Quotient.mk _ (constructedLocalModulusRetraction W.localWitness.radius
    (pointStraightening W p.1)) = _
  rw [pointStraightening_of_t_ne_zero W p.1 p.2]
  rfl

theorem constructedPositiveInteriorTorusHomeomorph_exponential_first
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (s : ℂ)
    (hs : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius)
    (zeta : ComplexTwoSpace) :
    (constructedPositiveInteriorTorusHomeomorph W
      (constructedPositiveInteriorProjection W
        (constructedPuncturedModulus W (puncturedPointStraightening W
          ⟨localCuspExponentialPoint constructedModel W.localWitness.radius zeta s hs,
            by rw [localCuspExponentialPoint_t]; exact Complex.exp_ne_zero _⟩)))).1 =
      fun i ↦ (exponentialStraighteningCoordinate W s hs zeta i : UnitAddCircle) := by
  rw [constructedPositiveInteriorTorusHomeomorph_projection]
  change (fun i ↦ ((positiveInteriorLogProduct W
    (constructedPuncturedModulus W (puncturedPointStraightening W _))).1 i : UnitAddCircle)) = _
  rw [positiveInteriorLogProduct_straightened_modulus]
  rfl

theorem positiveInteriorLogProduct_straightened_modulus_height
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (p : PuncturedLocalCarrier W) :
    ((positiveInteriorLogProduct W
      (constructedPuncturedModulus W (puncturedPointStraightening W p))).2 : ℝ) =
      ‖constructedModel.t p.1‖ := by
  change ‖constructedModel.t
    (constructedLocalModulusRetraction W.localWitness.radius
      (puncturedPointStraightening W p).1)‖ = _
  rw [constructedLocalModulusRetraction_t]
  simp only [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  congr 1
  change constructedModel.t (constructedModel.torusEmbedding
    (phaseEmbedding (straighteningPhase W p) * torusCoordinates constructedModel p.1)) = _
  rw [constructedModel.t_torus, Pi.mul_apply, phaseEmbedding_apply_two, one_mul,
    torusCoordinates_last constructedModel p.2]

theorem constructedPositiveInteriorTorusHomeomorph_firstTwoPeriods
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height)
    (hsr : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius) (a b : ℝ) :
    constructedPositiveInteriorTorusHomeomorph W
      (constructedPositiveInteriorProjection W
        (constructedPuncturedModulus W (puncturedPointStraightening W
          ⟨localCuspExponentialPoint constructedModel W.localWitness.radius
            (a • periodVector (actualCuspCollarPeriodParameter N s) (Pi.single 0 1) +
              b • periodVector (actualCuspCollarPeriodParameter N s) (Pi.single 1 1)) s hsr,
            by rw [localCuspExponentialPoint_t]; exact Complex.exp_ne_zero _⟩))) =
      (![ (a : UnitAddCircle), (b : UnitAddCircle)],
        ⟨‖cuspQ s‖, norm_pos_iff.mpr (Complex.exp_ne_zero _), mem_ball_zero_iff.mp hsr⟩) := by
  apply Prod.ext
  · rw [constructedPositiveInteriorTorusHomeomorph_exponential_first,
      exponentialStraighteningCoordinate_firstTwoPeriods W s hs]
    ext i
    fin_cases i <;> rfl
  · apply Subtype.ext
    rw [constructedPositiveInteriorTorusHomeomorph_projection]
    change ((positiveInteriorLogProduct W
      (constructedPuncturedModulus W (puncturedPointStraightening W _))).2 : ℝ) = _
    rw [positiveInteriorLogProduct_straightened_modulus_height,
      localCuspExponentialPoint_t]

theorem constructedCuspPositiveProjection_firstTorus_real
    (A : PaperAnalyticData) (a b : ℝ) :
    constructedCuspPositiveProjection A.starCuspWitness
      (A.cuspFiniteFiberTorusToFilling 0 ![(a : UnitAddCircle), (b : UnitAddCircle)]) =
      ((constructedPositiveInteriorTorusHomeomorph A.starCuspWitness).symm
        (![ (a : UnitAddCircle), (b : UnitAddCircle)],
          ⟨‖cuspQ (CuspRadialClutchingConstruction.markedCuspParameter A.starCuspWitness)‖,
            norm_pos_iff.mpr (Complex.exp_ne_zero _),
            (CuspRadialClutchingConstruction.actualCuspRadialClutchingData
              A.starCuspWitness).markingParameter_mem⟩)).1 := by
  let W := A.starCuspWitness
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData W
  let s := CuspRadialClutchingConstruction.markedCuspParameter W
  have hs : s ∈ cuspHalfPlane A.cuspCoordinate.height :=
    mem_cuspHalfPlane_of_norm_cuspQ_lt W.localWitness.radius_le G.markingParameter_mem
  have hsr : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius :=
    mem_ball_zero_iff.mpr G.markingParameter_mem
  rw [A.cuspFiniteFiberTorusToFilling_real]
  dsimp only
  change constructedCuspPositiveProjection W
    (Quotient.mk _ (localCuspExponentialPoint constructedModel W.localWitness.radius
      (a • periodVector (actualCuspCollarPeriodParameter A.cuspCoordinate s) (Pi.single 0 1) +
        b • periodVector (actualCuspCollarPeriodParameter A.cuspCoordinate s) (Pi.single 1 1))
      s hsr)) = _
  have hp : constructedModel.t (localCuspExponentialPoint constructedModel W.localWitness.radius
      (a • periodVector (actualCuspCollarPeriodParameter A.cuspCoordinate s) (Pi.single 0 1) +
        b • periodVector (actualCuspCollarPeriodParameter A.cuspCoordinate s) (Pi.single 1 1))
      s hsr) ≠ 0 := by
    rw [localCuspExponentialPoint_t]
    exact Complex.exp_ne_zero _
  rw [constructedCuspPositiveProjection_punctured W ⟨_, hp⟩]
  apply congrArg Subtype.val
  apply (constructedPositiveInteriorTorusHomeomorph W).injective
  rw [Homeomorph.apply_symm_apply,
    constructedPositiveInteriorTorusHomeomorph_firstTwoPeriods W s hs]

theorem constructedCuspPositiveProjection_firstTorus
    (A : PaperAnalyticData) (z : SphereSixComplex.StandardTorusHomology.StdTorus 2) :
    constructedCuspPositiveProjection A.starCuspWitness (A.cuspFiniteFiberTorusToFilling 0 z) =
      ((constructedPositiveInteriorTorusHomeomorph A.starCuspWitness).symm
        (z, ⟨‖cuspQ (CuspRadialClutchingConstruction.markedCuspParameter A.starCuspWitness)‖,
          norm_pos_iff.mpr (Complex.exp_ne_zero _),
          (CuspRadialClutchingConstruction.actualCuspRadialClutchingData
            A.starCuspWitness).markingParameter_mem⟩)).1 := by
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (z 0)
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk_surjective (z 1)
  have hz : z = ![(a : UnitAddCircle), (b : UnitAddCircle)] := by
    ext i
    fin_cases i
    · exact ha.symm
    · exact hb.symm
  rw [hz]
  exact constructedCuspPositiveProjection_firstTorus_real A a b

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
