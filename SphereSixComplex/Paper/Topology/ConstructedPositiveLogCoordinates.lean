module

public import SphereSixComplex.Paper.Topology.ConstructedPositiveQuotientInterior
public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveInteriorContractibility

@[expose] public section

noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex.Periods CuspFilling CuspLocalPhaseAction CuspPuncturedCollarBridge
open CuspPeriodExpansion CuspStraighteningRetraction CuspStraighteningAlgebra
open CuspStraighteningHomeomorph StandardInfiniteA2ToricQuantitativeRegions
open CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}

theorem positiveDeck_preserves_height (lambda : ParameterLattice) (p : LocalCarrier M r) :
    M.t (normalizedPositiveDeckLocalMap N M r lambda p) = M.t p := by
  change M.t (M.torusAction _ (Additive.toMul (M.fanShear lambda) p.1)) = _
  rw [M.t_torusAction, normalizedCuspPositiveTwist_last]
  simp only [Units.val_one, one_mul, M.fanShear_preserves_t]

theorem positiveDeck_torusCoordinates (lambda : ParameterLattice)
    (p : LocalCarrier M r) (hp : M.t p ≠ 0) :
    torusCoordinates M (normalizedPositiveDeckLocalMap N M r lambda p) =
      normalizedCuspPositiveTwist N lambda * denseTorusShear lambda (torusCoordinates M p) := by
  apply M.torus_openEmbedding.injective
  rw [torusEmbedding_torusCoordinates M (by rw [positiveDeck_preserves_height]; exact hp)]
  change M.torusAction _ (Additive.toMul (M.fanShear lambda) p.1) = _
  rw [← torusEmbedding_torusCoordinates M hp, M.fanShear_torus, M.torusAction_torus]
  rw [torusEmbedding_torusCoordinates M hp]

theorem positiveDeck_logCoordinate (lambda : ParameterLattice)
    (p : LocalCarrier M r) (hp : M.t p ≠ 0) (i : Fin 2) :
    Real.log ‖(torusCoordinates M (normalizedPositiveDeckLocalMap N M r lambda p)
      i.castSucc : ℂ)‖ =
    (phaseLogMatrix N 0).mulVec (realParameter lambda) i +
      Real.log ‖(torusCoordinates M p i.castSucc : ℂ)‖ +
        (shearVector lambda i : ℝ) * Real.log ‖M.t p‖ := by
  rw [positiveDeck_torusCoordinates lambda p hp]
  have he : (normalizedCuspPositiveTwist N lambda * denseTorusShear lambda (torusCoordinates M p))
      i.castSucc = normalizedCuspPositiveTwist N lambda i.castSucc *
        (torusCoordinates M p i.castSucc * torusCoordinates M p 2 ^ shearVector lambda i) := by
    fin_cases i <;> rfl
  rw [he]
  simp only [Units.val_mul, norm_mul]
  rw [Real.log_mul (ne_of_gt (Units.norm_pos _))
      (mul_ne_zero (ne_of_gt (Units.norm_pos _)) (ne_of_gt (Units.norm_pos _))),
    Real.log_mul (ne_of_gt (Units.norm_pos _)) (ne_of_gt (Units.norm_pos _)),
    show ((torusCoordinates M p 2 ^ shearVector lambda i : ℂˣ) : ℂ) =
      (torusCoordinates M p 2 : ℂ) ^ shearVector lambda i from map_zpow (Units.coeHom ℂ) _ _,
    norm_zpow, Real.log_zpow, torusCoordinates_last M hp,
    log_norm_normalizedCuspPositiveTwist]
  ring

theorem positiveDeck_rescaledPosition (hr : r < 1) (lambda : ParameterLattice)
    (p : LocalCarrier M r) (hp : M.t p ≠ 0) :
    rescaledPosition M (normalizedPositiveDeckLocalMap N M r lambda p) =
      rescaledPosition M p + frozenEffectiveFanDisplacement N (M.t p)
        (fun i ↦ (shearVector lambda i : ℝ)) := by
  have hlog : Real.log ‖M.t p‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one
    (norm_pos_iff.mpr hp) (ne_of_lt ((mem_ball_zero_iff.mp p.2).trans hr))
  ext i
  simp only [rescaledPosition, Pi.add_apply, frozenEffectiveFanDisplacement,
    CuspFillingRadialCompactness.realFanShearInverse_shearVector]
  rw [positiveDeck_preserves_height, positiveDeck_logCoordinate lambda p hp i]
  field_simp
  ring

def positiveLogPeriodCoordinate (W : ActualPuncturedCuspCollarWitness N M)
    (p : PuncturedLocalCarrier W) : Fin 2 → ℝ :=
  CuspFillingRadialCompactness.realFanShearInverse
    ((frozenDisplacementMatrix N (M.t p.1))⁻¹ *ᵥ rescaledPosition M p.1)

def positivePuncturedDeck (W : ActualPuncturedCuspCollarWitness N M)
    (lambda : ParameterLattice) (p : PuncturedLocalCarrier W) : PuncturedLocalCarrier W :=
  ⟨normalizedPositiveDeckLocalMap N M W.localWitness.radius lambda p.1,
    by rw [positiveDeck_preserves_height]; exact p.2⟩

theorem positiveLogPeriodCoordinate_deck (W : ActualPuncturedCuspCollarWitness N M)
    (lambda : ParameterLattice) (p : PuncturedLocalCarrier W) :
    positiveLogPeriodCoordinate W (positivePuncturedDeck W lambda p) =
      positiveLogPeriodCoordinate W p + realParameter lambda := by
  unfold positiveLogPeriodCoordinate
  change CuspFillingRadialCompactness.realFanShearInverse
    ((frozenDisplacementMatrix N (M.t (normalizedPositiveDeckLocalMap N M
      W.localWitness.radius lambda p.1)))⁻¹ *ᵥ
      rescaledPosition M (normalizedPositiveDeckLocalMap N M W.localWitness.radius lambda p.1)) = _
  rw [positiveDeck_preserves_height,
    positiveDeck_rescaledPosition W.localWitness.radius_lt_one lambda p.1 p.2,
    Matrix.mulVec_add, ← frozenDisplacementMatrix_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (frozenDisplacementMatrix_det_ne_zero W p)),
    Matrix.one_mulVec, CuspFillingRadialCompactness.realFanShearInverse_add,
    CuspFillingRadialCompactness.realFanShearInverse_shearVector]

theorem positiveLogPeriodCoordinate_continuous (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (positiveLogPeriodCoordinate W) :=
  continuous_inverseStraighteningRealParameter W

open StandardInfiniteA2ToricModel.Construction

def positiveInteriorRegionProduct (r : ℝ) :
    constructedA2PositiveInteriorRegion r ≃ₜ ((Fin 2 → ℝ) × Set.Ioo (0 : ℝ) r) where
  toFun x := (fun i ↦ x.1 i.castSucc, ⟨x.1 2, x.2⟩)
  invFun x := ⟨![x.1 0, x.1 1, x.2.1], x.2.2⟩
  left_inv x := by apply Subtype.ext; ext i; fin_cases i <;> rfl
  right_inv x := by ext i; fin_cases i <;> rfl; rfl
  continuous_toFun := (continuous_pi (fun i ↦ (continuous_apply i.castSucc).comp continuous_subtype_val)).prodMk
    (((continuous_apply 2).comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := by fun_prop

def positiveInteriorRawProduct (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedA2PositiveOffCentral W.localWitness.radius ≃ₜ
      ((Fin 2 → ℝ) × Set.Ioo (0 : ℝ) W.localWitness.radius) :=
  (constructedA2PositiveInteriorHomeomorph W.localWitness.radius_lt_one).trans
    (positiveInteriorRegionProduct W.localWitness.radius)

def positiveHeightReference (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (t : Set.Ioo (0 : ℝ) W.localWitness.radius) : PuncturedLocalCarrier W :=
  let p := (positiveInteriorRawProduct W).symm (0, t)
  ⟨p.1.1, p.2⟩

theorem positiveHeightReference_height (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (t : Set.Ioo (0 : ℝ) W.localWitness.radius) :
    constructedModel.t (positiveHeightReference W t).1 = (t.1 : ℂ) := by
  exact constructedA2OffCentralMomentInverse_t _ _

theorem positiveHeightReference_continuous (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (positiveHeightReference W) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_subtype_val).comp
    ((positiveInteriorRawProduct W).symm.continuous.comp (continuous_const.prodMk continuous_id))

def positiveHeightDisplacement (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (t : Set.Ioo (0 : ℝ) W.localWitness.radius) : Matrix (Fin 2) (Fin 2) ℝ :=
  frozenDisplacementMatrix N (t.1 : ℂ)

theorem positiveHeightDisplacement_continuous (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (positiveHeightDisplacement W) := by
  change Continuous (fun t : Set.Ioo (0 : ℝ) W.localWitness.radius ↦ frozenDisplacementMatrix N (t.1 : ℂ))
  have h := (continuous_frozenDisplacementMatrix W).comp (positiveHeightReference_continuous W)
  simpa only [Function.comp_def, positiveHeightReference_height, positiveHeightDisplacement] using h

theorem positiveHeightDisplacement_inverse_continuous (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (fun t ↦ (positiveHeightDisplacement W t)⁻¹) := by
  have h := (continuous_frozenDisplacementMatrix_inv W).comp (positiveHeightReference_continuous W)
  simpa only [Function.comp_def, positiveHeightReference_height, positiveHeightDisplacement] using h

theorem positiveHeightDisplacement_unit (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (t : Set.Ioo (0 : ℝ) W.localWitness.radius) : IsUnit (positiveHeightDisplacement W t).det := by
  have h := frozenDisplacementMatrix_det_ne_zero W (positiveHeightReference W t)
  rw [positiveHeightReference_height] at h
  exact isUnit_iff_ne_zero.mpr h

def positiveLogProductNormalization (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ((Fin 2 → ℝ) × Set.Ioo (0 : ℝ) W.localWitness.radius) ≃ₜ
      ((Fin 2 → ℝ) × Set.Ioo (0 : ℝ) W.localWitness.radius) where
  toFun x := (CuspFillingRadialCompactness.realFanShearInverse
    ((positiveHeightDisplacement W x.2)⁻¹ *ᵥ x.1), x.2)
  invFun x := ((positiveHeightDisplacement W x.2) *ᵥ ![x.1 1, -x.1 0], x.2)
  left_inv x := by
    apply Prod.ext
    swap
    · rfl
    change positiveHeightDisplacement W x.2 *ᵥ
      ![((positiveHeightDisplacement W x.2)⁻¹ *ᵥ x.1) 0,
        -(-((positiveHeightDisplacement W x.2)⁻¹ *ᵥ x.1) 1)] = x.1
    simp only [neg_neg]
    have hv (v : Fin 2 → ℝ) : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    rw [hv, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (positiveHeightDisplacement_unit W x.2), Matrix.one_mulVec]
  right_inv x := by
    apply Prod.ext
    swap
    · rfl
    change CuspFillingRadialCompactness.realFanShearInverse
      ((positiveHeightDisplacement W x.2)⁻¹ *ᵥ
        (positiveHeightDisplacement W x.2 *ᵥ ![x.1 1, -x.1 0])) = x.1
    rw [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (positiveHeightDisplacement_unit W x.2), Matrix.one_mulVec]
    ext i
    fin_cases i <;> simp [CuspFillingRadialCompactness.realFanShearInverse]
  continuous_toFun := by
    have h : Continuous (fun x : (Fin 2 → ℝ) × Set.Ioo (0 : ℝ) W.localWitness.radius ↦
        (positiveHeightDisplacement W x.2)⁻¹ *ᵥ x.1) :=
      ((positiveHeightDisplacement_inverse_continuous W).comp continuous_snd).matrix_mulVec continuous_fst
    exact (continuous_pi (fun i ↦ by
      fin_cases i
      · exact ((continuous_apply 1).comp h).neg
      · exact (continuous_apply 0).comp h)).prodMk continuous_snd
  continuous_invFun := by
    apply Continuous.prodMk _ continuous_snd
    exact ((positiveHeightDisplacement_continuous W).comp continuous_snd).matrix_mulVec (by fun_prop)

def positiveInteriorLogProduct (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    constructedA2PositiveOffCentral W.localWitness.radius ≃ₜ
      ((Fin 2 → ℝ) × Set.Ioo (0 : ℝ) W.localWitness.radius) :=
  (positiveInteriorRawProduct W).trans (positiveLogProductNormalization W)

theorem positivePart_height_eq_norm (q : constructedLocalPositivePart r) :
    constructedModel.t q.1 = (‖constructedModel.t q.1‖ : ℝ) := by
  have h := constructedLocalModulusRetraction_t r q.1
  rw [constructedLocalModulusRetraction_fixed] at h
  exact h

theorem positiveInteriorLogProduct_first
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : constructedA2PositiveOffCentral W.localWitness.radius) :
    (positiveInteriorLogProduct W q).1 = positiveLogPeriodCoordinate W ⟨q.1.1, q.2⟩ := by
  change CuspFillingRadialCompactness.realFanShearInverse
    ((frozenDisplacementMatrix N (‖constructedModel.t q.1.1‖ : ℝ))⁻¹ *ᵥ
      (fun i : Fin 2 ↦ (![rescaledPosition constructedModel q.1.1 0,
        rescaledPosition constructedModel q.1.1 1, ‖constructedModel.t q.1.1‖] : Fin 3 → ℝ) i.castSucc)) = _
  have hv : (fun i : Fin 2 ↦ (![rescaledPosition constructedModel q.1.1 0,
      rescaledPosition constructedModel q.1.1 1, ‖constructedModel.t q.1.1‖] : Fin 3 → ℝ) i.castSucc) =
      rescaledPosition constructedModel q.1.1 := by ext i; fin_cases i <;> rfl
  rw [hv, ← positivePart_height_eq_norm q.1]
  rfl

def positiveOffCentralDeck (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (lambda : ParameterLattice) (q : constructedA2PositiveOffCentral W.localWitness.radius) :
    constructedA2PositiveOffCentral W.localWitness.radius :=
  ⟨⟨normalizedPositiveDeckLocalMap N constructedModel W.localWitness.radius lambda q.1.1,
    constructedPositiveDeck_mem N W.localWitness.radius lambda q.1⟩,
    by
      change constructedModel.t (normalizedPositiveDeckLocalMap N constructedModel W.localWitness.radius lambda q.1.1) ≠ 0
      rw [positiveDeck_preserves_height]
      exact q.2⟩

theorem positiveInteriorLogProduct_deck
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (lambda : ParameterLattice) (q : constructedA2PositiveOffCentral W.localWitness.radius) :
    positiveInteriorLogProduct W (positiveOffCentralDeck W lambda q) =
      ((positiveInteriorLogProduct W q).1 + realParameter lambda,
        (positiveInteriorLogProduct W q).2) := by
  apply Prod.ext
  · rw [positiveInteriorLogProduct_first, positiveInteriorLogProduct_first]
    exact positiveLogPeriodCoordinate_deck W lambda ⟨q.1.1, q.2⟩
  · apply Subtype.ext
    change ‖constructedModel.t (normalizedPositiveDeckLocalMap N constructedModel W.localWitness.radius lambda q.1.1)‖ =
      ‖constructedModel.t q.1.1‖
    rw [positiveDeck_preserves_height]

theorem positiveOffCentralDeck_eq_iff_logProduct
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (lambda : ParameterLattice) (p q : constructedA2PositiveOffCentral W.localWitness.radius) :
    positiveOffCentralDeck W lambda p = q ↔
      (positiveInteriorLogProduct W q).1 =
          (positiveInteriorLogProduct W p).1 + realParameter lambda ∧
        (positiveInteriorLogProduct W q).2 = (positiveInteriorLogProduct W p).2 := by
  rw [← (positiveInteriorLogProduct W).injective.eq_iff,
    positiveInteriorLogProduct_deck, Prod.mk.injEq]
  exact and_congr eq_comm eq_comm

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
