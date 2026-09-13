module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundarySweepCoordinates
public import SphereSixComplex.Paper.Topology.CuspPeriodLoopDeckComparison
import all SphereSixComplex.Paper.LatticeData
import all SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryCharts

@[expose] public section
noncomputable section
open Set Matrix
open scoped ContinuousMap unitInterval
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralBoundary
open SphereSixComplex SphereSixComplex.Periods SphereSixComplex.LatticeData
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspCombinatorics
open StandardCircleHomologyLiftDegree
variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

def meridianDeck : Fin 3 → ParameterLattice := ![![0,0], ![0,-1], ![1,0]]

theorem meridianDeck_shear (i : Fin 3) :
    shearVector (meridianDeck i) = (upperChart i).2 := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [meridianDeck, upperChart, shearVector, B₀, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, e₁, e₂]

theorem upperPoint_zero_deck
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    let _ := actualLocalCuspQuotientAction W
    (upperPoint W i 0).1 =
      (Additive.toMul (meridianDeck i) : Multiplicative ParameterLattice) •
        constructedCentralOrigin W true := by
  let _ := actualLocalCuspQuotientAction W
  apply Subtype.ext
  rw [constructedCentralOrigin_smul_coe]
  change inclusion (upperChart i) (singleAxis (upperAxis i) 0) =
    inclusion (true, 0 + shearVector (meridianDeck i)) 0
  rw [singleAxis_zero, meridianDeck_shear, zero_add]
  rfl

def lowerMeridianLift
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    Path (constructedCentralOrigin W false) (axisPoint W false i 1).1 :=
  ((Path.segment (0 : ℂ) 1).map
    (continuous_subtype_val.comp (continuous_axisPoint W false i))).cast
      (by apply Subtype.ext; simp [axisPoint, singleAxis_zero, constructedCentralOrigin]; rfl) rfl

def upperMeridianLift
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    let _ := actualLocalCuspQuotientAction W
    Path (axisPoint W false i 1).1
      ((Additive.toMul (meridianDeck i) : Multiplicative ParameterLattice) •
        constructedCentralOrigin W true) := by
  let _ := actualLocalCuspQuotientAction W
  exact ((Path.segment (1 : ℂ) 0).map
    (continuous_subtype_val.comp (continuous_upperPoint W i))).cast
      (by
        apply Subtype.ext
        exact (lower_upper_carrier_eq_iff i 1 1).mpr ⟨one_ne_zero, inv_one.symm⟩)
      (upperPoint_zero_deck W i).symm

def meridianLift
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    let _ := actualLocalCuspQuotientAction W
    Path (constructedCentralOrigin W false)
      ((Additive.toMul (meridianDeck i) : Multiplicative ParameterLattice) •
        constructedCentralOrigin W true) :=
  (lowerMeridianLift W i).trans (upperMeridianLift W i)

def toFilling (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C(Spheres, ActualLocalCuspFilling W) :=
  ⟨fun x ↦ actualLocalCuspCentralOrbitMap W (homeomorph W x),
    (actualLocalCuspCentralOrbitMap_isEmbedding W).continuous.comp
      (continuous_subtype_val.comp (homeomorph W).continuous)⟩

theorem meridianLift_projects
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (t : unitInterval) :
    actualCuspFillingProjection W (meridianLift W i t) = toFilling W (meridian W i t) := by
  change actualCuspFillingProjection W ((lowerMeridianLift W i).trans _ t) =
    toFilling W ((lowerMeridian i).trans _ t)
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · rw [lowerMeridian_apply]
    dsimp only [toFilling, ContinuousMap.coe_mk]
    rw [homeomorph_mk_coe]
    simp [lowerMeridianLift, Path.segment, AffineMap.lineMap_apply]
    rfl
  · rw [upperMeridian_apply]
    dsimp only [toFilling, ContinuousMap.coe_mk]
    rw [homeomorph_reciprocalChart]
    simp [upperMeridianLift, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, add_comm]
    rfl

def meridianDifference (W : ActualPuncturedCuspCollarWitness N constructedModel) (i j : Fin 3) :
    Path (mk 0 (0 : ℂ)) (mk 0 (0 : ℂ)) :=
  (meridian W i).trans (meridian W j).symm

def meridianDifferenceLift
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i j : Fin 3) :
    let _ := actualLocalCuspQuotientAction W
    Path (constructedCentralOrigin W false)
      ((Additive.toMul (meridianDeck i - meridianDeck j) : Multiplicative ParameterLattice) •
        constructedCentralOrigin W false) := by
  let _ := actualLocalCuspQuotientAction W
  let _ := actualLocalPsiContinuousConstSMul W
  let g : Multiplicative ParameterLattice := Additive.toMul (meridianDeck i - meridianDeck j)
  let q := ((meridianLift W j).symm.map (continuous_const_smul g)).cast
    (show (Additive.toMul (meridianDeck i) : Multiplicative ParameterLattice) •
      constructedCentralOrigin W true =
        g • ((Additive.toMul (meridianDeck j) : Multiplicative ParameterLattice) •
          constructedCentralOrigin W true) from by
      rw [← mul_smul]
      congr 1
      change meridianDeck i = meridianDeck i - meridianDeck j + meridianDeck j
      abel) rfl
  exact (meridianLift W i).trans q

theorem meridianDifferenceLift_projects
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i j : Fin 3) (t : unitInterval) :
    actualCuspFillingProjection W (meridianDifferenceLift W i j t) =
      toFilling W (meridianDifference W i j t) := by
  let _ := actualLocalCuspQuotientAction W
  change actualCuspFillingProjection W ((meridianLift W i).trans _ t) =
    toFilling W ((meridian W i).trans _ t)
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact meridianLift_projects W i _
  · change actualCuspFillingProjection W
      ((Additive.toMul (meridianDeck i - meridianDeck j) : Multiplicative ParameterLattice) •
        meridianLift W j _) = _
    rw [(actualCuspFillingProjection_isQuotientCoveringMap W).map_smul]
    exact meridianLift_projects W j _

theorem meridianDifference_homology
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i j : Fin 3) :
    let _ := actualLocalCuspQuotientAction W
    let _ : SimplyConnectedSpace (localCarrier constructedModel W.localWitness.radius) :=
      constructedModel.localCarrierSimplyConnected W.localWitness.radius W.localWitness.radius_pos
    let hp := actualCuspFillingProjection_isQuotientCoveringMap W
    let _ : PathConnectedSpace (ActualLocalCuspFilling W) :=
      hp.surjective.pathConnectedSpace hp.continuous
    Topology.abelianCoverHomologyEquiv hp (constructedCentralOrigin W false)
      (meridianDeck i - meridianDeck j) =
        loopHomologyClass ((meridianDifference W i j).map (toFilling W).continuous) := by
  let _ := actualLocalCuspQuotientAction W
  let _ : SimplyConnectedSpace (localCarrier constructedModel W.localWitness.radius) :=
    constructedModel.localCarrierSimplyConnected W.localWitness.radius W.localWitness.radius_pos
  let hp := actualCuspFillingProjection_isQuotientCoveringMap W
  let _ : PathConnectedSpace (ActualLocalCuspFilling W) :=
    hp.surjective.pathConnectedSpace hp.continuous
  let q := (meridianDifference W i j).map (toFilling W).continuous
  have hb : actualCuspFillingProjection W (constructedCentralOrigin W false) =
      toFilling W (mk 0 (0 : ℂ)) := by
    dsimp only [toFilling, ContinuousMap.coe_mk]
    rw [homeomorph_mk_coe, axisOrbit_zero]
    rfl
  have h := Topology.abelianCoverHomologyEquiv_of_lift hp (constructedCentralOrigin W false)
    (constructedCentralOrigin W false) (Additive.toMul (meridianDeck i - meridianDeck j))
    (q.cast hb hb) (meridianDifferenceLift W i j) (meridianDifferenceLift_projects W i j)
  rw [loopHomologyClass_cast] at h
  exact h

theorem localCuspPeriodLoop_meridianHomology
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (s : ℂ) (hs : s ∈ cuspHalfPlane N.height)
    (hsr : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius)
    (a : ParameterLattice) :
    loopHomologyClass (localCuspPeriodLoop W s hs hsr a) =
      (-a 0 + a 1) • loopHomologyClass
        ((meridianDifference W 0 2).map (toFilling W).continuous) +
      (-a 1) • loopHomologyClass
        ((meridianDifference W 1 2).map (toFilling W).continuous) := by
  let _ := actualLocalCuspQuotientAction W
  let _ : SimplyConnectedSpace (localCarrier constructedModel W.localWitness.radius) :=
    constructedModel.localCarrierSimplyConnected W.localWitness.radius W.localWitness.radius_pos
  let hp := actualCuspFillingProjection_isQuotientCoveringMap W
  let _ : PathConnectedSpace (ActualLocalCuspFilling W) :=
    hp.surjective.pathConnectedSpace hp.continuous
  rw [← localCuspPeriodLoop_homology W s hs hsr (constructedCentralOrigin W false) a,
    ← meridianDifference_homology W 0 2, ← meridianDifference_homology W 1 2]
  let e := Topology.abelianCoverHomologyEquiv hp (constructedCentralOrigin W false)
  change e a = (-a 0 + a 1) • e (meridianDeck 0 - meridianDeck 2) +
    (-a 1) • e (meridianDeck 1 - meridianDeck 2)
  have ha : a = (-a 0 + a 1) • (meridianDeck 0 - meridianDeck 2) +
      (-a 1) • (meridianDeck 1 - meridianDeck 2) := by
    ext i
    fin_cases i <;> simp [meridianDeck]
  exact (congrArg e ha).trans ((e.map_add _ _).trans
    (congrArg₂ (· + ·) (map_zsmul e _ _) (map_zsmul e _ _)))

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralBoundary
