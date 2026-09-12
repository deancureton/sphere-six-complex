module
public import SphereSixComplex.Paper.Topology.CuspNormalizedPathHomotopy
public import SphereSixComplex.Prerequisites.Topology.CircleSweepWhiskerHomotopy

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex SphereSixComplex.Topology GlobalTorusFamily TriangleGroup
open SphereSixComplex.Periods
open SphereSixComplex.StandardTorusHomology

public def regularThirdCircleFamily (A : AnalyticData) :
    C(RegularBase (U := A.paperTriangleUniformization), C(StdTorus 1, A.CentralFamily)) :=
  ((regularPeriodCircleInGlobal A.periods (Pi.single 2 1)).comp
    ⟨fun p : RegularBase (U := A.paperTriangleUniformization) × StdTorus 1 =>
      (p.2 0, p.1), (continuous_apply 0 |>.comp continuous_snd).prodMk continuous_fst⟩).curry

public theorem regularThirdCircleFamily_gZero (A : AnalyticData) (k : ℤ)
    (b : RegularBase (U := A.paperTriangleUniformization)) :
    A.regularThirdCircleFamily (regularSourceEquiv (g₀ ^ k) b) =
      A.regularThirdCircleFamily b := by
  ext z
  have h := DFunLike.congr_fun
    (regularPeriodCircleFamily_deck A.periods (Pi.single 2 1) (g₀ ^ k) b) (z 0)
  rw [← zpow_neg, rhoLambda_thirdBasis_gZero_zpow] at h
  exact h

public def normalizedThirdPeriodLoop (A : AnalyticData)
    (p : Path A.affineNormalizedMidpoint
      (regularSourceEquiv g₀⁻¹ A.affineNormalizedMidpoint)) :
    Path (A.regularThirdCircleFamily A.affineNormalizedMidpoint)
      (A.regularThirdCircleFamily A.affineNormalizedMidpoint) :=
  (p.map A.regularThirdCircleFamily.continuous).cast rfl
    (by simpa using (A.regularThirdCircleFamily_gZero (-1)
      A.affineNormalizedMidpoint).symm)

public theorem normalizedThirdPeriodLoop_homotopic (A : AnalyticData) :
    (A.normalizedThirdPeriodLoop A.normalizedWhiskeredCuspRegularPath).Homotopic
      (A.normalizedThirdPeriodLoop A.normalizedMeridianPairRegularPath) :=
  (A.normalizedWhiskeredCuspRegularPath_homotopic_meridianPair.map
    A.regularThirdCircleFamily).pathCast _ _

public theorem regularThirdCircleFamily_peripheral (A : AnalyticData) (k : ℤ)
    (b : RegularBase (U := A.paperTriangleUniformization)) :
    A.regularThirdCircleFamily (regularSourceEquiv ((g₁ * g₂) ^ k) b) =
      A.regularThirdCircleFamily b := by
  ext z
  have h := DFunLike.congr_fun
    (regularPeriodCircleFamily_deck A.periods (Pi.single 2 1) ((g₁ * g₂) ^ k) b) (z 0)
  rw [← zpow_neg, rhoLambda_thirdBasis_peripheral_zpow] at h
  exact h

public theorem regularThirdCircleFamily_normalizedCuspEndpoint (A : AnalyticData) :
    A.regularThirdCircleFamily
      (regularSourceEquiv (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
        (regularTotalSpaceBase A.periods A.cuspRegularRepresentative)) =
      A.cuspChosenThirdPeriodFamily 0 := by
  rw [← zpow_neg, A.regularThirdCircleFamily_peripheral]
  rw [← A.cuspChosenPositiveRegularBase_zero]
  rfl

public def normalizedThirdCircleWhisker (A : AnalyticData) :
    Path (A.regularThirdCircleFamily A.affineNormalizedMidpoint)
      (A.cuspChosenThirdPeriodFamily 0) :=
  (A.affineNormalizedCuspPath.map A.regularThirdCircleFamily.continuous).cast rfl
    A.regularThirdCircleFamily_normalizedCuspEndpoint.symm

public theorem regularThirdCircleFamily_positivePath (A : AnalyticData) (t : unitInterval) :
    A.regularThirdCircleFamily (A.normalizedCuspPositiveRegularPath t) =
      A.cuspChosenThirdPeriodFamily t := by
  change A.regularThirdCircleFamily
    (regularSourceEquiv (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
      (A.cuspChosenPositiveRegularBase t)) = _
  rw [← zpow_neg, A.regularThirdCircleFamily_peripheral]
  rfl

public theorem normalizedThirdPeriodLoop_eq_whisker (A : AnalyticData) :
    A.normalizedThirdPeriodLoop A.normalizedWhiskeredCuspRegularPath =
      A.normalizedThirdCircleWhisker.trans
        (A.cuspChosenThirdPeriodLoop.trans A.normalizedThirdCircleWhisker.symm) := by
  apply Path.ext
  funext t
  simp only [normalizedThirdPeriodLoop, normalizedWhiskeredCuspRegularPath,
    normalizedThirdCircleWhisker, Path.cast_coe, Path.map_coe, Path.trans_apply,
    Path.symm_apply, Function.comp_apply]
  split_ifs
  · rfl
  · exact A.regularThirdCircleFamily_positivePath _
  · simpa using A.regularThirdCircleFamily_gZero (-1)
      (A.affineNormalizedCuspPath (unitInterval.symm _))

public def cuspChosenThirdSweep_homotopy_normalizedMeridians (A : AnalyticData) :
    (A.cuspChosenThirdSweepCentral.comp
      ((CircleProductIdentityMappingTorus.circleProductIdentityMappingTorusHomeomorph
        (X := StdTorus 1)).symm :
          C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)), UnitAddCircle × StdTorus 1))).Homotopy
      (identityMappingTorusMapOfLoop
        (A.normalizedThirdPeriodLoop A.normalizedMeridianPairRegularPath)) := by
  rw [← A.cuspChosenThirdSweepCentral_loop_realization]
  refine (identityMappingTorusMapOfLoop_whiskerHomotopy
    A.normalizedThirdCircleWhisker A.cuspChosenThirdPeriodLoop).symm.trans ?_
  rw [← A.normalizedThirdPeriodLoop_eq_whisker]
  exact identityMappingTorusMapOfLoop_homotopy A.normalizedThirdPeriodLoop_homotopic.some

end SphereSixComplex.Geometry.AnalyticData
end
