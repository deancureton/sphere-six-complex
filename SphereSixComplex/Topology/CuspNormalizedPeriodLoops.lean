module
public import SphereSixComplex.Topology.CuspNormalizedPathHomotopy
public import SphereSixComplex.Topology.CuspThirdPeripheralInvariance
public import SphereSixComplex.Topology.CircleSweepWhiskerHomotopy

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex SphereSixComplex.Topology GlobalTorusFamily TriangleGroup
open SphereSixComplex.Periods
open SphereSixComplex.StandardTorusHomology

public def regularThirdCircleFamily (A : PaperAnalyticData) :
    C(RegularBase (U := A.paperTriangleUniformization), C(StdTorus 1, A.CentralFamily)) :=
  ((regularPeriodCircleInGlobal A.periods (Pi.single 2 1)).comp
    ⟨fun p : RegularBase (U := A.paperTriangleUniformization) × StdTorus 1 =>
      (p.2 0, p.1), (continuous_apply 0 |>.comp continuous_snd).prodMk continuous_fst⟩).curry

public theorem regularThirdCircleFamily_gZero (A : PaperAnalyticData) (k : ℤ)
    (b : RegularBase (U := A.paperTriangleUniformization)) :
    A.regularThirdCircleFamily (regularSourceEquiv (g₀ ^ k) b) =
      A.regularThirdCircleFamily b := by
  ext z
  have h := DFunLike.congr_fun
    (regularPeriodCircleFamily_deck A.periods (Pi.single 2 1) (g₀ ^ k) b) (z 0)
  rw [← zpow_neg, rhoLambda_thirdBasis_gZero_zpow] at h
  exact h

public def normalizedThirdPeriodLoop (A : PaperAnalyticData)
    (p : Path A.sectionSevenAffineNormalizedMidpoint
      (regularSourceEquiv g₀⁻¹ A.sectionSevenAffineNormalizedMidpoint)) :
    Path (A.regularThirdCircleFamily A.sectionSevenAffineNormalizedMidpoint)
      (A.regularThirdCircleFamily A.sectionSevenAffineNormalizedMidpoint) :=
  (p.map A.regularThirdCircleFamily.continuous).cast rfl
    (by simpa using (A.regularThirdCircleFamily_gZero (-1)
      A.sectionSevenAffineNormalizedMidpoint).symm)

public theorem normalizedThirdPeriodLoop_homotopic (A : PaperAnalyticData) :
    (A.normalizedThirdPeriodLoop A.normalizedWhiskeredCuspRegularPath).Homotopic
      (A.normalizedThirdPeriodLoop A.normalizedMeridianPairRegularPath) :=
  (A.normalizedWhiskeredCuspRegularPath_homotopic_meridianPair.map
    A.regularThirdCircleFamily).pathCast _ _

public theorem regularThirdCircleFamily_peripheral (A : PaperAnalyticData) (k : ℤ)
    (b : RegularBase (U := A.paperTriangleUniformization)) :
    A.regularThirdCircleFamily (regularSourceEquiv ((g₁ * g₂) ^ k) b) =
      A.regularThirdCircleFamily b := by
  ext z
  have h := DFunLike.congr_fun
    (regularPeriodCircleFamily_deck A.periods (Pi.single 2 1) ((g₁ * g₂) ^ k) b) (z 0)
  rw [← zpow_neg, rhoLambda_thirdBasis_peripheral_zpow] at h
  exact h

public theorem regularThirdCircleFamily_normalizedCuspEndpoint (A : PaperAnalyticData) :
    A.regularThirdCircleFamily
      (regularSourceEquiv (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
        (regularTotalSpaceBase A.periods A.actualCuspRegularRepresentative)) =
      A.actualCuspChosenThirdPeriodFamily 0 := by
  rw [← zpow_neg, A.regularThirdCircleFamily_peripheral]
  rw [← A.actualCuspChosenPositiveRegularBase_zero]
  rfl

public def normalizedThirdCircleWhisker (A : PaperAnalyticData) :
    Path (A.regularThirdCircleFamily A.sectionSevenAffineNormalizedMidpoint)
      (A.actualCuspChosenThirdPeriodFamily 0) :=
  (A.sectionSevenAffineNormalizedCuspPath.map A.regularThirdCircleFamily.continuous).cast rfl
    A.regularThirdCircleFamily_normalizedCuspEndpoint.symm

public theorem regularThirdCircleFamily_positivePath (A : PaperAnalyticData) (t : unitInterval) :
    A.regularThirdCircleFamily (A.normalizedCuspPositiveRegularPath t) =
      A.actualCuspChosenThirdPeriodFamily t := by
  change A.regularThirdCircleFamily
    (regularSourceEquiv (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
      (A.actualCuspChosenPositiveRegularBase t)) = _
  rw [← zpow_neg, A.regularThirdCircleFamily_peripheral]
  rfl

public theorem normalizedThirdPeriodLoop_eq_whisker (A : PaperAnalyticData) :
    A.normalizedThirdPeriodLoop A.normalizedWhiskeredCuspRegularPath =
      A.normalizedThirdCircleWhisker.trans
        (A.actualCuspChosenThirdPeriodLoop.trans A.normalizedThirdCircleWhisker.symm) := by
  apply Path.ext
  funext t
  simp only [normalizedThirdPeriodLoop, normalizedWhiskeredCuspRegularPath,
    normalizedThirdCircleWhisker, Path.cast_coe, Path.map_coe, Path.trans_apply,
    Path.symm_apply, Function.comp_apply]
  split_ifs
  · rfl
  · exact A.regularThirdCircleFamily_positivePath _
  · simpa using A.regularThirdCircleFamily_gZero (-1)
      (A.sectionSevenAffineNormalizedCuspPath (unitInterval.symm _))

public def actualCuspChosenThirdSweep_homotopy_normalizedMeridians (A : PaperAnalyticData) :
    (A.actualCuspChosenThirdSweepCentral.comp
      ((CircleProductIdentityMappingTorus.circleProductIdentityMappingTorusHomeomorph
        (X := StdTorus 1)).symm :
          C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)), UnitAddCircle × StdTorus 1))).Homotopy
      (identityMappingTorusMapOfLoop
        (A.normalizedThirdPeriodLoop A.normalizedMeridianPairRegularPath)) := by
  rw [← A.actualCuspChosenThirdSweepCentral_loop_realization]
  refine (identityMappingTorusMapOfLoop_whiskerHomotopy
    A.normalizedThirdCircleWhisker A.actualCuspChosenThirdPeriodLoop).symm.trans ?_
  rw [← A.normalizedThirdPeriodLoop_eq_whisker]
  exact identityMappingTorusMapOfLoop_homotopy A.normalizedThirdPeriodLoop_homotopic.some

end SphereSixComplex.Geometry.PaperAnalyticData
end
