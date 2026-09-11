module
public import SphereSixComplex.Paper.Topology.CuspChosenThirdPeriodLoop
public import SphereSixComplex.Paper.Topology.CuspThirdPeripheralInvariance

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology GlobalTorusFamily TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness

public theorem regularSourceEquiv_continuous (A : PaperAnalyticData) (g : Delta) :
    Continuous (regularSourceEquiv (U := A.paperTriangleUniformization) g) := by
  let _ := A.regularBaseDeckAction
  let _ := A.regularBaseDeckAction_continuous
  exact continuous_const_smul g

public theorem cuspPeripheral_inverse_commute (A : PaperAnalyticData) :
    Commute (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹) g₀⁻¹ := by
  have hg : g₀⁻¹ = g₁ * g₂ := (eq_inv_of_mul_eq_one_left g₁_mul_g₂_mul_g₀).symm
  rw [hg]
  exact ((Commute.refl (g₁ * g₂)).zpow_left A.geometricCentralCuspConjugatorExponent).inv_left

public def normalizedCuspPositiveRegularPath (A : PaperAnalyticData) :
    Path (regularSourceEquiv (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
      (regularTotalSpaceBase A.periods A.cuspRegularRepresentative))
      (regularSourceEquiv g₀⁻¹
        (regularSourceEquiv (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
          (regularTotalSpaceBase A.periods A.cuspRegularRepresentative))) where
  toFun t := regularSourceEquiv (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
    (A.cuspChosenPositiveRegularBase (t : ℝ))
  continuous_toFun := (regularSourceEquiv_continuous A _).comp
    (A.cuspChosenPositiveRegularBase.continuous.comp continuous_subtype_val)
  source' := congrArg (regularSourceEquiv _ ) A.cuspChosenPositiveRegularBase_zero
  target' := by
    let _ := regularSourceMulAction A.paperTriangleUniformization
    simp only [show ((1 : unitInterval) : ℝ) = 1 from rfl]
    rw [A.cuspChosenPositiveRegularBase_one, A.cuspChosenPositiveRegularBase_zero]
    change (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹) •
      (g₀⁻¹ • (regularTotalSpaceBase A.periods A.cuspRegularRepresentative)) =
        g₀⁻¹ • ((((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹) •
          (regularTotalSpaceBase A.periods A.cuspRegularRepresentative))
    rw [← mul_smul, (cuspPeripheral_inverse_commute A).eq, mul_smul]

public def normalizedWhiskeredCuspRegularPath (A : PaperAnalyticData) :
    Path A.affineNormalizedMidpoint
      (regularSourceEquiv g₀⁻¹ A.affineNormalizedMidpoint) :=
  A.affineNormalizedCuspPath.trans
    (A.normalizedCuspPositiveRegularPath.trans
      (A.affineNormalizedCuspPath.symm.map (regularSourceEquiv_continuous A g₀⁻¹)))

public def normalizedMeridianPairRegularPath (A : PaperAnalyticData) :
    Path A.affineNormalizedMidpoint
      (regularSourceEquiv g₀⁻¹ A.affineNormalizedMidpoint) := by
  let _ := regularSourceMulAction A.paperTriangleUniformization
  let p := A.affineNormalizedZeroLift.trans
    (A.affineNormalizedOneLift.map (regularSourceEquiv_continuous A g₁))
  refine p.cast rfl ?_
  change g₀⁻¹ • A.affineNormalizedMidpoint =
    g₁ • (g₂ • A.affineNormalizedMidpoint)
  rw [← mul_smul, eq_inv_of_mul_eq_one_left g₁_mul_g₂_mul_g₀]

public theorem normalizedCuspPositiveRegularPath_projects (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate (A.normalizedCuspPositiveRegularPath t) =
      A.cuspAngularCoordinateLoop.symm t := by
  change A.regularCoordinate
    (SphereSixComplex.Geometry.EquivariantQuotientHomeomorph.actionMap A.regularBaseDeckAction _
      (A.cuspChosenPositiveRegularBase t)) = _
  rw [A.regularCoordinate_deck_invariant]
  exact A.cuspChosenPositiveRegularBase_projects t

end SphereSixComplex.Geometry.PaperAnalyticData
end
