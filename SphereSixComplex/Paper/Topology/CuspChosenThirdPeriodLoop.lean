module
public import SphereSixComplex.Paper.Topology.CuspChosenThirdSweep
public import SphereSixComplex.Paper.Topology.CuspThirdSweepLoopRealization

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open GlobalTorusFamily CuspPuncturedCollarBridge CuspRadialClutchingConstruction
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open ComplexTorus TorusFamily CuspPeriodExpansion
open CircleProductIdentityMappingTorus
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness

public theorem actualCuspChosenPositiveRegularBase_one (A : PaperAnalyticData) :
    A.actualCuspChosenPositiveRegularBase 1 =
      regularSourceEquiv g₀⁻¹ (A.actualCuspChosenPositiveRegularBase 0) := by
  let _ := regularSourceMulAction A.paperTriangleUniformization
  have h : regularSourceEquiv g₀ (A.actualCuspChosenPositiveRegularBase 1) =
      A.actualCuspChosenPositiveRegularBase 0 := by
    apply Subtype.ext
    have hs := A.cuspCoordinate.lift_shift _
      (additiveCuspRadiusCover_halfPlane A.starCuspWitness.localWitness.radius_le
        (A.actualCuspChosenPositiveCover 1))
    change A.paperTriangleUniformization.sourceAction g₀
      (A.cuspCoordinate.lift (A.actualCuspBoundaryCoverBase.1.2 + (1 : ℝ))) =
        A.cuspCoordinate.lift (A.actualCuspBoundaryCoverBase.1.2 + (0 : ℝ))
    simpa [actualCuspChosenPositiveCover] using hs.symm
  calc
    _ = regularSourceEquiv g₀⁻¹
        (regularSourceEquiv g₀ (A.actualCuspChosenPositiveRegularBase 1)) :=
      (inv_smul_smul g₀ (A.actualCuspChosenPositiveRegularBase 1)).symm
    _ = _ := congrArg (regularSourceEquiv g₀⁻¹) h

public def actualCuspChosenPositiveRegularPath (A : PaperAnalyticData) :
    Path (A.actualCuspChosenPositiveRegularBase 0)
      (regularSourceEquiv g₀⁻¹ (A.actualCuspChosenPositiveRegularBase 0)) where
  toFun t := A.actualCuspChosenPositiveRegularBase (t : ℝ)
  continuous_toFun := A.actualCuspChosenPositiveRegularBase.continuous.comp continuous_subtype_val
  source' := rfl
  target' := A.actualCuspChosenPositiveRegularBase_one

public def actualCuspChosenThirdPeriodFamily (A : PaperAnalyticData) :
    C(ℝ, C(StdTorus 1, A.CentralFamily)) :=
  ((regularPeriodCircleInGlobal A.periods (Pi.single 2 1)).comp
    ⟨fun p : ℝ × StdTorus 1 ↦ (p.2 0, A.actualCuspChosenPositiveRegularBase p.1),
      (continuous_apply 0 |>.comp continuous_snd).prodMk
        (A.actualCuspChosenPositiveRegularBase.continuous.comp continuous_fst)⟩).curry

public theorem actualCuspChosenThirdPeriodFamily_eq_sweep (A : PaperAnalyticData)
    (r : ℝ) (z : StdTorus 1) :
    A.actualCuspChosenThirdPeriodFamily r z =
      A.starToCentral 0 (A.actualCuspChosenThirdSweep ((r : UnitAddCircle), z)) := by
  have hz : z = fun _ ↦ z 0 := by ext i; fin_cases i; rfl
  rw [hz]
  exact (actualCuspChosenThirdSweep_central_real A r (z 0)).symm

public theorem actualCuspChosenThirdPeriodFamily_one (A : PaperAnalyticData) :
    A.actualCuspChosenThirdPeriodFamily 1 = A.actualCuspChosenThirdPeriodFamily 0 := by
  ext z
  rw [actualCuspChosenThirdPeriodFamily_eq_sweep, actualCuspChosenThirdPeriodFamily_eq_sweep,
    AddCircle.coe_period, AddCircle.coe_zero]

public def actualCuspChosenThirdPeriodLoop (A : PaperAnalyticData) :
    Path (A.actualCuspChosenThirdPeriodFamily 0) (A.actualCuspChosenThirdPeriodFamily 0) where
  toFun t := A.actualCuspChosenThirdPeriodFamily (t : ℝ)
  continuous_toFun := A.actualCuspChosenThirdPeriodFamily.continuous.comp continuous_subtype_val
  source' := rfl
  target' := A.actualCuspChosenThirdPeriodFamily_one

public def actualCuspChosenThirdSweepCentral (A : PaperAnalyticData) :
    C(UnitAddCircle × StdTorus 1, A.CentralFamily) :=
  ⟨fun p ↦ A.starToCentral 0 (A.actualCuspChosenThirdSweep p),
    (A.starToCentral_isOpenEmbedding 0).continuous.comp A.actualCuspChosenThirdSweep.continuous⟩

public theorem actualCuspChosenThirdSweepCentral_loop_realization (A : PaperAnalyticData) :
    identityMappingTorusMapOfLoop A.actualCuspChosenThirdPeriodLoop =
      A.actualCuspChosenThirdSweepCentral.comp
        ((circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1)).symm :
          C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)), UnitAddCircle × StdTorus 1)) := by
  ext z
  induction z using Quotient.inductionOn with
  | _ z =>
    obtain ⟨u, t, x⟩ := z
    cases u
    change A.actualCuspChosenThirdPeriodLoop t x =
      A.actualCuspChosenThirdSweepCentral (circleProductIdentityMappingTorusHomeomorph.symm
        (torusPt (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) () t x))
    rw [circleProductIdentityMappingTorusHomeomorph_symm_interval]
    exact A.actualCuspChosenThirdPeriodFamily_eq_sweep t x

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
