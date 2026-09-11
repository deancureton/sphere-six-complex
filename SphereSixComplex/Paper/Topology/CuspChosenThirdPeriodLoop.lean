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

public theorem cuspChosenPositiveRegularBase_one (A : PaperAnalyticData) :
    A.cuspChosenPositiveRegularBase 1 =
      regularSourceEquiv g₀⁻¹ (A.cuspChosenPositiveRegularBase 0) := by
  let _ := regularSourceMulAction A.paperTriangleUniformization
  have h : regularSourceEquiv g₀ (A.cuspChosenPositiveRegularBase 1) =
      A.cuspChosenPositiveRegularBase 0 := by
    apply Subtype.ext
    have hs := A.cuspCoordinate.lift_shift _
      (additiveCuspRadiusCover_halfPlane A.starCuspWitness.localWitness.radius_le
        (A.cuspChosenPositiveCover 1))
    change A.paperTriangleUniformization.sourceAction g₀
      (A.cuspCoordinate.lift (A.cuspBoundaryCoverBase.1.2 + (1 : ℝ))) =
        A.cuspCoordinate.lift (A.cuspBoundaryCoverBase.1.2 + (0 : ℝ))
    simpa [cuspChosenPositiveCover] using hs.symm
  calc
    _ = regularSourceEquiv g₀⁻¹
        (regularSourceEquiv g₀ (A.cuspChosenPositiveRegularBase 1)) :=
      (inv_smul_smul g₀ (A.cuspChosenPositiveRegularBase 1)).symm
    _ = _ := congrArg (regularSourceEquiv g₀⁻¹) h


public def cuspChosenThirdPeriodFamily (A : PaperAnalyticData) :
    C(ℝ, C(StdTorus 1, A.CentralFamily)) :=
  ((regularPeriodCircleInGlobal A.periods (Pi.single 2 1)).comp
    ⟨fun p : ℝ × StdTorus 1 ↦ (p.2 0, A.cuspChosenPositiveRegularBase p.1),
      (continuous_apply 0 |>.comp continuous_snd).prodMk
        (A.cuspChosenPositiveRegularBase.continuous.comp continuous_fst)⟩).curry

public theorem cuspChosenThirdPeriodFamily_eq_sweep (A : PaperAnalyticData)
    (r : ℝ) (z : StdTorus 1) :
    A.cuspChosenThirdPeriodFamily r z =
      A.starToCentral 0 (A.cuspChosenThirdSweep ((r : UnitAddCircle), z)) := by
  have hz : z = fun _ ↦ z 0 := by ext i; fin_cases i; rfl
  rw [hz]
  exact (cuspChosenThirdSweep_central_real A r (z 0)).symm

public theorem cuspChosenThirdPeriodFamily_one (A : PaperAnalyticData) :
    A.cuspChosenThirdPeriodFamily 1 = A.cuspChosenThirdPeriodFamily 0 := by
  ext z
  rw [cuspChosenThirdPeriodFamily_eq_sweep, cuspChosenThirdPeriodFamily_eq_sweep,
    AddCircle.coe_period, AddCircle.coe_zero]

public def cuspChosenThirdPeriodLoop (A : PaperAnalyticData) :
    Path (A.cuspChosenThirdPeriodFamily 0) (A.cuspChosenThirdPeriodFamily 0) where
  toFun t := A.cuspChosenThirdPeriodFamily (t : ℝ)
  continuous_toFun := A.cuspChosenThirdPeriodFamily.continuous.comp continuous_subtype_val
  source' := rfl
  target' := A.cuspChosenThirdPeriodFamily_one

public def cuspChosenThirdSweepCentral (A : PaperAnalyticData) :
    C(UnitAddCircle × StdTorus 1, A.CentralFamily) :=
  ⟨fun p ↦ A.starToCentral 0 (A.cuspChosenThirdSweep p),
    (A.starToCentral_isOpenEmbedding 0).continuous.comp A.cuspChosenThirdSweep.continuous⟩

public theorem cuspChosenThirdSweepCentral_loop_realization (A : PaperAnalyticData) :
    identityMappingTorusMapOfLoop A.cuspChosenThirdPeriodLoop =
      A.cuspChosenThirdSweepCentral.comp
        ((circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1)).symm :
          C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)), UnitAddCircle × StdTorus 1)) := by
  ext z
  induction z using Quotient.inductionOn with
  | _ z =>
    obtain ⟨u, t, x⟩ := z
    cases u
    change A.cuspChosenThirdPeriodLoop t x =
      A.cuspChosenThirdSweepCentral (circleProductIdentityMappingTorusHomeomorph.symm
        (torusPt (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) () t x))
    rw [circleProductIdentityMappingTorusHomeomorph_symm_interval]
    exact A.cuspChosenThirdPeriodFamily_eq_sweep t x

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
