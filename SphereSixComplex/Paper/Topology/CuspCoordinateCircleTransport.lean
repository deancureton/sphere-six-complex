module
public import SphereSixComplex.Paper.Topology.CuspThirdSweep
public import SphereSixComplex.Paper.Topology.RegularPeriodCircleTransport

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open GlobalTorusFamily CuspPuncturedCollarBridge CuspRadialClutchingConstruction
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open ComplexTorus TorusFamily CuspPeriodExpansion
open EllipticTwoDiscCoverData

public theorem cuspFullFibreSlice_coordinateCircle_real (A : PaperAnalyticData)
    (i : Fin 4) (s : ℂ) (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius) (t : ℝ) :
    actualCuspFullFibreSlice (A := A) s hs
      (cuspCoordinateCircle (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness)) i (fun _ ↦ (t : UnitAddCircle))) =
    additiveCuspBoundaryProjection A.starCuspWitness
      ⟨(t • periodVector (cuspBasePoint A.cuspCoordinate s).1 (Pi.single i 1), s), hs⟩ := by
  rw [cuspCoordinateCircle_real]
  have h : collarFiberEquiv A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness) s
      (t • periodVector (cuspBasePoint A.cuspCoordinate s).1 (Pi.single i 1)) =
      t • periodVector (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness)).1 (Pi.single i 1) := by
    rw [collarFiberEquiv_apply]
    change (fullRankDomain _).realEquiv ((fullRankDomain _).realEquiv.symm
      (t • periodVector _ (Pi.single i 1))) = _
    rw [map_smul, realEquiv_symm_periodVector, map_smul,
      (fullRankDomain _).map_integer]
  rw [← h]
  exact actualCuspFullFibreSlice_additiveTorusProjection s hs _

public theorem cuspFullFibreSlice_coordinateCircle_central (A : PaperAnalyticData)
    (i : Fin 4) (s : ℂ) (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius)
    (t : UnitAddCircle) :
    A.starToCentral 0
      (actualCuspFullFibreSlice (A := A) s hs
        (cuspCoordinateCircle (cuspBasePoint A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness)) i (fun _ ↦ t))) =
    regularPeriodCircleInGlobal A.periods (Pi.single i 1)
      (t, (additiveCuspBundleHomeomorph A.starCuspWitness ⟨(0, s), hs⟩).1.1) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [cuspFullFibreSlice_coordinateCircle_real]
  trans additiveCuspCoverToGlobal A.starCuspWitness
    ⟨(r • periodVector (cuspBasePoint A.cuspCoordinate s).1 (Pi.single i 1), s), hs⟩
  · exact puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection A.starCuspWitness _
  rw [additiveCuspCoverToGlobal_eq_quotientProjections]
  change _ = A.centralQuotientProjection (regularPeriodCircle A.periods (Pi.single i 1) _)
  rw [regularPeriodCircle_real]
  rfl

public def cuspPolarZeroCover (A : PaperAnalyticData) :
    C(ℝ, additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) := by
  let rho : OpenRadialInterval A.starCuspWitness.localWitness.radius :=
    ⟨A.starCuspWitness.localWitness.radius / 2, by
      have := A.starCuspWitness.localWitness.radius_pos
      constructor <;> linarith⟩
  refine ⟨fun r ↦ ⟨(0, cuspParameterOfPolar rho.1 r), ?_⟩, ?_⟩
  · change ‖cuspQ (cuspParameterOfPolar rho.1 r)‖ < _
    rw [norm_cuspQ_cuspParameterOfPolar _ _ rho.2.1]
    exact rho.2.2
  · exact (continuous_const.prodMk
      (continuous_cuspParameterOfPolar.comp (continuous_const.prodMk continuous_id))).subtype_mk _

public def cuspPolarRegularBase (A : PaperAnalyticData) :
    C(ℝ, RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
  ⟨fun r ↦ (additiveCuspBundleHomeomorph A.starCuspWitness (A.cuspPolarZeroCover r)).1.1,
    continuous_fst.comp (continuous_subtype_val.comp
      ((additiveCuspBundleHomeomorph A.starCuspWitness).continuous.comp
        A.cuspPolarZeroCover.continuous))⟩

public theorem cuspThirdSweep_central_real (A : PaperAnalyticData)
    (r : ℝ) (t : UnitAddCircle) :
    A.starToCentral 0 (cuspThirdSweep A ((r : UnitAddCircle), fun _ ↦ t)) =
      regularPeriodCircleInGlobal A.periods (Pi.single 2 1)
        (t, A.cuspPolarRegularBase r) := by
  change A.starToCentral 0 (cuspFixedCircleSweep A _ _) = _
  rw [cuspFixedCircleSweep_real]
  exact cuspFullFibreSlice_coordinateCircle_central A 2 _ _ t

public def cuspThirdPeriodFamily (A : PaperAnalyticData) :
    C(ℝ, C(StdTorus 1, A.CentralFamily)) :=
  ((regularPeriodCircleInGlobal A.periods (Pi.single 2 1)).comp
    ⟨fun p : ℝ × StdTorus 1 ↦ (p.2 0, A.cuspPolarRegularBase p.1),
      (continuous_apply 0 |>.comp continuous_snd).prodMk
        (A.cuspPolarRegularBase.continuous.comp continuous_fst)⟩).curry

public theorem cuspThirdPeriodFamily_eq_sweep (A : PaperAnalyticData)
    (r : ℝ) (z : StdTorus 1) :
    A.cuspThirdPeriodFamily r z =
      A.starToCentral 0 (cuspThirdSweep A ((r : UnitAddCircle), z)) := by
  have hz : z = fun _ ↦ z 0 := by ext i; fin_cases i; rfl
  rw [hz]
  exact (cuspThirdSweep_central_real A r (z 0)).symm

public theorem cuspThirdPeriodFamily_one (A : PaperAnalyticData) :
    A.cuspThirdPeriodFamily 1 = A.cuspThirdPeriodFamily 0 := by
  ext z
  rw [cuspThirdPeriodFamily_eq_sweep, cuspThirdPeriodFamily_eq_sweep,
    AddCircle.coe_period, AddCircle.coe_zero]

public def cuspThirdPeriodLoop (A : PaperAnalyticData) :
    Path (A.cuspThirdPeriodFamily 0) (A.cuspThirdPeriodFamily 0) where
  toFun t := A.cuspThirdPeriodFamily (t : ℝ)
  continuous_toFun := A.cuspThirdPeriodFamily.continuous.comp continuous_subtype_val
  source' := rfl
  target' := A.cuspThirdPeriodFamily_one

public theorem cuspThirdPeriodLoop_apply (A : PaperAnalyticData)
    (t : unitInterval) (z : StdTorus 1) :
    A.cuspThirdPeriodLoop t z =
      regularPeriodCircleInGlobal A.periods (Pi.single 2 1)
        (z 0, A.cuspPolarRegularBase t) := rfl

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
