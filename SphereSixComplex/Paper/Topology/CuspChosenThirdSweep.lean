module
public import SphereSixComplex.Paper.Topology.CuspSweepAnchorHomotopy
public import SphereSixComplex.Paper.Topology.CuspCoordinateCircleTransport

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

public def cuspChosenAnchor (A : PaperAnalyticData) :
    OpenRadialInterval A.starCuspWitness.localWitness.radius × ℝ :=
  (⟨‖cuspQ A.cuspBoundaryCoverBase.1.2‖,
    norm_cuspQ_pos _, A.cuspBoundaryCoverBase.2⟩, A.cuspBoundaryCoverBase.1.2.re)

public def cuspChosenThirdSweep (A : PaperAnalyticData) :
    C(UnitAddCircle × StdTorus 1, A.openEmbeddingStarData.collarSource 0) :=
  A.cuspFixedCircleSweepAnchors (cuspThirdFixedCircle (cuspBasePoint A.cuspCoordinate
    (markedCuspParameter A.starCuspWitness))) A.cuspChosenAnchor

public theorem cuspThirdSweep_homotopic_chosen (A : PaperAnalyticData) :
    (cuspThirdSweep A).Homotopic A.cuspChosenThirdSweep :=
  A.cuspFixedCircleSweep_homotopic_anchor _ _

private theorem cuspParameterOfPolar_norm_cuspQ_add (s : ℂ) (r : ℝ) :
    cuspParameterOfPolar ‖cuspQ s‖ (r + s.re) = s + r := by
  calc
    _ = cuspParameterOfPolar ‖cuspQ s‖ s.re + r := by
      simp only [cuspParameterOfPolar_eq, Complex.ofReal_add]
      ring
    _ = _ := by rw [cuspParameterOfPolar_norm_cuspQ]

public def cuspChosenPositiveCover (A : PaperAnalyticData) :
    C(ℝ, additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) := by
  refine ⟨fun r ↦ ⟨(0, A.cuspBoundaryCoverBase.1.2 + r), ?_⟩, ?_⟩
  · change ‖cuspQ (A.cuspBoundaryCoverBase.1.2 + r)‖ < _
    have h := A.cuspBoundaryCoverBase.2
    change ‖cuspQ A.cuspBoundaryCoverBase.1.2‖ < _ at h
    rw [norm_cuspQ] at h ⊢
    simpa using h
  · exact (continuous_const.prodMk (continuous_const.add Complex.continuous_ofReal)).subtype_mk _

public def cuspChosenPositiveRegularBase (A : PaperAnalyticData) :
    C(ℝ, RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
  ⟨fun r ↦ (additiveCuspBundleHomeomorph A.starCuspWitness (A.cuspChosenPositiveCover r)).1.1,
    continuous_fst.comp (continuous_subtype_val.comp
      ((additiveCuspBundleHomeomorph A.starCuspWitness).continuous.comp
        A.cuspChosenPositiveCover.continuous))⟩

public theorem cuspChosenThirdSweep_central_real (A : PaperAnalyticData)
    (r : ℝ) (t : UnitAddCircle) :
    A.starToCentral 0 (A.cuspChosenThirdSweep ((r : UnitAddCircle), fun _ ↦ t)) =
      regularPeriodCircleInGlobal A.periods (Pi.single 2 1)
        (t, A.cuspChosenPositiveRegularBase r) := by
  change A.starToCentral 0 (A.cuspFixedCircleSweepAnchors _ _ _) = _
  rw [cuspFixedCircleSweepAnchors_real]
  have hs := cuspParameterOfPolar_norm_cuspQ_add A.cuspBoundaryCoverBase.1.2 r
  change A.starToCentral 0 (actualCuspFullFiberSlice
    (cuspParameterOfPolar ‖cuspQ A.cuspBoundaryCoverBase.1.2‖
      (r + A.cuspBoundaryCoverBase.1.2.re)) _ _) = _
  erw [cuspFullFiberSlice_coordinateCircle_central A 2]
  apply congrArg (fun b ↦ regularPeriodCircleInGlobal A.periods (Pi.single 2 1) (t, b))
  apply Subtype.ext
  exact congrArg A.cuspCoordinate.lift hs

public theorem cuspChosenPositiveRegularBase_zero (A : PaperAnalyticData) :
    A.cuspChosenPositiveRegularBase 0 = regularTotalSpaceBase A.periods
      A.cuspRegularRepresentative := by
  apply Subtype.ext
  change A.cuspCoordinate.lift (A.cuspBoundaryCoverBase.1.2 + (0 : ℝ)) =
    A.cuspCoordinate.lift (A.cuspBoundaryCoverBase.1.2 - ((0 : unitInterval) : ℝ))
  simp

public theorem cuspChosenPositiveRegularBase_projects (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate (A.cuspChosenPositiveRegularBase t) =
      A.cuspAngularCoordinateLoop.symm t := by
  apply Subtype.ext
  rw [Path.symm_apply, Function.comp_apply, A.cuspAngularCoordinateLoop_apply]
  change A.modular.sourceCoordinate.coordinate
    (A.cuspCoordinate.lift (A.cuspBoundaryCoverBase.1.2 + (t : ℝ))) = _
  have he : A.cuspBoundaryCoverBase.1.2 - ((unitInterval.symm t : unitInterval) : ℝ) =
      (A.cuspBoundaryCoverBase.1.2 + (t : ℝ)) - 1 := by
    change A.cuspBoundaryCoverBase.1.2 - ((1 - (t : ℝ) : ℝ) : ℂ) = _
    simp only [Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [he]
  erw [A.cuspCoordinate.lift_shift _
    (additiveCuspRadiusCover_halfPlane A.starCuspWitness.localWitness.radius_le
      (A.cuspChosenPositiveCover t))]
  exact (A.modular.sourceCoordinate.coordinate_invariant g₀ _).symm

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
