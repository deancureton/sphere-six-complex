module
public import SphereSixComplex.Paper.Topology.CuspSweepAnchorHomotopy
public import SphereSixComplex.Paper.Topology.CuspCoordinateCircleTransport
public import SphereSixComplex.Paper.Topology.PaperGeometricCentralMonodromy

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open GlobalTorusFamily CuspPuncturedCollarBridge CuspRadialClutchingConstruction
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open ComplexTorus TorusFamily CuspPeriodExpansion
open SectionSevenEllipticTwoDiscCoverData

public def actualCuspChosenAnchor (A : PaperAnalyticData) :
    OpenRadialInterval A.starCuspWitness.localWitness.radius × ℝ :=
  (⟨‖cuspQ A.actualCuspBoundaryCoverBase.1.2‖,
    norm_cuspQ_pos _, A.actualCuspBoundaryCoverBase.2⟩, A.actualCuspBoundaryCoverBase.1.2.re)

public def actualCuspChosenThirdSweep (A : PaperAnalyticData) :
    C(UnitAddCircle × StdTorus 1, A.openEmbeddingStarData.collarSource 0) :=
  A.cuspFixedCircleSweepAnchors (cuspThirdFixedCircle (cuspBasePoint A.cuspCoordinate
    (markedCuspParameter A.starCuspWitness))) A.actualCuspChosenAnchor

public theorem cuspThirdSweep_homotopic_chosen (A : PaperAnalyticData) :
    (cuspThirdSweep A).Homotopic A.actualCuspChosenThirdSweep :=
  A.cuspFixedCircleSweep_homotopic_anchor _ _

private theorem cuspParameterOfPolar_norm_cuspQ_add (s : ℂ) (r : ℝ) :
    cuspParameterOfPolar ‖cuspQ s‖ (r + s.re) = s + r := by
  calc
    _ = cuspParameterOfPolar ‖cuspQ s‖ s.re + r := by
      simp only [cuspParameterOfPolar_eq, Complex.ofReal_add]
      ring
    _ = _ := by rw [cuspParameterOfPolar_norm_cuspQ]

public def actualCuspChosenPositiveCover (A : PaperAnalyticData) :
    C(ℝ, additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) := by
  refine ⟨fun r ↦ ⟨(0, A.actualCuspBoundaryCoverBase.1.2 + r), ?_⟩, ?_⟩
  · change ‖cuspQ (A.actualCuspBoundaryCoverBase.1.2 + r)‖ < _
    have h := A.actualCuspBoundaryCoverBase.2
    change ‖cuspQ A.actualCuspBoundaryCoverBase.1.2‖ < _ at h
    rw [norm_cuspQ] at h ⊢
    simpa using h
  · exact (continuous_const.prodMk (continuous_const.add Complex.continuous_ofReal)).subtype_mk _

public def actualCuspChosenPositiveRegularBase (A : PaperAnalyticData) :
    C(ℝ, RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
  ⟨fun r ↦ (additiveCuspBundleHomeomorph A.starCuspWitness (A.actualCuspChosenPositiveCover r)).1.1,
    continuous_fst.comp (continuous_subtype_val.comp
      ((additiveCuspBundleHomeomorph A.starCuspWitness).continuous.comp
        A.actualCuspChosenPositiveCover.continuous))⟩

public theorem actualCuspChosenThirdSweep_central_real (A : PaperAnalyticData)
    (r : ℝ) (t : UnitAddCircle) :
    A.starToCentral 0 (A.actualCuspChosenThirdSweep ((r : UnitAddCircle), fun _ ↦ t)) =
      regularPeriodCircleInGlobal A.periods (Pi.single 2 1)
        (t, A.actualCuspChosenPositiveRegularBase r) := by
  change A.starToCentral 0 (A.cuspFixedCircleSweepAnchors _ _ _) = _
  rw [cuspFixedCircleSweepAnchors_real]
  have hs := cuspParameterOfPolar_norm_cuspQ_add A.actualCuspBoundaryCoverBase.1.2 r
  change A.starToCentral 0 (actualCuspFullFibreSlice
    (cuspParameterOfPolar ‖cuspQ A.actualCuspBoundaryCoverBase.1.2‖
      (r + A.actualCuspBoundaryCoverBase.1.2.re)) _ _) = _
  erw [actualCuspFullFibreSlice_coordinateCircle_central A 2]
  apply congrArg (fun b ↦ regularPeriodCircleInGlobal A.periods (Pi.single 2 1) (t, b))
  apply Subtype.ext
  exact congrArg A.cuspCoordinate.lift hs

public theorem actualCuspChosenPositiveRegularBase_zero (A : PaperAnalyticData) :
    A.actualCuspChosenPositiveRegularBase 0 = regularTotalSpaceBase A.periods
      A.actualCuspRegularRepresentative := by
  apply Subtype.ext
  change A.cuspCoordinate.lift (A.actualCuspBoundaryCoverBase.1.2 + (0 : ℝ)) =
    A.cuspCoordinate.lift (A.actualCuspBoundaryCoverBase.1.2 - ((0 : unitInterval) : ℝ))
  simp

public theorem actualCuspChosenPositiveRegularBase_projects (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate (A.actualCuspChosenPositiveRegularBase t) =
      A.cuspAngularCoordinateLoop.symm t := by
  apply Subtype.ext
  rw [Path.symm_apply, Function.comp_apply, A.cuspAngularCoordinateLoop_apply]
  change A.modular.sourceCoordinate.coordinate
    (A.cuspCoordinate.lift (A.actualCuspBoundaryCoverBase.1.2 + (t : ℝ))) = _
  have he : A.actualCuspBoundaryCoverBase.1.2 - ((unitInterval.symm t : unitInterval) : ℝ) =
      (A.actualCuspBoundaryCoverBase.1.2 + (t : ℝ)) - 1 := by
    change A.actualCuspBoundaryCoverBase.1.2 - ((1 - (t : ℝ) : ℝ) : ℂ) = _
    simp only [Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [he]
  erw [A.cuspCoordinate.lift_shift _
    (additiveCuspRadiusCover_halfPlane A.starCuspWitness.localWitness.radius_le
      (A.actualCuspChosenPositiveCover t))]
  exact (A.modular.sourceCoordinate.coordinate_invariant g₀ _).symm

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
