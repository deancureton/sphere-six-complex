module
public import SphereSixComplex.Paper.Topology.CuspNormalizedRegularPaths
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex SphereSixComplex.Topology GlobalTorusFamily TriangleGroup

public theorem cuspPositiveWhisker_class (A : PaperAnalyticData) :
    Path.Homotopic.Quotient.mk
      (A.cuspMarkedCentralWhisker.trans
        (A.cuspAngularCentralLoop.symm.trans
          A.cuspMarkedCentralWhisker.symm)) =
      A.markedOneCentralMeridianClass * A.markedZeroCentralMeridianClass := by
  have h := congrArg (fun x : FundamentalGroup A.CentralFamily
    (A.centralZeroSection A.markedPuncturedBasepoint) => x⁻¹)
      A.cuspMarkedCentralLoop_class_eq_finiteProduct
  rw [mul_inv_rev, inv_inv, inv_inv] at h
  rw [← h]
  unfold cuspMarkedCentralLoop
  simp only [FundamentalGroup.inv_def, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, homotopicQuotient_symm_trans,
    homotopicQuotient_symm_symm, Path.Homotopic.Quotient.trans_assoc]

public theorem centralFamilyCoordinate_markedZero (A : PaperAnalyticData) :
    FundamentalGroup.mapOfEq
      ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
      A.affineMarkedCentralCoordinate_base A.markedZeroCentralMeridianClass =
        Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridian := by
  rw [A.markedZeroCentralMeridianClass_eq_pathLoopClass, FundamentalGroup.mapOfEq_apply]
  unfold markedZeroCentralMeridian markedZeroBaseMeridian
  rw [← Path.Homotopic.Quotient.mk_map]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  rw [Path.cast_coe]
  change A.centralFamilyCoordinate
    (A.centralZeroSection
      (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
        (twicePuncturedClockwiseZeroMeridian t))) = _
  rw [A.centralFamilyCoordinate_zeroSection]
  exact A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply _

public theorem centralFamilyCoordinate_markedOne (A : PaperAnalyticData) :
    FundamentalGroup.mapOfEq
      ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
      A.affineMarkedCentralCoordinate_base A.markedOneCentralMeridianClass =
        Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridian := by
  rw [A.markedOneCentralMeridianClass_eq_pathLoopClass, FundamentalGroup.mapOfEq_apply]
  unfold markedOneCentralMeridian markedOneBaseMeridian
  rw [← Path.Homotopic.Quotient.mk_map]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  rw [Path.cast_coe]
  change A.centralFamilyCoordinate
    (A.centralZeroSection
      (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
        (twicePuncturedClockwiseOneMeridian t))) = _
  rw [A.centralFamilyCoordinate_zeroSection]
  exact A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply _

public theorem cuspPositiveWhisker_coordinate_homotopy (A : PaperAnalyticData) :
    (((A.cuspMarkedCentralWhisker.trans
      (A.cuspAngularCentralLoop.symm.trans A.cuspMarkedCentralWhisker.symm)).map
        A.centralFamilyCoordinate_continuous).cast
          A.affineMarkedCentralCoordinate_base.symm
          A.affineMarkedCentralCoordinate_base.symm).Homotopic
      (twicePuncturedClockwiseZeroMeridian.trans twicePuncturedClockwiseOneMeridian) := by
  have h := congrArg
    (FundamentalGroup.mapOfEq
      ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
      A.affineMarkedCentralCoordinate_base) A.cuspPositiveWhisker_class
  rw [map_mul, A.centralFamilyCoordinate_markedOne, A.centralFamilyCoordinate_markedZero,
    FundamentalGroup.mul_def, ← Path.Homotopic.Quotient.mk_trans] at h
  apply Path.Homotopic.Quotient.eq.mp
  rw [FundamentalGroup.mapOfEq_apply] at h
  exact h

public theorem regularCoordinate_sourceEquiv (A : PaperAnalyticData) (g : Delta)
    (b : RegularBase (U := A.paperTriangleUniformization)) :
    A.regularCoordinate (regularSourceEquiv g b) = A.regularCoordinate b :=
  A.regularCoordinate_deck_invariant g b

public theorem normalizedWhiskeredCuspRegularPath_projects (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate (A.normalizedWhiskeredCuspRegularPath t) =
      A.centralFamilyCoordinate
        ((A.cuspMarkedCentralWhisker.trans
          (A.cuspAngularCentralLoop.symm.trans
            A.cuspMarkedCentralWhisker.symm)) t) := by
  simp only [normalizedWhiskeredCuspRegularPath, Path.trans_apply, Path.map_coe,
    Path.symm_apply, Function.comp_apply]
  split_ifs <;>
    simp only [A.affineNormalizedCuspPath_projects,
      A.normalizedCuspPositiveRegularPath_projects, A.regularCoordinate_sourceEquiv,
      cuspAngularCoordinateLoop, Path.symm_apply, Path.map_coe, Function.comp_apply]

public theorem normalizedMeridianPairRegularPath_projects (A : PaperAnalyticData)
    (t : unitInterval) :
    A.regularCoordinate (A.normalizedMeridianPairRegularPath t) =
      (twicePuncturedClockwiseZeroMeridian.trans twicePuncturedClockwiseOneMeridian) t := by
  simp only [normalizedMeridianPairRegularPath, Path.cast_coe, Path.trans_apply,
    Path.map_coe, Function.comp_apply]
  split_ifs <;>
    simp only [A.affineNormalizedZeroLift_projects,
      A.affineNormalizedOneLift_projects, A.regularCoordinate_sourceEquiv]

public theorem normalizedWhiskeredCuspRegularPath_homotopic_meridianPair
    (A : PaperAnalyticData) :
    A.normalizedWhiskeredCuspRegularPath.Homotopic A.normalizedMeridianPairRegularPath := by
  apply (A.regularCoordinate_isCoveringMap.homotopicRel_iff_comp
    (f₀ := A.normalizedWhiskeredCuspRegularPath.toContinuousMap)
    (f₁ := A.normalizedMeridianPairRegularPath.toContinuousMap) (S := {0, 1})
    ⟨0, Or.inl rfl, A.normalizedWhiskeredCuspRegularPath.source.trans
      A.normalizedMeridianPairRegularPath.source.symm⟩).mpr
  have h := A.cuspPositiveWhisker_coordinate_homotopy
  change ContinuousMap.HomotopicRel
    ((A.cuspMarkedCentralWhisker.trans
      (A.cuspAngularCentralLoop.symm.trans A.cuspMarkedCentralWhisker.symm)).map
        A.centralFamilyCoordinate_continuous).toContinuousMap
    (twicePuncturedClockwiseZeroMeridian.trans twicePuncturedClockwiseOneMeridian).toContinuousMap
    {0, 1} at h
  convert h using 1
  · ext t
    exact congrArg Subtype.val (A.normalizedWhiskeredCuspRegularPath_projects t)
  · ext t
    exact congrArg Subtype.val (A.normalizedMeridianPairRegularPath_projects t)

end SphereSixComplex.Geometry.PaperAnalyticData
end
