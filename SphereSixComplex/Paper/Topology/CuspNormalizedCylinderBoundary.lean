module
public import SphereSixComplex.Paper.Topology.CuspNormalizedPeriodLoops
public import SphereSixComplex.Paper.Topology.MarkedMeridianCircleCylinders

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory TopologicalSpace
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex SphereSixComplex.Topology GlobalTorusFamily TriangleGroup
open SphereSixComplex.StandardTorusHomology
open EllipticTwoDiscHomologyCoordinates

public def normalizedThirdOverlapCircle {A : PaperAnalyticData}
    (R : A.AffineRadialCompletionInput)
    (b : RegularBase (U := A.paperTriangleUniformization))
    (hb : A.regularCoordinate b = twicePuncturedComplexBasepoint) :
    C(StdTorus 1, (Opens.toTopCat (TopCat.of A.ellipticInterior)).obj
      (orderThreeOpen R.twoDiscCover ⊓ orderFourOpen R.twoDiscCover)) := by
  refine ⟨fun z ↦ ⟨A.regularPeriodCircleToInterior (Pi.single 2 1)
    (z 0, b), ?_, ?_⟩, ?_⟩
  · apply regularPeriodCircleToInterior_mem_three R
    change (A.regularCoordinate (b)).1.re < _
    rw [hb]
    norm_num [twicePuncturedComplexBasepoint]
  · apply regularPeriodCircleToInterior_mem_four R
    change _ < (A.regularCoordinate (b)).1.re
    rw [hb]
    norm_num [twicePuncturedComplexBasepoint]
  · exact ((A.regularPeriodCircleToInterior (Pi.single 2 1)).continuous.comp
      ((continuous_apply 0).prodMk continuous_const)).subtype_mk _

public def normalizedThirdZeroCirclePath (A : PaperAnalyticData) :
    Path (A.centralToEllipticInterior.comp
      (A.regularThirdCircleFamily A.affineNormalizedMidpoint))
      (A.centralToEllipticInterior.comp
        (A.regularThirdCircleFamily (regularSourceEquiv g₁ A.affineNormalizedMidpoint))) :=
  (A.affineNormalizedZeroLift.map A.regularThirdCircleFamily.continuous).map
    (ContinuousMap.continuous_postcomp A.centralToEllipticInterior)

public def normalizedThirdOneCirclePath (A : PaperAnalyticData) :
    Path (A.centralToEllipticInterior.comp
      (A.regularThirdCircleFamily (regularSourceEquiv g₁ A.affineNormalizedMidpoint)))
      (A.centralToEllipticInterior.comp
        (A.regularThirdCircleFamily A.affineNormalizedMidpoint)) := by
  let p := ((A.affineNormalizedOneLift.map
    (A.regularSourceEquiv_continuous g₁)).map A.regularThirdCircleFamily.continuous).map
      (ContinuousMap.continuous_postcomp A.centralToEllipticInterior)
  refine p.cast rfl ?_
  apply congrArg (fun c ↦ A.centralToEllipticInterior.comp c)
  have he : regularSourceEquiv g₁ (regularSourceEquiv g₂ A.affineNormalizedMidpoint) =
      regularSourceEquiv g₀⁻¹ A.affineNormalizedMidpoint :=
    by
      let _ := SphereSixComplex.TriangleGroup.FuchsianProperFreeness.regularSourceMulAction
        A.paperTriangleUniformization
      change g₁ • (g₂ • A.affineNormalizedMidpoint) =
        g₀⁻¹ • A.affineNormalizedMidpoint
      rw [← mul_smul, eq_inv_of_mul_eq_one_left g₁_mul_g₂_mul_g₀]
  rw [he]
  simpa using (A.regularThirdCircleFamily_gZero (-1) A.affineNormalizedMidpoint).symm

public theorem normalizedThirdZeroCirclePath_mem_three {A : PaperAnalyticData}
    (R : A.AffineRadialCompletionInput) (t : unitInterval) (z : StdTorus 1) :
    A.normalizedThirdZeroCirclePath t z ∈ R.twoDiscCover.orderThreeSide := by
  apply regularPeriodCircleToInterior_mem_three R
  change (A.regularCoordinate (A.affineNormalizedZeroLift t)).1.re < _
  rw [A.affineNormalizedZeroLift_projects]
  exact twicePuncturedClockwiseZeroPoint_mem_left t

public theorem normalizedThirdOneCirclePath_mem_four {A : PaperAnalyticData}
    (R : A.AffineRadialCompletionInput) (t : unitInterval) (z : StdTorus 1) :
    A.normalizedThirdOneCirclePath t z ∈ R.twoDiscCover.orderFourSide := by
  apply regularPeriodCircleToInterior_mem_four R
  change _ < (A.regularCoordinate
    (regularSourceEquiv g₁ (A.affineNormalizedOneLift t))).1.re
  rw [A.regularCoordinate_sourceEquiv, A.affineNormalizedOneLift_projects]
  exact twicePuncturedClockwiseOnePoint_mem_right t

public theorem normalizedThirdMeridianCylinder_boundary {A : PaperAnalyticData}
    (R : A.AffineRadialCompletionInput)
    (x : IntegralSingularHomology 2 (CircleMappingTorus (Homeomorph.refl (StdTorus 1)))) :
    ConcreteCategory.hom ((BinaryOpenCover.openCoverHomologyComparisonOfCover
      (ellipticOpenCover R.twoDiscCover)).boundary 1)
      (integralSingularHomologyMap 2
        (identityMappingTorusMapOfLoop
          (A.normalizedThirdZeroCirclePath.trans A.normalizedThirdOneCirclePath)) x) =
    integralSingularHomologyMap 1
      (normalizedThirdOverlapCircle R (regularSourceEquiv g₁ A.affineNormalizedMidpoint)
        ((A.regularCoordinate_sourceEquiv g₁ _).trans A.affineNormalizedMidpoint_projects))
      ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl (StdTorus 1)) 1).boundary x) -
    integralSingularHomologyMap 1
      (normalizedThirdOverlapCircle R A.affineNormalizedMidpoint
        A.affineNormalizedMidpoint_projects)
      ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl (StdTorus 1)) 1).boundary x) := by
  exact twoSideCircleLoop_boundary (orderThreeOpen R.twoDiscCover) (orderFourOpen R.twoDiscCover)
    (ellipticOpenCover R.twoDiscCover)
    (normalizedThirdOverlapCircle R A.affineNormalizedMidpoint
      A.affineNormalizedMidpoint_projects)
    (normalizedThirdOverlapCircle R (regularSourceEquiv g₁ A.affineNormalizedMidpoint)
      ((A.regularCoordinate_sourceEquiv g₁ _).trans A.affineNormalizedMidpoint_projects))
    A.normalizedThirdZeroCirclePath A.normalizedThirdOneCirclePath
    (normalizedThirdZeroCirclePath_mem_three R) (normalizedThirdOneCirclePath_mem_four R) 1 x

public theorem normalizedThirdMeridianCircleLoop_eq (A : PaperAnalyticData) :
    A.normalizedThirdZeroCirclePath.trans A.normalizedThirdOneCirclePath =
      (A.normalizedThirdPeriodLoop A.normalizedMeridianPairRegularPath).map
        (ContinuousMap.continuous_postcomp A.centralToEllipticInterior) := by
  apply Path.ext
  funext t
  simp only [normalizedThirdZeroCirclePath, normalizedThirdOneCirclePath,
    normalizedThirdPeriodLoop, normalizedMeridianPairRegularPath, Path.cast_coe,
    Path.map_coe, Path.trans_apply, Function.comp_apply]
  split_ifs <;> rfl

public theorem identityMappingTorusMapOfLoop_postcomp
    {F X Y : Type} [TopologicalSpace F] [LocallyCompactSpace F]
    [TopologicalSpace X] [TopologicalSpace Y] {c : C(F, X)}
    (p : Path c c) (f : C(X, Y)) :
    identityMappingTorusMapOfLoop (p.map (ContinuousMap.continuous_postcomp f)) =
      f.comp (identityMappingTorusMapOfLoop p) := by
  ext z
  induction z using Quotient.inductionOn with
  | _ z => rfl

public theorem cuspChosenThirdSweep_interior_homology (A : PaperAnalyticData) :
    integralSingularHomologyMap 2
      (A.centralToEllipticInterior.comp
        (A.cuspChosenThirdSweepCentral.comp
          ((CircleProductIdentityMappingTorus.circleProductIdentityMappingTorusHomeomorph
            (X := StdTorus 1)).symm :
              C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)), UnitAddCircle × StdTorus 1)))) =
    integralSingularHomologyMap 2
      (identityMappingTorusMapOfLoop
        (A.normalizedThirdZeroCirclePath.trans A.normalizedThirdOneCirclePath)) := by
  rw [A.normalizedThirdMeridianCircleLoop_eq, identityMappingTorusMapOfLoop_postcomp]
  exact integralSingularHomologyMap_eq_of_homotopy 2
    ((ContinuousMap.Homotopy.refl A.centralToEllipticInterior).comp
      A.cuspChosenThirdSweep_homotopy_normalizedMeridians)

end SphereSixComplex.Geometry.PaperAnalyticData
end
