module
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedMeridianLifts
public import SphereSixComplex.Paper.Topology.RegularPeriodCircleSideSupport
public import SphereSixComplex.Prerequisites.Topology.MappingTorusTwoSliceBoundary

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory TopologicalSpace
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology GlobalTorusFamily TriangleGroup ComplexTorus
open EllipticTwoDiscHomologyCoordinates

public def centralToEllipticInterior (A : PaperAnalyticData) :
    C(A.CentralFamily, A.ellipticInterior) :=
  ⟨fun x ↦ (A.ellipticCentralImageHomeomorph.symm x).1,
    continuous_subtype_val.comp A.ellipticCentralImageHomeomorph.symm.continuous⟩

public def markedPeriodCircle {A : PaperAnalyticData}
    (R : A.AffineRadialCompletionInput) (n : IntegerPeriods) :
    C(UnitAddCircle, (Opens.toTopCat (TopCat.of A.ellipticInterior)).obj
      (orderThreeOpen R.twoDiscCover ⊓ orderFourOpen R.twoDiscCover)) := by
  refine ⟨fun t ↦ ⟨A.regularPeriodCircleToInterior n (t, A.affineMarkedMidpoint),
    ?_, ?_⟩, ?_⟩
  · apply regularPeriodCircleToInterior_mem_three R
    change (A.regularCoordinate A.affineMarkedMidpoint).1.re < _
    rw [A.affineMarkedMidpoint_projects]
    norm_num [twicePuncturedComplexBasepoint]
  · apply regularPeriodCircleToInterior_mem_four R
    change _ < (A.regularCoordinate A.affineMarkedMidpoint).1.re
    rw [A.affineMarkedMidpoint_projects]
    norm_num [twicePuncturedComplexBasepoint]
  · exact ((A.regularPeriodCircleToInterior n).continuous.comp
      (continuous_id.prodMk continuous_const)).subtype_mk _

public def markedMeridianCirclePath (A : PaperAnalyticData)
    (n : IntegerPeriods)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint) :
    Path (A.centralToEllipticInterior.comp
      (regularPeriodCircleFamily A.periods n A.affineMarkedMidpoint))
      (A.centralToEllipticInterior.comp (regularPeriodCircleFamily A.periods
        (rhoLambda (A.affineMarkedLoopDeck γ)⁻¹ n)
        A.affineMarkedMidpoint)) :=
  (regularPeriodCircleDeckPath A.periods n (A.affineMarkedLoopDeck γ)
    (A.affineMarkedLoopLift γ)).map
      (ContinuousMap.continuous_postcomp A.centralToEllipticInterior)

public theorem markedMeridianCirclePath_apply (A : PaperAnalyticData)
    (n : IntegerPeriods)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint)
    (u : unitInterval) (t : UnitAddCircle) :
    A.markedMeridianCirclePath n γ u t =
      A.regularPeriodCircleToInterior n (t, A.affineMarkedLoopLift γ u) := rfl

public theorem markedZeroCirclePath_mem_three {A : PaperAnalyticData}
    (R : A.AffineRadialCompletionInput) (n : IntegerPeriods)
    (u : unitInterval) (t : UnitAddCircle) :
    A.markedMeridianCirclePath n twicePuncturedClockwiseZeroMeridian u t ∈
      R.twoDiscCover.orderThreeSide := by
  rw [markedMeridianCirclePath_apply]
  apply regularPeriodCircleToInterior_mem_three R
  exact A.affineMarkedZeroLift_mem_left u

public theorem markedOneCirclePath_mem_four {A : PaperAnalyticData}
    (R : A.AffineRadialCompletionInput) (n : IntegerPeriods)
    (u : unitInterval) (t : UnitAddCircle) :
    A.markedMeridianCirclePath n twicePuncturedClockwiseOneMeridian u t ∈
      R.twoDiscCover.orderFourSide := by
  rw [markedMeridianCirclePath_apply]
  apply regularPeriodCircleToInterior_mem_four R
  exact A.affineMarkedOneLift_mem_right u

public def markedTwoMeridianCircleLoop (A : PaperAnalyticData)
    (n : IntegerPeriods)
    (hclosed : rhoLambda (A.affineMarkedLoopDeck
        twicePuncturedClockwiseOneMeridian)⁻¹
      (rhoLambda (A.affineMarkedLoopDeck
        twicePuncturedClockwiseZeroMeridian)⁻¹ n) = n) :
    Path (A.centralToEllipticInterior.comp
      (regularPeriodCircleFamily A.periods n A.affineMarkedMidpoint))
      (A.centralToEllipticInterior.comp
        (regularPeriodCircleFamily A.periods n A.affineMarkedMidpoint)) :=
  (A.markedMeridianCirclePath n twicePuncturedClockwiseZeroMeridian).trans
    ((A.markedMeridianCirclePath
      (rhoLambda (A.affineMarkedLoopDeck twicePuncturedClockwiseZeroMeridian)⁻¹ n)
      twicePuncturedClockwiseOneMeridian).cast rfl
        (congrArg (fun m ↦ A.centralToEllipticInterior.comp
          (regularPeriodCircleFamily A.periods m A.affineMarkedMidpoint)) hclosed).symm)

public theorem markedTwoMeridianCircleLoop_boundary {A : PaperAnalyticData}
    (R : A.AffineRadialCompletionInput) (n : IntegerPeriods)
    (hclosed : rhoLambda (A.affineMarkedLoopDeck
        twicePuncturedClockwiseOneMeridian)⁻¹
      (rhoLambda (A.affineMarkedLoopDeck
        twicePuncturedClockwiseZeroMeridian)⁻¹ n) = n)
    (x : IntegralSingularHomology 2 (CircleMappingTorus (Homeomorph.refl UnitAddCircle))) :
    ConcreteCategory.hom ((BinaryOpenCover.openCoverHomologyComparisonOfCover
      (ellipticOpenCover R.twoDiscCover)).boundary 1)
      (integralSingularHomologyMap 2
        (identityMappingTorusMapOfLoop (A.markedTwoMeridianCircleLoop n hclosed)) x) =
    integralSingularHomologyMap 1
      (markedPeriodCircle R
        (rhoLambda (A.affineMarkedLoopDeck twicePuncturedClockwiseZeroMeridian)⁻¹ n))
      ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl UnitAddCircle) 1).boundary x) -
    integralSingularHomologyMap 1 (markedPeriodCircle R n)
      ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl UnitAddCircle) 1).boundary x) := by
  exact twoSideCircleLoop_boundary (orderThreeOpen R.twoDiscCover) (orderFourOpen R.twoDiscCover)
    (ellipticOpenCover R.twoDiscCover)
    (markedPeriodCircle R n)
    (markedPeriodCircle R
      (rhoLambda (A.affineMarkedLoopDeck twicePuncturedClockwiseZeroMeridian)⁻¹ n))
    (A.markedMeridianCirclePath n twicePuncturedClockwiseZeroMeridian)
    ((A.markedMeridianCirclePath
      (rhoLambda (A.affineMarkedLoopDeck twicePuncturedClockwiseZeroMeridian)⁻¹ n)
      twicePuncturedClockwiseOneMeridian).cast rfl
        (congrArg (fun m ↦ A.centralToEllipticInterior.comp
          (regularPeriodCircleFamily A.periods m A.affineMarkedMidpoint)) hclosed).symm)
    (markedZeroCirclePath_mem_three R n)
    (markedOneCirclePath_mem_four R _) 1 x

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
