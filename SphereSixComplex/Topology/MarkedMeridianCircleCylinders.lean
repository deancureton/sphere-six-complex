module
public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedMeridianLifts
public import SphereSixComplex.Topology.RegularPeriodCircleSideSupport
public import SphereSixComplex.Topology.MappingTorusTwoSliceBoundary

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory TopologicalSpace
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology GlobalTorusFamily TriangleGroup ComplexTorus
open SectionSevenEllipticTwoDiscHomologyCoordinates

public def centralToEllipticInterior (A : PaperAnalyticData) :
    C(A.CentralFamily, A.SectionSevenEllipticInterior) :=
  ⟨fun x ↦ (A.sectionSevenEllipticCentralImageHomeomorph.symm x).1,
    continuous_subtype_val.comp A.sectionSevenEllipticCentralImageHomeomorph.symm.continuous⟩

public def sectionSevenMarkedPeriodCircle {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) (n : IntegerPeriods) :
    C(UnitAddCircle, (Opens.toTopCat (TopCat.of A.SectionSevenEllipticInterior)).obj
      (orderThreeOpen R.twoDiscCover ⊓ orderFourOpen R.twoDiscCover)) := by
  refine ⟨fun t ↦ ⟨A.regularPeriodCircleToInterior n (t, A.sectionSevenAffineMarkedMidpoint),
    ?_, ?_⟩, ?_⟩
  · apply regularPeriodCircleToInterior_mem_three R
    change (A.regularCoordinate A.sectionSevenAffineMarkedMidpoint).1.re < _
    rw [A.sectionSevenAffineMarkedMidpoint_projects]
    norm_num [twicePuncturedComplexBasepoint]
  · apply regularPeriodCircleToInterior_mem_four R
    change _ < (A.regularCoordinate A.sectionSevenAffineMarkedMidpoint).1.re
    rw [A.sectionSevenAffineMarkedMidpoint_projects]
    norm_num [twicePuncturedComplexBasepoint]
  · exact ((A.regularPeriodCircleToInterior n).continuous.comp
      (continuous_id.prodMk continuous_const)).subtype_mk _

public def sectionSevenMarkedMeridianCirclePath (A : PaperAnalyticData)
    (n : IntegerPeriods)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint) :
    Path (A.centralToEllipticInterior.comp
      (regularPeriodCircleFamily A.periods n A.sectionSevenAffineMarkedMidpoint))
      (A.centralToEllipticInterior.comp (regularPeriodCircleFamily A.periods
        (rhoLambda (A.sectionSevenAffineMarkedLoopDeck γ)⁻¹ n)
        A.sectionSevenAffineMarkedMidpoint)) :=
  (regularPeriodCircleDeckPath A.periods n (A.sectionSevenAffineMarkedLoopDeck γ)
    (A.sectionSevenAffineMarkedLoopLift γ)).map
      (ContinuousMap.continuous_postcomp A.centralToEllipticInterior)

public theorem sectionSevenMarkedMeridianCirclePath_apply (A : PaperAnalyticData)
    (n : IntegerPeriods)
    (γ : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint)
    (u : unitInterval) (t : UnitAddCircle) :
    A.sectionSevenMarkedMeridianCirclePath n γ u t =
      A.regularPeriodCircleToInterior n (t, A.sectionSevenAffineMarkedLoopLift γ u) := rfl

public theorem sectionSevenMarkedZeroCirclePath_mem_three {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) (n : IntegerPeriods)
    (u : unitInterval) (t : UnitAddCircle) :
    A.sectionSevenMarkedMeridianCirclePath n twicePuncturedClockwiseZeroMeridian u t ∈
      R.twoDiscCover.orderThreeSide := by
  rw [sectionSevenMarkedMeridianCirclePath_apply]
  apply regularPeriodCircleToInterior_mem_three R
  exact A.sectionSevenAffineMarkedZeroLift_mem_left u

public theorem sectionSevenMarkedOneCirclePath_mem_four {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) (n : IntegerPeriods)
    (u : unitInterval) (t : UnitAddCircle) :
    A.sectionSevenMarkedMeridianCirclePath n twicePuncturedClockwiseOneMeridian u t ∈
      R.twoDiscCover.orderFourSide := by
  rw [sectionSevenMarkedMeridianCirclePath_apply]
  apply regularPeriodCircleToInterior_mem_four R
  exact A.sectionSevenAffineMarkedOneLift_mem_right u

public def sectionSevenMarkedTwoMeridianCircleLoop (A : PaperAnalyticData)
    (n : IntegerPeriods)
    (hclosed : rhoLambda (A.sectionSevenAffineMarkedLoopDeck
        twicePuncturedClockwiseOneMeridian)⁻¹
      (rhoLambda (A.sectionSevenAffineMarkedLoopDeck
        twicePuncturedClockwiseZeroMeridian)⁻¹ n) = n) :
    Path (A.centralToEllipticInterior.comp
      (regularPeriodCircleFamily A.periods n A.sectionSevenAffineMarkedMidpoint))
      (A.centralToEllipticInterior.comp
        (regularPeriodCircleFamily A.periods n A.sectionSevenAffineMarkedMidpoint)) :=
  (A.sectionSevenMarkedMeridianCirclePath n twicePuncturedClockwiseZeroMeridian).trans
    ((A.sectionSevenMarkedMeridianCirclePath
      (rhoLambda (A.sectionSevenAffineMarkedLoopDeck twicePuncturedClockwiseZeroMeridian)⁻¹ n)
      twicePuncturedClockwiseOneMeridian).cast rfl
        (congrArg (fun m ↦ A.centralToEllipticInterior.comp
          (regularPeriodCircleFamily A.periods m A.sectionSevenAffineMarkedMidpoint)) hclosed).symm)

public theorem sectionSevenMarkedTwoMeridianCircleLoop_boundary {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) (n : IntegerPeriods)
    (hclosed : rhoLambda (A.sectionSevenAffineMarkedLoopDeck
        twicePuncturedClockwiseOneMeridian)⁻¹
      (rhoLambda (A.sectionSevenAffineMarkedLoopDeck
        twicePuncturedClockwiseZeroMeridian)⁻¹ n) = n)
    (x : IntegralSingularHomology 2 (CircleMappingTorus (Homeomorph.refl UnitAddCircle))) :
    ConcreteCategory.hom ((BinaryOpenCover.openCoverHomologyComparisonOfCover
      (ellipticOpenCover R.twoDiscCover)).boundary 1)
      (integralSingularHomologyMap 2
        (identityMappingTorusMapOfLoop (A.sectionSevenMarkedTwoMeridianCircleLoop n hclosed)) x) =
    integralSingularHomologyMap 1
      (sectionSevenMarkedPeriodCircle R
        (rhoLambda (A.sectionSevenAffineMarkedLoopDeck twicePuncturedClockwiseZeroMeridian)⁻¹ n))
      ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl UnitAddCircle) 1).boundary x) -
    integralSingularHomologyMap 1 (sectionSevenMarkedPeriodCircle R n)
      ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl UnitAddCircle) 1).boundary x) := by
  exact twoSideCircleLoop_boundary (orderThreeOpen R.twoDiscCover) (orderFourOpen R.twoDiscCover)
    (ellipticOpenCover R.twoDiscCover)
    (sectionSevenMarkedPeriodCircle R n)
    (sectionSevenMarkedPeriodCircle R
      (rhoLambda (A.sectionSevenAffineMarkedLoopDeck twicePuncturedClockwiseZeroMeridian)⁻¹ n))
    (A.sectionSevenMarkedMeridianCirclePath n twicePuncturedClockwiseZeroMeridian)
    ((A.sectionSevenMarkedMeridianCirclePath
      (rhoLambda (A.sectionSevenAffineMarkedLoopDeck twicePuncturedClockwiseZeroMeridian)⁻¹ n)
      twicePuncturedClockwiseOneMeridian).cast rfl
        (congrArg (fun m ↦ A.centralToEllipticInterior.comp
          (regularPeriodCircleFamily A.periods m A.sectionSevenAffineMarkedMidpoint)) hclosed).symm)
    (sectionSevenMarkedZeroCirclePath_mem_three R n)
    (sectionSevenMarkedOneCirclePath_mem_four R _) 1 x

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
