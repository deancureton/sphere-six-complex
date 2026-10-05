module

public import SphereSixComplex.Paper.Geometry.GlobalTorusFiberFundamentalGroup
public import SphereSixComplex.Prerequisites.Topology.FreeLoopHomology

@[expose] public section
noncomputable section
open scoped ContinuousMap
open SphereSixComplex.Hurewicz.Chains
open SphereSixComplex.StandardCircleHomologyLiftDegree
open SphereSixComplex.Periods SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily

namespace SphereSixComplex.Geometry.GlobalTorusFamily

theorem loopHomologyClass_regularFamilyPeriodLoop
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (p q : RegularBase (U := U) × ComplexTwoSpace) (a : IntegerPeriods)
    {Y : Type} [TopologicalSpace Y] (f : C(RegularTotalSpace F, Y)) :
    loopHomologyClass ((regularFamilyPeriodLoop F p a).map f.continuous) =
      loopHomologyClass ((regularFamilyPeriodLoop F q a).map f.continuous) := by
  let _ := regularBase_pathConnected U
  obtain ⟨P⟩ := PathConnectedSpace.joined p q
  let H := (ContinuousMap.Homotopy.refl f).comp
    (regularFamilyPeriodLoopHomotopyAlong F P a)
  apply loopHomologyClass_eq_of_freeHomotopy _ _ H
  intro s
  change f (regularFamilyCoverProjection F
    ((P s).1, (0 : ℝ) • periodVector (regularParameterMap F (P s).1).1 a + (P s).2)) =
      f (regularFamilyCoverProjection F
        ((P s).1, (1 : ℝ) • periodVector (regularParameterMap F (P s).1).1 a + (P s).2))
  simpa only [zero_smul, one_smul, zero_add] using
    (congrArg f (regularFamilyProjection_period_smul F (P s) a)).symm

theorem loopHomologyClass_regularFamilyPeriodLoop_rhoLambda
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (p : RegularBase (U := U) × ComplexTwoSpace)
    (g : SphereSixComplex.TriangleGroup.Delta) (a : IntegerPeriods) :
    loopHomologyClass ((regularFamilyPeriodLoop F p
      (SphereSixComplex.TriangleGroup.rhoLambda g a)).map
      (regularFamilyQuotientMap F).continuous) =
    loopHomologyClass ((regularFamilyPeriodLoop F p a).map
      (regularFamilyQuotientMap F).continuous) := by
  have h := loopHomologyClass_regularFamilyPeriodLoop F p (regularDeckMap F g p)
    (SphereSixComplex.TriangleGroup.rhoLambda g a) (regularFamilyQuotientMap F)
  have hd := congrArg loopHomologyClass (regularFamilyPeriodLoop_deck F g p a)
  rw [loopHomologyClass_cast] at hd
  exact h.trans hd

end SphereSixComplex.Geometry.GlobalTorusFamily
