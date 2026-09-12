module

public import SphereSixComplex.Paper.Topology.ConstructedPositivePeriodCoordinates
public import SphereSixComplex.Paper.Topology.ConstructedCuspPositivePhaseVanishing

@[expose] public section

noncomputable section
open Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.InfiniteA2Toric

def intervalProductSliceEquiv {X : Type*} [TopologicalSpace X] {r : ℝ}
    (t : Set.Ioo (0 : ℝ) r) : ContinuousMap.HomotopyEquiv X (X × Set.Ioo (0 : ℝ) r) where
  toFun := ⟨fun x ↦ (x,t), continuous_id.prodMk continuous_const⟩
  invFun := ⟨Prod.fst, continuous_fst⟩
  left_inv := ContinuousMap.Homotopic.refl _
  right_inv := ⟨{
    toFun := fun p ↦ (p.2.1, ⟨(1 - (p.1 : ℝ)) * t.1 + (p.1 : ℝ) * p.2.2.1,
      (convex_Ioo (0 : ℝ) r) t.2 p.2.2.2 (sub_nonneg.mpr p.1.2.2)
        p.1.2.1 (sub_add_cancel _ _)⟩)
    continuous_toFun := by fun_prop
    map_zero_left := by intro x; apply Prod.ext <;> first | rfl | (apply Subtype.ext; simp)
    map_one_left := by intro x; apply Prod.ext <;> first | rfl | (apply Subtype.ext; simp)
  }⟩

open SphereSixComplex.StandardTorusHomology
open CuspPeriodExpansion CuspPuncturedCollarBridge CuspStraighteningRetraction
open CuspRadialClutchingConstruction

def constructedFirstTorusPositiveHomotopyEquiv (A : AnalyticData) :
    ContinuousMap.HomotopyEquiv (StdTorus 2) (ConstructedA2PositiveQuotient A.starCuspWitness) :=
  ((intervalProductSliceEquiv
    (⟨‖cuspQ (markedCuspParameter A.starCuspWitness)‖,
      norm_pos_iff.mpr (Complex.exp_ne_zero _),
      (actualCuspRadialClutchingData A.starCuspWitness).markingParameter_mem⟩ :
        Set.Ioo (0 : ℝ) A.starCuspWitness.localWitness.radius)).trans
    (constructedPositiveInteriorTorusHomeomorph A.starCuspWitness).symm.toHomotopyEquiv).trans
    (constructedPositiveQuotientInteriorHomotopyEquiv A.starCuspWitness).symm

theorem constructedFirstTorusPositiveHomotopyEquiv_toFun (A : AnalyticData) :
    (constructedFirstTorusPositiveHomotopyEquiv A).toFun =
      (constructedCuspPositiveProjection A.starCuspWitness).comp
        (A.cuspFiniteFiberTorusToFilling 0) := by
  ext1 z
  exact (constructedCuspPositiveProjection_firstTorus A z).symm

def constructedFirstTorusPositiveHomologyEquiv (A : AnalyticData) :
    IntegralSingularHomology 2 (StdTorus 2) ≃+
      IntegralSingularHomology 2 (ConstructedA2PositiveQuotient A.starCuspWitness) :=
  integralSingularHomologyEquivOfHomotopyEquiv 2 (constructedFirstTorusPositiveHomotopyEquiv A)

theorem constructedFirstTorusPositiveHomologyEquiv_apply (A : AnalyticData)
    (x : IntegralSingularHomology 2 (StdTorus 2)) :
    constructedFirstTorusPositiveHomologyEquiv A x =
      integralSingularHomologyMap 2 (constructedCuspPositiveProjection A.starCuspWitness)
        (integralSingularHomologyMap 2 (A.cuspFiniteFiberTorusToFilling 0) x) := by
  change integralSingularHomologyMap 2 (constructedFirstTorusPositiveHomotopyEquiv A).toFun x = _
  rw [constructedFirstTorusPositiveHomotopyEquiv_toFun]
  erw [← integralSingularHomologyMap_comp_wang]
  rfl

def constructedPositiveHomologyTwoReadout (A : AnalyticData) :
    IntegralSingularHomology 2 (ConstructedA2PositiveQuotient A.starCuspWitness) →+ ℤ where
  toFun x := (stdTorusHomologyTwo 2 ((constructedFirstTorusPositiveHomologyEquiv A).symm x))
    standardTwoTorusDegreeTwoIndex
  map_zero' := by simp
  map_add' x y := by simp

theorem constructedPositiveHomologyTwoReadout_firstTorus (A : AnalyticData) :
    constructedPositiveHomologyTwoReadout A
      (integralSingularHomologyMap 2 (constructedCuspPositiveProjection A.starCuspWitness)
        (integralSingularHomologyMap 2 (A.cuspFiniteFiberTorusToFilling 0)
          standardTwoTorusHomologyGenerator)) = 1 := by
  rw [← constructedFirstTorusPositiveHomologyEquiv_apply]
  change (stdTorusHomologyTwo 2 ((constructedFirstTorusPositiveHomologyEquiv A).symm
    (constructedFirstTorusPositiveHomologyEquiv A standardTwoTorusHomologyGenerator)))
      standardTwoTorusDegreeTwoIndex = 1
  rw [AddEquiv.symm_apply_apply]
  simp [standardTwoTorusHomologyGenerator]


def constructedCuspHomologyTwoPositiveReadout (A : AnalyticData) :
    IntegralSingularHomology 2 (CuspPuncturedCollarBridge.ActualLocalCuspFilling A.starCuspWitness) →+ ℤ :=
  (constructedPositiveHomologyTwoReadout A).comp
    (integralSingularHomologyMap 2 (constructedCuspPositiveProjection A.starCuspWitness))



end SphereSixComplex.Geometry.InfiniteA2Toric
