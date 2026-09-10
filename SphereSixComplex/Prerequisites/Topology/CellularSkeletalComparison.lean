module

public import SphereSixComplex.Prerequisites.Topology.CellularHomologyClassicalBoundary

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

namespace CellularHomology.IntegralComparison

variable (T : CellularHomology.IntegralComparison)
  (X : Type) [TopologicalSpace X] [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]

public theorem homologyEquiv_skeletal_apply (n : ℕ)
    (x : (CWIntegralSingularChainComplexObj
      (TopCat.of (IntegralCWSkeletonLT X (n + 1)))).homology n) :
    T.homologyEquiv X n ((integralCWSkeletalHomologyToCellular X n).hom x) =
      (HomologicalComplex.homologyMap
        (cwIntegralSingularChainMapObj (integralCWSkeletonToSpace X (n + 1))) n).hom x :=
  ConcreteCategory.congr_hom (T.homologyEquiv_skeletal X n) x

public theorem homologyEquiv_of_skeletalCycle (n : ℕ) {A : AddCommGrpCat}
    (a : A ⟶
      (integralCWSkeletalChainComplex X (integralCWRelativeBoundary_comp_self X)).cycles n)
    (b : A ⟶
      (CWIntegralSingularChainComplexObj (TopCat.of (IntegralCWSkeletonLT X (n + 1)))).homology n)
    (h : b ≫ HomologicalComplex.homologyMap
        (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion X n)) n =
      a ≫ (integralCWSkeletalChainComplex X
        (integralCWRelativeBoundary_comp_self X)).iCycles n) :
    a ≫ (integralCWSkeletalChainComplex X
        (integralCWRelativeBoundary_comp_self X)).homologyπ n ≫
        (T.homologyEquiv X n).toAddCommGrpIso.hom =
      b ≫ HomologicalComplex.homologyMap
        (cwIntegralSingularChainMapObj (integralCWSkeletonToSpace X (n + 1))) n := by
  let K := integralCWSkeletalChainComplex X (integralCWRelativeBoundary_comp_self X)
  let p : (CWIntegralSingularChainComplexObj
      (TopCat.of (IntegralCWSkeletonLT X (n + 1)))).homology n ⟶ K.X n :=
    HomologicalComplex.homologyMap
    (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion X n)) n
  have ha : a = b ≫ K.liftCycles p _ rfl (integralCWSkeletalProjection_cycle X n) := by
    rw [← cancel_mono (K.iCycles n), Category.assoc, HomologicalComplex.liftCycles_i]
    exact h.symm
  rw [ha, Category.assoc]
  exact congrArg (b ≫ ·) (T.homologyEquiv_skeletal X n)

end CellularHomology.IntegralComparison

end SphereSixComplex
