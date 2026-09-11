module

public import SphereSixComplex.Prerequisites.Topology.CellularHomology

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

namespace CellularHomology.IntegralComparison

variable (T : CellularHomology.IntegralComparison)
  (X : Type) [TopologicalSpace X] [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]

public theorem homologyEquiv_skeletal_apply (n : ℕ)
    (x : (cwIntegralSingularChainComplexObj
      (TopCat.of (IntegralCWSkeletonLT X (n + 1)))).homology n) :
    T.homologyEquiv X n ((integralCWSkeletalHomologyToCellular X n).hom x) =
      (HomologicalComplex.homologyMap
        (cwIntegralSingularChainMapObj (integralCWSkeletonToSpace X (n + 1))) n).hom x :=
  ConcreteCategory.congr_hom (T.homologyEquiv_skeletal X n) x


end CellularHomology.IntegralComparison

end SphereSixComplex
