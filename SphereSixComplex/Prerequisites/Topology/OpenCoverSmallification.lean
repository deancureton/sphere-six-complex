module

public import SphereSixComplex.Prerequisites.Topology.SingularExcisionOpenCover
public import SphereSixComplex.Prerequisites.Topology.SingularStandardSimplexCone

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set
namespace SphereSixComplex

/-- Open-cover smallification data in the interface used by the Section 7 reduction.  Formerly an
axiom, this is now a thin wrapper around `coverSmallChainRetractionData_of_openCover`; the
established name is retained so existing consumers remain unchanged. -/
public noncomputable def establishedOpenCoverSmallChainRetractionData
    {ι X : Type} [TopologicalSpace X] (U : ι → Set X)
    (hOpen : ∀ i, IsOpen (U i)) (hCover : ⋃ i, U i = Set.univ) :
    CoverSmallChainRetractionData (TopCat.of X) U :=
  coverSmallChainRetractionData_of_openCover (TopCat.of X) U hOpen hCover

end SphereSixComplex
