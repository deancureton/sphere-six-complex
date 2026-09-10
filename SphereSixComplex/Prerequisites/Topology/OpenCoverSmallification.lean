module

public import SphereSixComplex.Prerequisites.Topology.SingularExcisionOpenCover
public import SphereSixComplex.Prerequisites.Topology.SingularStandardSimplexCone

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set
namespace SphereSixComplex

/-- Open-cover small-chain retraction data, obtained by applying the singular-chain construction
to the associated topological space. -/
public noncomputable def coverSmallChainRetractionData
    {ι X : Type} [TopologicalSpace X] (U : ι → Set X)
    (hOpen : ∀ i, IsOpen (U i)) (hCover : ⋃ i, U i = Set.univ) :
    CoverSmallChainRetractionData (TopCat.of X) U :=
  coverSmallChainRetractionData_of_openCover (TopCat.of X) U hOpen hCover

end SphereSixComplex
