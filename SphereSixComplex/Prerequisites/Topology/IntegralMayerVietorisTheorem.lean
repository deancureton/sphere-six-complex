module

public import SphereSixComplex.Prerequisites.Topology.BinaryOpenCoverLegacyMayerVietoris

namespace SphereSixComplex

/-- The integral singular-homology Mayer--Vietoris sequence for two open subsets, with difference
map `(i_*, -j_*)` and sum map `k_* + l_*` as defined in `IntegralMayerVietoris`. -/
public theorem IntegralMayerVietoris.exact_sequence_of_isOpen
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) :
    IntegralMayerVietoris.ExactSequence A B :=
  BinaryOpenCover.integralMayerVietorisExactSequence_of_isOpen A B hA hB

end SphereSixComplex
