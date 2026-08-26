module

public import SphereSixComplex.Topology.BinaryOpenCoverLegacyMayerVietoris

/-!
# Established singular-homology Mayer--Vietoris theorem

The chain-level binary open-cover construction supplies the integral singular-homology
Mayer--Vietoris theorem for arbitrary open subsets. The paper-specific homology calculation is
separate from this general theorem.
-/

namespace SphereSixComplex

/-- The integral singular-homology Mayer--Vietoris sequence for two open subsets, with difference
map `(i_*, -j_*)` and sum map `k_* + l_*` as defined in `IntegralMayerVietoris`. -/
public theorem establishedIntegralMayerVietorisExactSequence
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) :
    IntegralMayerVietoris.ExactSequence A B :=
  BinaryOpenCover.integralMayerVietorisExactSequence_of_isOpen A B hA hB

/-- The established binary theorem supplies exactness at each stage of an ordered four-piece open
cover. -/
public theorem establishedFourPieceMayerVietorisExactness
    {X : Type} [TopologicalSpace X] (C : FourPieceOpenCover X) :
    FourPieceMayerVietorisExactness C := by
  intro r
  exact establishedIntegralMayerVietorisExactSequence _ _
    (C.isOpen_stage r.castSucc) (C.isOpen_piece r.succ)

/-- A paper-specific comparison quasi-isomorphism, together with the established open-cover
Mayer--Vietoris theorem, gives the full four-piece contract. -/
public theorem fourPieceMayerVietorisContract_of_homologyComputation
    {X : Type} [TopologicalSpace X] (C : FourPieceOpenCover X)
    (h : FourPieceHomologyComputation C) : FourPieceMayerVietorisContract C :=
  ⟨establishedFourPieceMayerVietorisExactness C, h⟩

end SphereSixComplex
