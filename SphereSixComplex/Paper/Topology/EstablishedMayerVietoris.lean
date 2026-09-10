module

public import SphereSixComplex.Prerequisites.Topology.IntegralMayerVietorisTheorem

/-!
# Established singular-homology Mayer--Vietoris theorem

The chain-level binary open-cover construction supplies the integral singular-homology
Mayer--Vietoris theorem for arbitrary open subsets. The paper-specific homology calculation is
separate from this general theorem.
-/

namespace SphereSixComplex

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
