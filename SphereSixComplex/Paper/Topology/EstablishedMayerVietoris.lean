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
public theorem FourPieceOpenCover.mayerVietoris_exact
    {X : Type} [TopologicalSpace X] (C : FourPieceOpenCover X) :
    FourPieceMayerVietorisExactness C := by
  intro r
  exact IntegralMayerVietoris.exact_sequence_of_isOpen _ _
    (C.isOpen_stage r.castSucc) (C.isOpen_piece r.succ)


end SphereSixComplex
