module

public import SphereSixComplex.Topology.MayerVietoris

/-!
# Established singular-homology Mayer--Vietoris theorem

Mathlib does not yet provide the excision theorem needed to construct the connecting maps for
singular homology.  We isolate precisely that standard external input for two open subsets.  The
paper-specific homology calculation is not part of this axiom.
-/

namespace SphereSixComplex

/-- The integral singular-homology Mayer--Vietoris sequence for two open subsets, with difference
map `(i_*, -j_*)` and sum map `k_* + l_*` as defined in `IntegralMayerVietoris`. -/
public axiom establishedIntegralMayerVietorisExactSequence
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) :
    IntegralMayerVietoris.ExactSequence A B

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
