module

public import SphereSixComplex.Topology.PaperSectionSevenCuspWangFullFibreSlice

/-!
# Oriented chain comparison for the explicit cusp fibre slice

The full-fibre slice constructs the map from the actual cusp fibre into the intersection of the
pulled-back binary cover.  The remaining input is therefore reduced to two equalities for that
specific map: its period-marked identification with the elliptic band and the oriented
connecting-morphism comparison.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- The exact residual comparison for the constructed full-fibre slice.  The second equality
fixes the sign of the connecting morphism. -/
public structure ActualCuspWangFullFibreSliceComparison
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop where
  fiberToBand_homology :
    R.twoDiscCover.canonicalCuspFiberToBandHomologyOne =
      actualCuspWangFibreToBandHomologyOne (A := A) R
  wangBoundary_eq_chainConnecting :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R).comp
        (actualCuspWangBoundaryHom A) =
      R.twoDiscCover.cuspOpenCoverConnectingHom

namespace EstablishedActualCuspWangOpenCoverChainRealization

/-- The period-marked and oriented chain comparison for the explicitly constructed full-fibre
slice. -/
public axiom fullFibreSliceComparison (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspWangFullFibreSliceComparison R

/-- The standard chain-level Wang theorem for the actual radial mapping-torus cut cover.  Its
content is the oriented realization of the established Wang connecting map by the explicit
short exact singular-chain sequence, before transport to the elliptic cover. -/
public noncomputable def realization (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.ActualCuspWangOpenCoverChainRealization :=
  actualCuspWangOpenCoverChainRealization_of_fullFibreSlice (A := A) R
    (fullFibreSliceComparison R).fiberToBand_homology
    (fullFibreSliceComparison R).wangBoundary_eq_chainConnecting

end EstablishedActualCuspWangOpenCoverChainRealization

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
