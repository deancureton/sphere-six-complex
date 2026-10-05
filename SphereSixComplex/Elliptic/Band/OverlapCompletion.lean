module

public import SphereSixComplex.Elliptic.Band.HomologyComparison

/-!
# Proved affine overlap completion

The affine topology is proved at the homotopy level actually used by the
radial completion.  Both overlap inclusions are proved homotopy equivalences in the preceding
modules; the marked band homotopies are determined by a midpoint torus slice.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.AnalyticData

/-- Collar shrinks give the overlap equivalences, and midpoint torus comparisons give
the marked band homotopies. -/
public theorem affineOverlapCompletionInput (A : AnalyticData) :
    A.AffineOverlapCompletionInput :=
  {
    orderThreeOverlap := A.orderThreeOverlapIsHomotopyEquivalence
    orderFourOverlap := A.orderFourOverlapIsHomotopyEquivalence
    orderThreeCompatibility := A.midpointComparisonThree_compatibility
    orderFourCompatibility := A.midpointComparisonFour_compatibility }

/-- Exact drop-in replacement for the former broad radial-completion existence assumption. -/
public theorem affineRadialCompletionInput_nonempty
    (A : AnalyticData) :
    Nonempty A.AffineRadialCompletionInput :=
  ⟨(affineOverlapCompletionInput A).toRadialCompletion⟩


end SphereSixComplex.Geometry.AnalyticData

end
