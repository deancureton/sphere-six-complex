module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedBandSquares
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineOverlapInterleaving
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineNormalizedBandCompatibility

/-!
# Proved affine overlap completion

The affine topology is proved at the homotopy level actually used by the
radial completion.  Both overlap inclusions are proved homotopy equivalences in the preceding
modules; the marked band homotopies follow from normalized radial collar bounds.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.AnalyticData

/-- Collar shrinks give the overlap equivalences, and normalized radial bounds give the
marked band homotopies. Together they supply the full affine completion. -/
public theorem affineOverlapCompletionInput (A : AnalyticData) :
    A.AffineOverlapCompletionInput :=
  {
    orderThreeOverlap := A.orderThreeOverlapIsHomotopyEquivalence
    orderFourOverlap := A.orderFourOverlapIsHomotopyEquivalence
    orderThreeCompatibility := A.homotopic_bandToReducedFiber_coverMap.1
    orderFourCompatibility := A.homotopic_bandToReducedFiber_coverMap.2 }

/-- Exact drop-in replacement for the former broad radial-completion existence assumption. -/
public theorem affineRadialCompletionInput_nonempty
    (A : AnalyticData) :
    Nonempty A.AffineRadialCompletionInput :=
  ⟨(affineOverlapCompletionInput A).toRadialCompletion⟩


end SphereSixComplex.Geometry.AnalyticData

end
