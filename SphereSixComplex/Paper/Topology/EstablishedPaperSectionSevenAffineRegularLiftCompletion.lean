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

namespace SphereSixComplex.Geometry.PaperAnalyticData

/-- The two band maps induced by the proved affine overlap
equivalences are homotopic to the finite-cover projections marked by the unique affine-strip
lift normalized by the common peripheral marking. -/
public theorem affineRegularLiftMarkedBandHomotopies (A : PaperAnalyticData) :
    A.AffineOverlapBandCompatibility :=
  A.actualMarkedBandHomotopies


/-- Collar shrinks give the overlap equivalences, and normalized radial bounds give the
marked band homotopies. Together they supply the full affine completion. -/
public theorem affineOverlapCompletionInput (A : PaperAnalyticData) :
    A.AffineOverlapCompletionInput :=
  (affineRegularLiftMarkedBandHomotopies A).toOverlapCompletionInput

/-- Exact drop-in replacement for the former broad radial-completion existence assumption. -/
public theorem affineRadialCompletionInput_nonempty
    (A : PaperAnalyticData) :
    Nonempty A.AffineRadialCompletionInput :=
  ⟨(affineOverlapCompletionInput A).toRadialCompletion⟩


end SphereSixComplex.Geometry.PaperAnalyticData

end
