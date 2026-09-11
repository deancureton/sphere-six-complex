module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedRetractionGeometry
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

/-- The marked band homotopies and the proved overlap equivalences supply marked retractions.
The retractions themselves are the canonical homotopy inverses of the two proved inclusion
equivalences, whose inverse maps are the literal subspace inclusions. -/
public theorem affineMarkedRetractionInput_nonempty (A : PaperAnalyticData) :
    Nonempty A.AffineMarkedRetractionInput := by
  let hThree := orderThreeOverlapIsHomotopyEquivalence_inclusion
    A.orderThreeOverlapIsHomotopyEquivalence
  let hFour := orderFourOverlapIsHomotopyEquivalence_inclusion
    A.orderFourOverlapIsHomotopyEquivalence
  refine ⟨{ orderThree := ?_, orderFour := ?_ }⟩
  · exact
      { retraction := hThree.toHomotopyEquiv
        invFun_eq := hThree.toHomotopyEquiv_invFun
        markedSquare := by
          rw [← affineOrderThreeBandToReducedFiber_eq_bandMapOfRetraction]
          rw [affineBandOrderThreeMarkedProjection_eq_coverMap]
          exact (affineRegularLiftMarkedBandHomotopies A).orderThree }
  · exact
      { retraction := hFour.toHomotopyEquiv
        invFun_eq := hFour.toHomotopyEquiv_invFun
        markedSquare := by
          rw [← affineOrderFourBandToReducedFiber_eq_bandMapOfRetraction]
          rw [affineBandOrderFourMarkedProjection_eq_coverMap]
          exact (affineRegularLiftMarkedBandHomotopies A).orderFour }

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

/-- The affine radial package selected from the explicit regular-cover construction. -/
public theorem affineRadialCompletion
    (A : PaperAnalyticData) :
    A.AffineRadialCompletionInput :=
  (_root_.SphereSixComplex.Geometry.PaperAnalyticData.affineOverlapCompletionInput A).toRadialCompletion

end SphereSixComplex.Geometry.PaperAnalyticData

end
