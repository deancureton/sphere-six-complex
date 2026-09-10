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

namespace EstablishedSectionSevenAffineRegularLiftTopology

/-- The two band maps induced by the proved affine overlap
equivalences are homotopic to the finite-cover projections marked by the unique affine-strip
lift normalized by the common peripheral marking. -/
public theorem markedBandHomotopies (A : PaperAnalyticData) :
    A.SectionSevenAffineOverlapBandCompatibility :=
  A.actualMarkedBandHomotopies

/-- The marked band homotopies and the proved overlap equivalences supply marked retractions.
The retractions themselves are the canonical homotopy inverses of the two proved inclusion
equivalences, whose inverse maps are the literal subspace inclusions. -/
public theorem markedRetractionInput_nonempty (A : PaperAnalyticData) :
    Nonempty A.SectionSevenAffineMarkedRetractionInput := by
  let hThree := orderThreeOverlapIsHomotopyEquivalence_inclusion
    A.orderThreeOverlapIsHomotopyEquivalence
  let hFour := orderFourOverlapIsHomotopyEquivalence_inclusion
    A.orderFourOverlapIsHomotopyEquivalence
  refine ⟨{ orderThree := ?_, orderFour := ?_ }⟩
  · exact
      { retraction := hThree.toHomotopyEquiv
        invFun_eq := hThree.toHomotopyEquiv_invFun
        markedSquare := by
          rw [← sectionSevenAffineOrderThreeBandToReducedFiber_eq_bandMapOfRetraction]
          rw [sectionSevenAffineBandOrderThreeMarkedProjection_eq_coverMap]
          exact (markedBandHomotopies A).orderThree }
  · exact
      { retraction := hFour.toHomotopyEquiv
        invFun_eq := hFour.toHomotopyEquiv_invFun
        markedSquare := by
          rw [← sectionSevenAffineOrderFourBandToReducedFiber_eq_bandMapOfRetraction]
          rw [sectionSevenAffineBandOrderFourMarkedProjection_eq_coverMap]
          exact (markedBandHomotopies A).orderFour }

/-- The normalized marked band squares supply the affine overlap compatibility. -/
public theorem overlapBandCompatibility (A : PaperAnalyticData) :
    A.SectionSevenAffineOverlapBandCompatibility := by
  let G := (markedRetractionInput_nonempty A).some
  refine { orderThree := ?_, orderFour := ?_ }
  · let h := orderThreeOverlapIsHomotopyEquivalence_inclusion
      A.orderThreeOverlapIsHomotopyEquivalence
    have hRetraction : h.toHomotopyEquiv.toFun.Homotopic G.orderThree.retraction.toFun :=
      homotopyEquiv_toFun_homotopic_of_invFun_eq _ _
        (h.toHomotopyEquiv_invFun.trans G.orderThree.invFun_eq.symm)
    rw [sectionSevenAffineOrderThreeBandToReducedFiber_eq_bandMapOfRetraction]
    rw [← sectionSevenAffineBandOrderThreeMarkedProjection_eq_coverMap A]
    exact (sectionSevenAffineOrderThreeBandMapOfRetraction_homotopic hRetraction).trans
      G.orderThree.markedSquare
  · let h := orderFourOverlapIsHomotopyEquivalence_inclusion
      A.orderFourOverlapIsHomotopyEquivalence
    have hRetraction : h.toHomotopyEquiv.toFun.Homotopic G.orderFour.retraction.toFun :=
      homotopyEquiv_toFun_homotopic_of_invFun_eq _ _
        (h.toHomotopyEquiv_invFun.trans G.orderFour.invFun_eq.symm)
    rw [sectionSevenAffineOrderFourBandToReducedFiber_eq_bandMapOfRetraction]
    rw [← sectionSevenAffineBandOrderFourMarkedProjection_eq_coverMap A]
    exact (sectionSevenAffineOrderFourBandMapOfRetraction_homotopic hRetraction).trans
      G.orderFour.markedSquare

/-- Collar shrinks give the overlap equivalences, and normalized radial bounds give the
marked band homotopies. Together they supply the full affine completion. -/
public theorem overlapCompletionInput (A : PaperAnalyticData) :
    A.SectionSevenAffineOverlapCompletionInput :=
  (overlapBandCompatibility A).toOverlapCompletionInput

/-- Exact drop-in replacement for the former broad radial-completion existence assumption. -/
public theorem radialCompletionInput_nonempty
    (A : PaperAnalyticData) :
    Nonempty A.SectionSevenAffineRadialCompletionInput :=
  ⟨(overlapCompletionInput A).toRadialCompletion⟩

end EstablishedSectionSevenAffineRegularLiftTopology

/-- The affine radial package selected from the explicit regular-cover construction. -/
public theorem establishedSectionSevenAffineRadialCompletionInput
    (A : PaperAnalyticData) :
    A.SectionSevenAffineRadialCompletionInput :=
  (EstablishedSectionSevenAffineRegularLiftTopology.overlapCompletionInput A).toRadialCompletion

end SphereSixComplex.Geometry.PaperAnalyticData

end
