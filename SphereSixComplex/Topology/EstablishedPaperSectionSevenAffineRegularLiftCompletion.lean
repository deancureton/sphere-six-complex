module

public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedRetractionGeometry
public import SphereSixComplex.Topology.PaperSectionSevenAffineOverlapInterleaving

/-!
# Established overlap input for the affine completion

The paper's remaining affine topology is recorded at exactly the level used by the radial
completion.  Both overlap inclusions are now *proved* to be homotopy equivalences, by the radial
shrink of the Cayley star collars in
`SphereSixComplex.Topology.PaperSectionSevenAffineOverlapInterleaving`.  What is still assumed is
only the pair of marked band squares: the induced band maps are homotopic to the two marked
finite-cover projections.  No quotient model or set-level identification of an overlap with an
affine disc is assumed.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

namespace EstablishedSectionSevenAffineRegularLiftTopology

/-- The exact remaining paper geometry: the two band maps induced by the proved affine overlap
equivalences are homotopic to the named finite-cover projections. -/
public axiom markedBandHomotopies (A : PaperAnalyticData) :
    A.SectionSevenAffineOverlapBandCompatibility

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

/-- The exact residual affine input from the paper: the two marked band square homotopies.

**Do not weaken the trivialization used here.**  This statement was *false* in an earlier form of
the development, and is sound only because the band trivialization is taken at a *named* lift.
Historically `sectionSevenAffineCentralBandProductHomeomorph` was
`(establishedActualCentralBandProductTrivialization A S).choose`.  Since
`IsHomeomorphicTrivialFiberBundle` pins only the *base* coordinate, that left the fibre coordinate
entirely free: post-composing the chosen trivialization with a fibrewise self-homeomorphism lying
outside the order-three subgroup of `GL₄(ℤ)` falsifies the band square, so no proof of the
un-marked statement could exist.  The current
`sectionSevenAffineCentralBandMarkedProductHomeomorph` is built from the named
`sectionSevenAffineNamedStripLift`, which pins the fibre coordinate and makes
`SectionSevenAffineOverlapBandCompatibility` a true statement.  Anyone tempted to "simplify" the
marked product homeomorphism back to an `Exists.choose` would be reintroducing a false axiom. -/
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

/-- The full residual affine input: radial contraction of each actual overlap and the two marked
band homotopies.  The two overlap homotopy equivalences are supplied by the proved collar shrinks,
so only the band squares are assumed. -/
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
