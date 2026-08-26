module

public import SphereSixComplex.Topology.PaperSectionSevenAffineBandTrivializationDefs
public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandTrivialization

/-!
# The affine central band as a trivial torus bundle

The base of the concrete central height band is the convex vertical strip
`1 / 3 < re z < 2 / 3`.  Once the actual central torus bundle is trivialized over this strip,
contractibility of the strip gives the homotopy equivalence required by the radial input.

The strip, the band projection, and the product-trivialization statement itself now live in
`PaperSectionSevenAffineBandTrivializationDefs`; the trivialization is proved in
`PaperSectionSevenAffineMarkedBandTrivialization` and is merely repackaged here under its
historical name.
-/

@[expose] public section

noncomputable section

open Set Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

namespace EstablishedSectionSevenAffineBandTopology

/-- Standard quotient-bundle triviality over the convex affine strip.  The unconditional
real-period product coordinates trivialize the varying lattice upstairs, while the unique lift of
the simply connected strip through the regular-coordinate covering trivializes the descended
quotient bundle.  Both ingredients are assembled into the marked trivialization, of which this is
the forgetful consequence. -/
public theorem establishedActualCentralBandProductTrivialization
    (A : PaperAnalyticData) (S : A.SectionSevenAffineCentralSeparation) :
    A.SectionSevenAffineCentralBandProductTrivialization S :=
  SectionSevenAffineCentralBandMarkedTrivialization.toProductTrivialization
    (establishedActualCentralBandMarkedTrivialization A S)

end EstablishedSectionSevenAffineBandTopology

open EstablishedSectionSevenAffineBandTopology

variable (A : PaperAnalyticData)

/-- The standard product trivialization over the affine strip supplies exactly the
`bandHomotopyEquiv` field of the central-height radial input. -/
public noncomputable def SectionSevenAffineCentralBandProductTrivialization.bandHomotopyEquiv
    {S : A.SectionSevenAffineCentralSeparation}
    (T : A.SectionSevenAffineCentralBandProductTrivialization S) :
    centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper ≃ₕ
      AdditiveTorus A.duplicatedSectionSevenBandParameter := by
  let _ : ContractibleSpace sectionSevenAffineVerticalStrip :=
    sectionSevenAffineVerticalStripContractible
  exact homotopyEquivFiberOfTrivialBundle T

/-- The established quotient-bundle triviality gives the concrete central band equivalence used
by the radial realization. -/
public noncomputable def sectionSevenAffineCentralBandHomotopyEquiv
    (S : A.SectionSevenAffineCentralSeparation) :
    centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper ≃ₕ
      AdditiveTorus A.duplicatedSectionSevenBandParameter :=
  by
    let T := establishedActualCentralBandProductTrivialization A S
    exact SectionSevenAffineCentralBandProductTrivialization.bandHomotopyEquiv A T

end SphereSixComplex.Geometry.PaperAnalyticData
