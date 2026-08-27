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

/-- The single named lift of the convex affine strip through the regular-coordinate covering.
Every central-band fibre coordinate in the development is marked by *this* lift; it is named here
once and nowhere else. -/
public noncomputable def sectionSevenAffineNamedStripLift : A.SectionSevenAffineStripLift :=
  A.sectionSevenAffineStripLift_nonempty.some

/-- The named marked product trivialization of the affine central band: the marked trivialization
of `PaperSectionSevenAffineMarkedBandTrivialization` taken at `sectionSevenAffineNamedStripLift`.
Both coordinates are pinned — the base coordinate by
`sectionSevenAffineCentralBandMarkedProductHomeomorph_fst` and the fibre coordinate by
`sectionSevenAffineCentralBandMarkedProductHomeomorph_symm_toCentralFamily`. -/
public noncomputable def sectionSevenAffineCentralBandMarkedProductHomeomorph
    (S : A.SectionSevenAffineCentralSeparation) :
    centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper ≃ₜ
      sectionSevenAffineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter :=
  (A.sectionSevenAffineCentralBandProductHomeomorphOfLift S
    A.sectionSevenAffineNamedStripLift).symm

/-- The named marked trivialization has the affine band projection as its base coordinate, so it
is in particular a witness of the unmarked product-trivialization statement. -/
public theorem sectionSevenAffineCentralBandMarkedProductHomeomorph_fst
    (S : A.SectionSevenAffineCentralSeparation)
    (x : centralHeightBand
      (A.sectionSevenAffineCentralHeightSplit S).height
      (A.sectionSevenAffineCentralHeightSplit S).lower
      (A.sectionSevenAffineCentralHeightSplit S).upper) :
    (A.sectionSevenAffineCentralBandMarkedProductHomeomorph S x).1 =
      A.sectionSevenAffineCentralBandProjection S x := by
  have hkey := A.sectionSevenAffineCentralBandProductHomeomorphOfLift_toCentralFamily S
    A.sectionSevenAffineNamedStripLift
    (A.sectionSevenAffineCentralBandMarkedProductHomeomorph S x)
  rw [sectionSevenAffineCentralBandMarkedProductHomeomorph, Homeomorph.apply_symm_apply] at hkey
  have hcoord := congrArg A.centralFamilyCoordinate hkey
  rw [A.centralFamilyCoordinate_stripLiftPoint] at hcoord
  apply Subtype.ext
  exact (congrArg (Subtype.val : RegularCoordinateBase → ℂ) hcoord).symm

/-- The marking itself: the fibre coordinate of the named trivialization is the canonical
real-period coordinate of the central four-torus along the named strip lift.  This is the
property that `Exists.choose` of the unmarked statement could never supply. -/
public theorem sectionSevenAffineCentralBandMarkedProductHomeomorph_symm_toCentralFamily
    (S : A.SectionSevenAffineCentralSeparation)
    (p : sectionSevenAffineVerticalStrip ×
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    A.sectionSevenAffineCentralBandToCentralFamily S
        ((A.sectionSevenAffineCentralBandMarkedProductHomeomorph S).symm p) =
      A.stripLiftPoint A.sectionSevenAffineNamedStripLift p.1 p.2 := by
  rw [sectionSevenAffineCentralBandMarkedProductHomeomorph, Homeomorph.symm_symm]
  exact A.sectionSevenAffineCentralBandProductHomeomorphOfLift_toCentralFamily S
    A.sectionSevenAffineNamedStripLift p

/-- A named product decomposition of the affine central band supplies exactly the
`bandHomotopyEquiv` field of the central-height radial input.  The decomposition is data, so the
fibre coordinate of the resulting homotopy equivalence is the one carried by that data. -/
public noncomputable def SectionSevenAffineCentralBandProductTrivialization.bandHomotopyEquiv
    {S : A.SectionSevenAffineCentralSeparation}
    (e : centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper ≃ₜ
      sectionSevenAffineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper ≃ₕ
      AdditiveTorus A.duplicatedSectionSevenBandParameter := by
  let _ : ContractibleSpace sectionSevenAffineVerticalStrip :=
    sectionSevenAffineVerticalStripContractible
  exact homotopyEquivFiberOfTrivialBundle e

/-- The named marked product decomposition gives the concrete central band equivalence used by
the radial realization.  Its forward map is the marked fibre coordinate of the affine central
band relative to `sectionSevenAffineNamedStripLift`. -/
public noncomputable def sectionSevenAffineCentralBandHomotopyEquiv
    (S : A.SectionSevenAffineCentralSeparation) :
    centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper ≃ₕ
      AdditiveTorus A.duplicatedSectionSevenBandParameter :=
  SectionSevenAffineCentralBandProductTrivialization.bandHomotopyEquiv A
    (A.sectionSevenAffineCentralBandMarkedProductHomeomorph S)

end SphereSixComplex.Geometry.PaperAnalyticData
