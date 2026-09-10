module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineBandTrivializationDefs
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineActualCuspStripLift
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineNormalizedStripLift

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
    (A : PaperAnalyticData) (S : A.AffineCentralSeparation) :
    A.AffineCentralBandProductTrivialization S :=
  AffineCentralBandMarkedTrivialization.toProductTrivialization
    (affineCentralBandMarkedTrivialization A S)

end EstablishedSectionSevenAffineBandTopology

open EstablishedSectionSevenAffineBandTopology

variable (A : PaperAnalyticData)

/-- The affine strip lift normalized by the common peripheral marking. -/
public noncomputable def affineNamedStripLift : A.AffineStripLift :=
  A.affineNormalizedStripLift

public theorem affineNamedStripLift_apply_midpoint :
    A.affineNamedStripLift.lift affineStripMidpoint =
      A.affineNormalizedMidpoint :=
  A.affineNormalizedStripContinuousLift_midpoint

/-- The named marked product trivialization of the affine central band: the marked trivialization
of `PaperSectionSevenAffineMarkedBandTrivialization` taken at `affineNamedStripLift`.
Both coordinates are pinned — the base coordinate by
`affineCentralBandMarkedProductHomeomorph_fst` and the fibre coordinate by
`affineCentralBandMarkedProductHomeomorph_symm_toCentralFamily`. -/
public noncomputable def affineCentralBandMarkedProductHomeomorph
    (S : A.AffineCentralSeparation) :
    centralHeightBand
        (A.affineCentralHeightSplit S).height
        (A.affineCentralHeightSplit S).lower
        (A.affineCentralHeightSplit S).upper ≃ₜ
      affineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter :=
  (A.affineCentralBandProductHomeomorphOfLift S
    A.affineNamedStripLift).symm

/-- The named marked trivialization has the affine band projection as its base coordinate, so it
is in particular a witness of the unmarked product-trivialization statement. -/
public theorem affineCentralBandMarkedProductHomeomorph_fst
    (S : A.AffineCentralSeparation)
    (x : centralHeightBand
      (A.affineCentralHeightSplit S).height
      (A.affineCentralHeightSplit S).lower
      (A.affineCentralHeightSplit S).upper) :
    (A.affineCentralBandMarkedProductHomeomorph S x).1 =
      A.affineCentralBandProjection S x := by
  have hkey := A.affineCentralBandProductHomeomorphOfLift_toCentralFamily S
    A.affineNamedStripLift
    (A.affineCentralBandMarkedProductHomeomorph S x)
  rw [affineCentralBandMarkedProductHomeomorph, Homeomorph.apply_symm_apply] at hkey
  have hcoord := congrArg A.centralFamilyCoordinate hkey
  rw [A.centralFamilyCoordinate_stripLiftPoint] at hcoord
  apply Subtype.ext
  exact (congrArg (Subtype.val : regularCoordinateBase → ℂ) hcoord).symm

/-- The marking itself: the fibre coordinate of the named trivialization is the canonical
real-period coordinate of the central four-torus along the named strip lift.  This is the
property that `Exists.choose` of the unmarked statement could never supply. -/
public theorem affineCentralBandMarkedProductHomeomorph_symm_toCentralFamily
    (S : A.AffineCentralSeparation)
    (p : affineVerticalStrip ×
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    A.affineCentralBandToCentralFamily S
        ((A.affineCentralBandMarkedProductHomeomorph S).symm p) =
      A.stripLiftPoint A.affineNamedStripLift p.1 p.2 := by
  rw [affineCentralBandMarkedProductHomeomorph, Homeomorph.symm_symm]
  exact A.affineCentralBandProductHomeomorphOfLift_toCentralFamily S
    A.affineNamedStripLift p

/-- A named product decomposition of the affine central band supplies exactly the
`bandHomotopyEquiv` field of the central-height radial input.  The decomposition is data, so the
fibre coordinate of the resulting homotopy equivalence is the one carried by that data. -/
public noncomputable def AffineCentralBandProductTrivialization.bandHomotopyEquiv
    {S : A.AffineCentralSeparation}
    (e : centralHeightBand
        (A.affineCentralHeightSplit S).height
        (A.affineCentralHeightSplit S).lower
        (A.affineCentralHeightSplit S).upper ≃ₜ
      affineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    centralHeightBand
        (A.affineCentralHeightSplit S).height
        (A.affineCentralHeightSplit S).lower
        (A.affineCentralHeightSplit S).upper ≃ₕ
      AdditiveTorus A.duplicatedSectionSevenBandParameter := by
  let _ : ContractibleSpace affineVerticalStrip :=
    affineVerticalStrip_contractibleSpace
  exact homotopyEquivFiberOfTrivialBundle e

/-- The named marked product decomposition gives the concrete central band equivalence used by
the radial realization.  Its forward map is the marked fibre coordinate of the affine central
band relative to `affineNamedStripLift`. -/
public noncomputable def affineCentralBandHomotopyEquiv
    (S : A.AffineCentralSeparation) :
    centralHeightBand
        (A.affineCentralHeightSplit S).height
        (A.affineCentralHeightSplit S).lower
        (A.affineCentralHeightSplit S).upper ≃ₕ
      AdditiveTorus A.duplicatedSectionSevenBandParameter :=
  AffineCentralBandProductTrivialization.bandHomotopyEquiv A
    (A.affineCentralBandMarkedProductHomeomorph S)

end SphereSixComplex.Geometry.PaperAnalyticData
