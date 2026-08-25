module

public import SphereSixComplex.Topology.SingularAffineSubdivisionRelativeMesh
public import SphereSixComplex.Topology.SingularAffineSubdivisionSupport
public import SphereSixComplex.Topology.SingularExcisionQuasiIso

/-!
# Small-chain approximation for open covers

This file assembles the geometric affine-mesh theorem, the exact permutation-ancestry expansion,
the adaptive quasi-isomorphism argument, and projectivity.  The result is the classical
small-singular-chain theorem for every open cover, with no additional hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace SphereSixComplex

variable {ι : Type} (X : TopCat) (U : ι → Set X)

/-- Every finite singular chain becomes subordinate to an open cover after sufficiently many
genuine affine barycentric subdivisions. -/
public theorem coverSmallAffineSubdivisionEventuallySmall_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    CoverSmallAffineSubdivisionEventuallySmall X U :=
  coverSmallAffineSubdivisionEventuallySmall_of_relativeMesh X U hUopen hUcover
    (fun n _ ↦ affineFlagRelativeMeshContraction n)

/-- The cover-small inclusion is a quasi-isomorphism for every open cover. -/
public theorem coverSmallChainQuasiIsomorphism_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    CoverSmallChainQuasiIsomorphism X U :=
  coverSmallChainQuasiIsomorphism_of_eventuallySmall X U
    (coverSmallAffineSubdivisionEventuallySmall_of_openCover X U hUopen hUcover)

/-- Classical small-chain approximation: the inclusion of chains subordinate to an open cover is
a chain-homotopy equivalence for integral singular chains. -/
public theorem coverSmallChainApproximation_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    CoverSmallChainApproximation X U :=
  coverSmallChainApproximation_of_eventuallySmall X U
    (coverSmallAffineSubdivisionEventuallySmall_of_openCover X U hUopen hUcover)

/-- The concrete two-set cover of the seven-disk now satisfies the formerly missing small-chain
approximation theorem unconditionally. -/
public theorem diskSevenSmallChainApproximation :
    DiskSevenSmallChainApproximation :=
  coverSmallChainApproximation_of_openCover
    (TopCat.disk.{0} 7) diskSevenExcisionCover diskSevenExcisionCover_isOpen
      diskSevenExcisionCover_iUnion

/-- Equivalently, the cover-small inclusion for the concrete disk cover is a quasi-isomorphism. -/
public theorem diskSevenSmallChainQuasiIsomorphism :
    DiskSevenSmallChainQuasiIsomorphism :=
  coverSmallChainQuasiIsomorphism_of_openCover
    (TopCat.disk.{0} 7) diskSevenExcisionCover diskSevenExcisionCover_isOpen
      diskSevenExcisionCover_iUnion

end SphereSixComplex
