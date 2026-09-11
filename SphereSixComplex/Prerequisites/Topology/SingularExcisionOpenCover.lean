module

public import SphereSixComplex.Prerequisites.Topology.SingularAffineSubdivisionRelativeMesh
public import SphereSixComplex.Prerequisites.Topology.SingularAffineSubdivisionSupport
public import SphereSixComplex.Prerequisites.Topology.SingularExcisionQuasiIso

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





end SphereSixComplex
