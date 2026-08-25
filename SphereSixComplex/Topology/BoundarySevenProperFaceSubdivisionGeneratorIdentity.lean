module

public import SphereSixComplex.Topology.BoundarySevenProperFaceSubdivisionIso
public import SphereSixComplex.Topology.BoundarySevenSubdivisionGeneratorTransportPrelude

/-!
# The boundary-seven generator under the proper-face subdivision isomorphism

The canonical barycentric subdivision of the intrinsic boundary generator becomes exactly the
intrinsic proper-face fundamental chain.  Both chains were already known to become the explicit
subdivided boundary chain after the literal inclusion of the proper-face nerve; injectivity of
that inclusion on degree-six chains permits cancellation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Simplicial

namespace SphereSixComplex

/-- Canonical barycentric subdivision followed by the proper-face comparison sends the
intrinsic alternating boundary generator exactly to the intrinsic proper-face generator. -/
public theorem boundarySevenOriginalFundamentalChain_subdivisionToProperFace :
    (boundarySevenOriginalFundamentalChain ≫
        (barycentricSubdivisionChainMapCanonical
          (∂Δ[7] : SSet.{0})).f 6) ≫
      (SSet.chainComplexMap boundarySevenSubdivisionToProperFaceNerve
        (AddCommGrpCat.of ℤ)).f 6 =
    boundarySevenProperFaceFundamentalChain := by
  let I := (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
    (AddCommGrpCat.of ℤ)).f 6
  let _ : Mono I :=
    boundarySevenProperFaceNerveInclusion_chainComplexMap_f_mono 6
  apply (cancel_mono I).1
  calc
    ((boundarySevenOriginalFundamentalChain ≫
          (barycentricSubdivisionChainMapCanonical
            (∂Δ[7] : SSet.{0})).f 6) ≫
        (SSet.chainComplexMap boundarySevenSubdivisionToProperFaceNerve
          (AddCommGrpCat.of ℤ)).f 6) ≫ I =
        subdividedSevenBoundaryFundamentalChain :=
      boundarySevenOriginalFundamentalChain_subdivisionToProperFace_comp_inclusion
    _ = boundarySevenProperFaceFundamentalChain ≫ I :=
      boundarySevenProperFaceFundamentalChain_comp_inclusion.symm

end SphereSixComplex
