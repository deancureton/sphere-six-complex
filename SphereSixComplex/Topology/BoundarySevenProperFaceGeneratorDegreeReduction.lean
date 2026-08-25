module

public import SphereSixComplex.Topology.BoundarySevenSubdivisionGeneratorTransportPrelude

/-!
# Reduction of boundary-seven degree transport to the proper-face generator

The literal inclusion of the proper-face nerve is degreewise monic.  Consequently every scalar
identity for the subdivided boundary generator pulls back to the intrinsic proper-face generator.
This file packages that fact in the exact form consumed by the degree calculation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Simplicial

namespace SphereSixComplex

/-- The remaining degree assertion expressed directly using the generator of the proper-face
nerve whose affine realization is already an explicit homeomorphism. -/
public def BoundarySevenProperFaceGeneratorDegreeTransport
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) : Prop :=
  ∀ (sigma : Equiv.Perm (Fin 8)) (z : ℤ),
    boundarySevenProperFaceFundamentalChain ≫
        (SSet.chainComplexMap (boundarySevenProperFaceNervePermIso sigma).hom
          (AddCommGrpCat.of ℤ)).f 6 =
      z • boundarySevenProperFaceFundamentalChain →
    sixSphereHomologicalDegree
        (sixSphereTopHomologyAddEquivOfStandardBoundaryComparison hcomparison e)
        (boundarySevenPermutationSphereMap e sigma) = z

/-- Proper-face generator transport implies the earlier subdivision-generator transport without
any additional geometric assumption. -/
public theorem boundarySevenSubdivisionGeneratorDegreeTransport_of_properFace
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere)
    (hproper : BoundarySevenProperFaceGeneratorDegreeTransport hcomparison e) :
    BoundarySevenSubdivisionGeneratorDegreeTransport hcomparison e := by
  intro sigma z hsubdivided
  exact hproper sigma z
    (boundarySevenProperFaceFundamentalChain_eq_zsmul_of_subdivided
      sigma z hsubdivided)

end SphereSixComplex
