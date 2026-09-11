module

public import SphereSixComplex.Prerequisites.Topology.BoundarySevenNormalizedGeneratorHomology
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.NonsingularColimit
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import SphereSixComplex.Prerequisites.Topology.SingularBarycentricOuterFaces
public import Mathlib.GroupTheory.Perm.Sign
public import SphereSixComplex.Prerequisites.Topology.SmoothRecognition
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import SphereSixComplex.Prerequisites.Topology.SimplicialSixSphereTopHomologyKernel
public import SphereSixComplex.Prerequisites.Topology.BoundarySevenRealizationInjective
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import SphereSixComplex.Prerequisites.Topology.SingularAffineSubdivision
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.Data.Finset.Sort
public import SphereSixComplex.Prerequisites.Topology.SingularStandardSimplexCone
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import SphereSixComplex.Prerequisites.Topology.SingularAffineSubdivisionPrism
public import Mathlib.Algebra.Group.Int.Units

/-!
# Degree transport from the proper-face generator

This file closes the generator-transport reduction.  First it strengthens the ambient affine
chain identity to singular chains in the ordinary simplex boundary.  It then transports the
explicit normalized orientation through that identity and proves the proper-face degree formula.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits ContinuousMap Opposite PartialOrder
  Simplicial

namespace SphereSixComplex






/-! ## Homology classes represented by explicit cycles -/












/-! ## The explicit sphere orientation and degree -/


/-- The chain-complex isomorphism induced by the canonical realization homeomorphism to the
ordinary affine boundary. -/
public noncomputable def boundarySevenRealizationSingularChainIso :
    (TopCat.toSSet.obj (SSet.toTop.obj (∂Δ[7] : SSet.{0}))).chainComplex
        (AddCommGrpCat.of ℤ) ≅
      (TopCat.toSSet.obj
        (TopCat.of (StandardSimplexBoundary 7))).chainComplex
          (AddCommGrpCat.of ℤ) :=
  ((SSet.chainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).mapIso
      (TopCat.toSSet.mapIso
        (TopCat.isoOfHomeo
          (boundarySevenRealizationHomeomorphStandardBoundary_of_injective
            boundarySevenRealizationToBoundary_injective)))

/-- The singular chain-complex isomorphism induced by a boundary--sphere homeomorphism. -/
public noncomputable def boundarySevenBoundarySphereSingularChainIso
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    (TopCat.toSSet.obj
        (TopCat.of (StandardSimplexBoundary 7))).chainComplex
          (AddCommGrpCat.of ℤ) ≅
      (TopCat.toSSet.obj (TopCat.of SixSphere)).chainComplex
        (AddCommGrpCat.of ℤ) :=
  ((SSet.chainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).mapIso
      (TopCat.toSSet.mapIso (TopCat.isoOfHomeo e))

/-- The fully explicit top-homology orientation of the standard sphere obtained from the
normalized simplicial generator, the comparison map, and the selected boundary model. -/
public noncomputable def boundarySevenExplicitSphereHomologyIsoInt
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    ((TopCat.toSSet.obj (TopCat.of SixSphere)).chainComplex
      (AddCommGrpCat.of ℤ)).homology 6 ≅ AddCommGrpCat.of ℤ := by
  let _ : QuasiIso (simplicialToRealizationSingularChainMap
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) := hcomparison
  let comparisonIso := isoOfQuasiIsoAt
    (simplicialToRealizationSingularChainMap
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) 6
  let realizationIso := HomologicalComplex.homologyMapIso
    boundarySevenRealizationSingularChainIso 6
  let sphereIso := HomologicalComplex.homologyMapIso
    (boundarySevenBoundarySphereSingularChainIso e) 6
  exact (comparisonIso.trans realizationIso |>.trans sphereIso).symm ≪≫
    boundarySevenSimplicialHomologySixIsoInt

/-- The additive equivalence underlying the explicit sphere orientation. -/
public noncomputable def boundarySevenExplicitSphereHomologyAddEquivInt
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    IntegralSingularHomology 6 SixSphere ≃+ ℤ :=
  (boundarySevenExplicitSphereHomologyIsoInt hcomparison e).addCommGroupIsoToAddEquiv







end SphereSixComplex
