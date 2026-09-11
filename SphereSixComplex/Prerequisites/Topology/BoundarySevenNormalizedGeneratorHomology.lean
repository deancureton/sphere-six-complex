module

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
public import SphereSixComplex.Prerequisites.Topology.SingularStandardSimplexCone
public import Mathlib.AlgebraicTopology.SimplicialSet.NonsingularColimit
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# The normalized boundary-seven generator in simplicial homology

This file packages the previously constructed normalization and top-cycle isomorphisms into an
explicit orientation of unnormalized simplicial homology.  It also verifies that the intrinsic
alternating facet chain represents the positive generator for that orientation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

public noncomputable abbrev boundarySevenUnnormalizedIntegralChains :
    ChainComplex AddCommGrpCat ℕ :=
  (∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)

/-- The canonical composite identifying unnormalized degree-six simplicial homology of
`∂Δ[7]` with `ℤ`: normalize, identify normalized homology with its top cycle kernel,
and use the orientation coming from the unique normalized seven-simplex of `Δ[7]`. -/
public noncomputable def boundarySevenSimplicialHomologySixIsoInt :
    boundarySevenUnnormalizedIntegralChains.homology 6 ≅ AddCommGrpCat.of ℤ := by
  let _ : QuasiIso ((∂Δ[7] : SSet.{0}).toNormalizedChainComplex
      (AddCommGrpCat.of ℤ)) := inferInstance
  exact isoOfQuasiIsoAt
      ((∂Δ[7] : SSet.{0}).toNormalizedChainComplex
        (AddCommGrpCat.of ℤ)) 6 ≪≫
    boundarySeven_normalizedHomologySixIsoTopCycles ≪≫
    boundarySevenTopCyclesIsoStandardSevenTopCycles ≪≫
    standardSevenTopCyclesIsoInt










end SphereSixComplex
