module

public import SphereSixComplex.Prerequisites.Topology.SimplicialSingularComparison
public import SphereSixComplex.Prerequisites.Topology.SmoothRecognition
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

/-!
# Top homology of the combinatorial six-sphere: finite reduction

The unnormalized simplicial chain complex contains degenerate simplices in every degree.  Mathlib's
normalization theorem removes them by a chain-homotopy equivalence.  Since `∂Δ[7]` has dimension
strictly below seven, its normalized degree-seven group vanishes, so degree-six homology is exactly
the kernel of its one finite differential `C₆ → C₅`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

public noncomputable abbrev boundarySevenNormalizedIntegralChains :
    ChainComplex AddCommGrpCat ℕ :=
  (∂Δ[7] : SSet.{0}).normalizedChainComplex (AddCommGrpCat.of ℤ)


/-- The normalized complex has no incoming group in degree six. -/
public theorem boundarySeven_normalizedChains_degreeSeven_isZero :
    IsZero (boundarySevenNormalizedIntegralChains.X 7) :=
  (∂Δ[7] : SSet.{0}).isZero_normalizedChainComplex_X_of_hasDimensionLT
    (AddCommGrpCat.of ℤ) 7 7

/-- Consequently, normalized degree-six homology is the kernel of its outgoing differential. -/
public noncomputable def boundarySeven_normalizedHomologySixIsoTopCycles :
    boundarySevenNormalizedIntegralChains.homology 6 ≅
      kernel (boundarySevenNormalizedIntegralChains.d 6 5) := by
  let K := boundarySevenNormalizedIntegralChains
  let S := K.sc' 7 6 5
  have hf : S.f = 0 :=
    boundarySeven_normalizedChains_degreeSeven_isZero.eq_of_src _ _
  exact K.homologyIsoSc' 7 6 5 (by simp) (by simp) ≪≫
    (S.asIsoHomologyπ hf).symm ≪≫ S.cyclesIsoKernel


end SphereSixComplex
