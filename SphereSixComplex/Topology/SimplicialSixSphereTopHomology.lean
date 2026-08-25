module

public import SphereSixComplex.Topology.SixSphereDegreeComparison
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

public noncomputable abbrev BoundarySevenNormalizedIntegralChains :
    ChainComplex AddCommGrpCat ℕ :=
  (∂Δ[7] : SSet.{0}).normalizedChainComplex (AddCommGrpCat.of ℤ)

/-- The precise finite integer-matrix calculation left for top homology: the kernel of the
normalized boundary map from the eight oriented facets is infinite cyclic. -/
public def BoundarySevenNormalizedTopCyclesOrientation : Prop :=
  Nonempty ((kernel (BoundarySevenNormalizedIntegralChains.d 6 5) :
    AddCommGrpCat) ≃+ ℤ)

/-- The normalized complex has no incoming group in degree six. -/
public theorem boundarySeven_normalizedChains_degreeSeven_isZero :
    IsZero (BoundarySevenNormalizedIntegralChains.X 7) :=
  (∂Δ[7] : SSet.{0}).isZero_normalizedChainComplex_X_of_hasDimensionLT
    (AddCommGrpCat.of ℤ) 7 7

/-- Consequently, normalized degree-six homology is the kernel of its outgoing differential. -/
public noncomputable def boundarySeven_normalizedHomologySixIsoTopCycles :
    BoundarySevenNormalizedIntegralChains.homology 6 ≅
      kernel (BoundarySevenNormalizedIntegralChains.d 6 5) := by
  let K := BoundarySevenNormalizedIntegralChains
  let S := K.sc' 7 6 5
  have hf : S.f = 0 :=
    boundarySeven_normalizedChains_degreeSeven_isZero.eq_of_src _ _
  exact K.homologyIsoSc' 7 6 5 (by simp) (by simp) ≪≫
    (S.asIsoHomologyπ hf).symm ≪≫ S.cyclesIsoKernel

/-- The finite normalized kernel calculation supplies the combinatorial top generator. -/
public theorem boundarySevenSimplicialTopHomologyOrientation_of_normalizedCycles
    (h : BoundarySevenNormalizedTopCyclesOrientation) :
    BoundarySevenSimplicialTopHomologyOrientation := by
  obtain ⟨orientation⟩ := h
  let _ : QuasiIso ((∂Δ[7] : SSet.{0}).toNormalizedChainComplex
      (AddCommGrpCat.of ℤ)) := inferInstance
  let normalizationIso := isoOfQuasiIsoAt
    ((∂Δ[7] : SSet.{0}).toNormalizedChainComplex (AddCommGrpCat.of ℤ)) 6
  exact ⟨normalizationIso.addCommGroupIsoToAddEquiv.trans
    (boundarySeven_normalizedHomologySixIsoTopCycles.addCommGroupIsoToAddEquiv.trans
      orientation)⟩

end SphereSixComplex
