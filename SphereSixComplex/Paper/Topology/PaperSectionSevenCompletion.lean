module

public import SphereSixComplex.Paper.Topology.CuspFundamentalGroup
public import SphereSixComplex.Prerequisites.Topology.SixSphereHomology
public import SphereSixComplex.Paper.Topology.EstablishedPaperSectionSevenAffineCompletion
public import SphereSixComplex.Paper.Topology.EstablishedPaperSectionSevenCuspCompletion

/-!
# Topology of the glued analytic threefold

The fundamental group and homology computations concern the same geometric glued carrier.
-/

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.AnalyticData

variable (P : AnalyticData)

/-- The Mayer--Vietoris calculation gives the integral homology of the six-sphere. -/
public theorem star_nonempty_homologyEquiv_sixSphere :
    ∀ k, Nonempty
      (IntegralSingularHomology k
        (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) ≃+
      IntegralSingularHomology k SixSphere) := by
  let R := P.affineRadialCompletionInput
  exact P.star_nonempty_homologyEquiv_sixSphere_of_positiveDegree
    (CuspAttachment.correctedPositiveDegreeAssembly R)

/-- The cusp relations make the fundamental group abelian, and vanishing first homology kills it. -/
public theorem star_simplyConnectedSpace :
    SimplyConnectedSpace
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) := by
  obtain ⟨e⟩ := P.star_nonempty_homologyEquiv_sixSphere 1
  have : Subsingleton (IntegralSingularHomology 1 SixSphere) :=
    sixSpherePositiveHomologyInputs.otherDegrees 1 (by decide) (by decide)
  have : Subsingleton (IntegralSingularHomology 1 P.VanKampenSpace) :=
    ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩
  exact P.star_simplyConnectedSpace_of_homologyOne_subsingleton P.cuspCentralNaturality

end SphereSixComplex.Geometry.AnalyticData
