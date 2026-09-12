module

public import SphereSixComplex.Paper.Topology.PaperActualAffineFillingCoverModels
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

/-- The selected filling twists kill the fundamental group of the actual glued star. -/
public theorem star_simplyConnectedSpace :
    SimplyConnectedSpace
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) := by
  let X := P.compactComplexStar.toComplexThreefold
  let : ConnectedSpace P.VanKampenSpace := X.connected
  let : ChartedSpace ComplexModel P.VanKampenSpace := X.charts
  let : LocallyPathConnectedSpace P.VanKampenSpace :=
    ChartedSpace.locallyPathConnectedSpace ComplexModel P.VanKampenSpace
  let : PathConnectedSpace P.VanKampenSpace := PathConnectedSpace.of_locallyPathConnectedSpace
  exact P.actualStarHasVanKampenData.simplyConnectedSpace

/-- The Mayer--Vietoris calculation gives the integral homology of the six-sphere. -/
public theorem star_nonempty_homologyEquiv_sixSphere :
    ∀ k, Nonempty
      (IntegralSingularHomology k
        (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) ≃+
      IntegralSingularHomology k SixSphere) := by
  let R := P.affineRadialCompletionInput
  exact P.star_nonempty_homologyEquiv_sixSphere_of_positiveDegree
    (CuspAttachment.correctedPositiveDegreeAssembly R)

end SphereSixComplex.Geometry.AnalyticData
