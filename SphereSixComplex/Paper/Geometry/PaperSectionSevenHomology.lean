module

public import SphereSixComplex.Paper.Geometry.PaperGluingInstantiation
public import SphereSixComplex.Paper.Topology.PaperSectionSevenHomologyAssembly
public import SphereSixComplex.Paper.Topology.PaperSectionSevenLocalEulerModelAssembly
public import SphereSixComplex.Paper.Topology.SectionSevenMayerVietorisEuler
public import SphereSixComplex.Paper.Topology.SectionSevenLocalEulerModels

/-!
# Section 7 homology for the analytic star

This file supplies the geometric manifold instances of the actual analytic star to the
source-faithful Mayer--Vietoris homology calculation.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry

noncomputable section

namespace PaperAnalyticData

variable (P : PaperAnalyticData)

/-- The Section 7 map calculation and the seven local Euler calculations give the integral
homology of the standard six-sphere for the actual analytic star. -/
public theorem star_hasIntegralHomologyOfSixSphere
    (H : P.openEmbeddingStarData.SectionSevenMayerVietorisHomologyAssembly)
    (hCentralFinite : IntegralHomologyFiniteSix P.openEmbeddingStarData.central)
    (hFillingFinite : ∀ i,
      IntegralHomologyFiniteSix (P.openEmbeddingStarData.filling i))
    (hCollarFinite : ∀ i,
      IntegralHomologyFiniteSix (P.openEmbeddingStarData.collarSource i))
    (hTop : P.openEmbeddingStarData.SectionSevenStageTopDegreeVanishing)
    (hLocal : P.openEmbeddingStarData.sectionSevenLocalEulerExpression = 2) :
    HasIntegralHomologyOfSixSphere
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) := by
  let A := P.openEmbeddingStarData.toFourPieceStarGluingData
  let D := A.glueData
  let _ : Finite D.J := by
    change Finite (Option (Fin 3))
    infer_instance
  let _ : Nonempty D.J := by
    change Nonempty (Option (Fin 3))
    infer_instance
  let _ := A.nonemptyPieceOfCollars P.fourPieceStarGluingData_nonemptyCentralCollar
  let _ (i : D.J) := P.starPiece_connected i
  let _ := P.biholomorphicFourPieceStarData.complexCharts
  let hComplex : GluingAtlasCompatible
      (I := modelWithCornersSelf ℂ ComplexModel) (n := ∞) D :=
    BiholomorphicStarGluing.BiholomorphicFourPieceStarData.gluing_atlas_compatible
      A P.fourPieceStarGluingData_nonemptyCentralCollar
        P.biholomorphicFourPieceStarData
  let _ : ChartedSpace ComplexModel (GluedSpace D) := gluedChartedSpace D
  let _ : T2Space (GluedSpace D) := P.starGluedT2
  let _ : Countable D.J := by
    change Countable (Option (Fin 3))
    infer_instance
  let _ (i : D.J) := P.starPiece_secondCountable i
  let _ : SecondCountableTopology (GluedSpace D) := secondCountableTopology_gluedSpace D
  let hManifold : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ (GluedSpace D) :=
    isManifold_gluedChartedSpace D hComplex
  let hConnected : ConnectedSpace (GluedSpace D) :=
    connectedSpace_gluedSpace D
      (A.intersectionGraphConnected P.fourPieceStarGluingData_nonemptyCentralCollar)
  exact H.hasIntegralHomologyOfSixSphere_of_localEulerCalculation
    (A := P.openEmbeddingStarData) hManifold P.starGluedCompact hConnected
      hCentralFinite hFillingFinite hCollarFinite hTop hLocal

/-- Geometric local CW, bundle, cover, and retraction models discharge every finiteness and
Euler-characteristic input in the Section 7 homology calculation. -/
public theorem star_hasIntegralHomologyOfSixSphere_of_localModels
    (H : P.openEmbeddingStarData.SectionSevenMayerVietorisHomologyAssembly)
    (M : P.LocalEulerModels)
    (hTop : P.openEmbeddingStarData.SectionSevenStageTopDegreeVanishing) :
    HasIntegralHomologyOfSixSphere
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) := by
  obtain ⟨hCentral, hFilling, hCollar⟩ := M.localIntegralHomologyFiniteSix
  exact P.star_hasIntegralHomologyOfSixSphere H hCentral hFilling hCollar hTop
    M.sectionSevenLocalEulerExpression_eq_two

/-- The positive-degree map computation and the proved local models compute the actual
integral homology of the glued analytic star. -/
public theorem star_nonempty_homologyEquiv_sixSphere_of_positiveDegree
    (H : P.PositiveDegreeHomologyAssembly)
    (hTop : P.openEmbeddingStarData.SectionSevenStageTopDegreeVanishing) :
    ∀ k, Nonempty
      (IntegralSingularHomology k
        (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) ≃+
      IntegralSingularHomology k SixSphere) :=
  P.star_hasIntegralHomologyOfSixSphere_of_localModels
    H.toSectionSevenMayerVietorisHomologyAssembly P.localEulerModels hTop

end PaperAnalyticData

end

end SphereSixComplex.Geometry
