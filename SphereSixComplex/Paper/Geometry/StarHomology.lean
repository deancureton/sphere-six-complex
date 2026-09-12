module

public import SphereSixComplex.Paper.Geometry.PaperGluingInstantiation
public import SphereSixComplex.Paper.Topology.PaperSectionSevenLocalEulerModelAssembly
public import SphereSixComplex.Paper.Topology.SectionSevenMayerVietorisEuler
public import SphereSixComplex.Prerequisites.Topology.ComplexThreefoldHomology

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.AnalyticData

open OpenEmbeddingStarData

/-- Vanishing first and second homology, together with the geometric Euler calculation,
identifies the integral homology of the glued threefold with that of the six-sphere. -/
public theorem star_nonempty_homologyEquiv_sixSphere_of_lowDegrees (P : AnalyticData)
    (hOne : Subsingleton (IntegralSingularHomology 1
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData)))
    (hTwo : Subsingleton (IntegralSingularHomology 2
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData))) :
    ∀ k, Nonempty (IntegralSingularHomology k
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) ≃+
      IntegralSingularHomology k SixSphere) := by
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
  let _ : T2Space (GluedSpace D) := P.t2Space_starGlued
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
  let := hManifold
  let := hConnected
  let := P.compactSpace_starGlued
  let T := ComplexThreefold.integralPoincareUCT (GluedSpace D)
    hManifold P.compactSpace_starGlued
  obtain ⟨hCentral, hFilling, hCollar⟩ := P.localEulerModels.localIntegralHomologyFiniteSix
  have hEuler : integralHomologyEulerCharacteristicSix (GluedSpace D) = 2 := by
    rw [integralHomologyEulerCharacteristicSix_eq_localExpression_of_homologySeven_subsingleton
      P.openEmbeddingStarData (T.subsingleton_homology_of_lt 7 (by omega)) hCentral hFilling hCollar]
    exact P.localEulerModels.sectionSevenLocalEulerExpression_eq_two
  exact ComplexThreefold.nonempty_homologyEquiv_sixSphere (GluedSpace D) hOne hTwo hEuler

end SphereSixComplex.Geometry.AnalyticData
