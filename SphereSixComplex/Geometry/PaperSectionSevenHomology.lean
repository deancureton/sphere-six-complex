module

public import SphereSixComplex.Geometry.PaperGluingInstantiation
public import SphereSixComplex.Topology.PaperSectionSevenHomologyAssembly
public import SphereSixComplex.Topology.PaperSectionSevenLocalEulerModelAssembly
public import SphereSixComplex.Topology.SectionSevenMayerVietorisEuler
public import SphereSixComplex.Topology.SectionSevenLocalEulerModels

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
    EstablishedBiholomorphicStarGluing.establishedFourPieceBiholomorphicGluingAtlasCompatible
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
      hCentralFinite hFillingFinite hCollarFinite hLocal

/-- Geometric local CW, bundle, cover, and retraction models discharge every finiteness and
Euler-characteristic input in the Section 7 homology calculation. -/
public theorem star_hasIntegralHomologyOfSixSphere_of_localModels
    (H : P.openEmbeddingStarData.SectionSevenMayerVietorisHomologyAssembly)
    (M : P.SectionSevenLocalEulerModels) :
    HasIntegralHomologyOfSixSphere
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) := by
  obtain ⟨hCentral, hFilling, hCollar⟩ := M.localIntegralHomologyFiniteSix
  exact P.star_hasIntegralHomologyOfSixSphere H hCentral hFilling hCollar
    M.sectionSevenLocalEulerExpression_eq_two

/-- Once the actual Mayer--Vietoris map bases and van Kampen calculation are supplied, the
geometric local models assemble directly into the paper's complete gluing package. -/
@[expose] public noncomputable def toPaperGluingData_of_sectionSevenLocalModels
    (vanKampen : Topology.HasVanKampenData
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) 0 1 (-1))
    (H : P.openEmbeddingStarData.SectionSevenMayerVietorisHomologyAssembly)
    (M : P.SectionSevenLocalEulerModels) : SphereSixComplex.PaperGluingData :=
  P.toPaperGluingData vanKampen
    (P.star_hasIntegralHomologyOfSixSphere_of_localModels H M)

/-- Assemble the paper gluing package while obtaining the final degree-zero Mayer--Vietoris data
from the actual analytic star rather than from an input. -/
public noncomputable def toPaperGluingData_of_positiveDegreeAndLocalModels
    (vanKampen : Topology.HasVanKampenData
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) 0 1 (-1))
    (H : P.SectionSevenPositiveDegreeHomologyAssembly)
    (M : P.SectionSevenLocalEulerModels) : SphereSixComplex.PaperGluingData :=
  P.toPaperGluingData_of_sectionSevenLocalModels vanKampen
    H.toSectionSevenMayerVietorisHomologyAssembly M

/-- The completed local topology is inserted automatically; only the positive-degree
Mayer--Vietoris calculation and van Kampen datum remain. -/
public noncomputable def toPaperGluingData_of_positiveDegree
    (vanKampen : Topology.HasVanKampenData
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) 0 1 (-1))
    (H : P.SectionSevenPositiveDegreeHomologyAssembly) : SphereSixComplex.PaperGluingData :=
  P.toPaperGluingData_of_positiveDegreeAndLocalModels vanKampen H
    P.sectionSevenLocalEulerModels

end PaperAnalyticData

end

end SphereSixComplex.Geometry
