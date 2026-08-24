module

public import SphereSixComplex.Geometry.CuspAnalyticFillingCollar
public import SphereSixComplex.Geometry.EllipticAnalyticFillingCollars
public import SphereSixComplex.Geometry.PaperOpenEmbeddingStarNonempty
public import SphereSixComplex.Geometry.PaperStarComplexStructures

/-!
# The concrete biholomorphic four-piece star

This packages the cusp and two elliptic analytic collar identifications at the simultaneously
separated radii.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry

open CuspAnalyticFillingCollar CuspAnalyticFillingCollar.PaperAnalyticData
open CuspPuncturedCollarBridge

noncomputable section

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- The cusp, order-three, and order-four analytic collar identifications. -/
@[expose] public noncomputable def starCollarPartialDiffeomorph :
    letI := A.starCentralCharts
    letI (i : Fin 3) := A.starFillingCharts i
    ∀ i, PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) A.CentralFamily
      (A.starFillingType i) ∞ := by
  let _ := A.starCentralCharts
  let _ (i : Fin 3) := A.starFillingCharts i
  refine Fin.cases
    (actualPuncturedCuspCollarPartialDiffeomorph A A.starCuspWitness) ?_
  intro i
  refine Fin.cases
    (A.orderThreeFillingCollarPartialDiffeomorph A.starSeparation.orderThree) ?_ i
  intro _
  exact A.orderFourFillingCollarPartialDiffeomorph A.starSeparation.orderFour

public theorem starCollarPartialDiffeomorph_source (i : Fin 3) :
    letI := A.starCentralCharts
    letI (i : Fin 3) := A.starFillingCharts i
    ((A.starCollarPartialDiffeomorph i).source :
      Set ↑A.openEmbeddingStarData.central) =
      (A.openEmbeddingStarData.centralCollar i :
        Set ↑A.openEmbeddingStarData.central) := by
  let _ := A.starCentralCharts
  let _ (i : Fin 3) := A.starFillingCharts i
  fin_cases i
  · change
      (actualPuncturedCuspCollarPartialDiffeomorph A A.starCuspWitness).source =
        Set.range (puncturedLocalCuspQuotientMap A.starCuspWitness)
    rw [actualPuncturedCuspCollarPartialDiffeomorph_source]
    exact (puncturedLocalCuspQuotientMap_range A.starCuspWitness).symm
  · exact A.orderThreeFillingCollarPartialDiffeomorph_source
      A.starSeparation.orderThree
  · exact A.orderFourFillingCollarPartialDiffeomorph_source
      A.starSeparation.orderFour

public theorem starCollarPartialDiffeomorph_target (i : Fin 3) :
    letI := A.starCentralCharts
    letI (i : Fin 3) := A.starFillingCharts i
    ((A.starCollarPartialDiffeomorph i).target :
      Set ↑(A.openEmbeddingStarData.filling i)) =
      (A.openEmbeddingStarData.fillingCollar i :
        Set ↑(A.openEmbeddingStarData.filling i)) := by
  let _ := A.starCentralCharts
  let _ (i : Fin 3) := A.starFillingCharts i
  fin_cases i
  · exact actualPuncturedCuspCollarPartialDiffeomorph_target
      A A.starCuspWitness
  · exact A.orderThreeFillingCollarPartialDiffeomorph_target
      A.starSeparation.orderThree
  · exact A.orderFourFillingCollarPartialDiffeomorph_target
      A.starSeparation.orderFour

public theorem starCollarPartialDiffeomorph_apply (i : Fin 3)
    (x : A.starCollarSourceType i) :
    letI := A.starCentralCharts
    letI (i : Fin 3) := A.starFillingCharts i
    A.starCollarPartialDiffeomorph i (A.starToCentral i x) =
      A.starToFilling i x := by
  let _ := A.starCentralCharts
  let _ (i : Fin 3) := A.starFillingCharts i
  fin_cases i
  · exact actualPuncturedCuspCollarPartialDiffeomorph_apply
      A A.starCuspWitness x
  · exact A.orderThreeFillingCollarPartialDiffeomorph_apply
      A.starSeparation.orderThree x
  · exact A.orderFourFillingCollarPartialDiffeomorph_apply
      A.starSeparation.orderFour x

/-- The concrete open-embedding star with its analytic collar identifications. -/
public noncomputable def openEmbeddingStarBiholomorphicData :
    A.openEmbeddingStarData.BiholomorphicData where
  centralCharts := A.starCentralCharts
  fillingCharts := A.starFillingCharts
  centralManifold := A.starCentral_isManifold
  fillingManifold := A.starFilling_isManifold
  collar := A.starCollarPartialDiffeomorph
  collar_source := A.starCollarPartialDiffeomorph_source
  collar_target := A.starCollarPartialDiffeomorph_target
  collar_toCentral := A.starCollarPartialDiffeomorph_apply

/-- The paper's four-piece star in the generic biholomorphic gluing interface. -/
public noncomputable def biholomorphicFourPieceStarData :=
  A.openEmbeddingStarBiholomorphicData.toBiholomorphicFourPieceStarData

end PaperAnalyticData

end

end SphereSixComplex.Geometry
