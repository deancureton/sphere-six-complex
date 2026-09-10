module

public import SphereSixComplex.Paper.Topology.PaperActualCollarMappingTorusEuler
public import SphereSixComplex.Paper.Topology.PaperCentralFamilyMayerVietorisEuler
public import SphereSixComplex.Paper.Topology.PaperCuspCentralFiberCWModel
public import SphereSixComplex.Paper.Topology.PaperCuspPhaseSpreading

/-!
# Assembly of the actual Section 7 local Euler models

All central, collar, cusp-cell, and elliptic-cover models are now constructed independently.  This
file combines them.  The only input is the actual equivariant cusp central-fibre retraction; its
existence is neither assumed nor asserted here.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge

variable (A : PaperAnalyticData)

/-- Assemble every local Euler model from an explicitly supplied actual cusp retraction. -/
public noncomputable def localEulerModelsOfCuspRetraction
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness) :
    A.LocalEulerModels :=
  LocalEulerModels.ofCuspCentralModelAndCollarMappingTorusModels A
    R A.centralHomologyEulerModel
      (actualCuspCentralFiberCellModel A.starCuspWitness R)
      A.actualCollarCircleMappingTorusModel

/-- The assembled local models give finite integral homology for all seven local spaces. -/
public theorem localIntegralHomologyFiniteSix_of_cuspRetraction
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness) :
    IntegralHomologyFiniteSix A.openEmbeddingStarData.central ∧
      (∀ i : Fin 3, IntegralHomologyFiniteSix (A.openEmbeddingStarData.filling i)) ∧
      (∀ i : Fin 3, IntegralHomologyFiniteSix
        (A.openEmbeddingStarData.collarSource i)) :=
  (A.localEulerModelsOfCuspRetraction R).localIntegralHomologyFiniteSix

/-- The exact local Euler expression is two once the explicit actual cusp retraction is supplied. -/
public theorem localEulerExpression_eq_two_of_cuspRetraction
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness) :
    A.openEmbeddingStarData.sectionSevenLocalEulerExpression = 2 :=
  (A.localEulerModelsOfCuspRetraction R).sectionSevenLocalEulerExpression_eq_two

/-- Assemble the seven local models using the standard phase-spread cusp retraction. -/
public noncomputable def localEulerModels :
    A.LocalEulerModels :=
  A.localEulerModelsOfCuspRetraction A.cuspCentralFiberRetractionData

/-- All seven local spaces have finite integral homology. -/
public theorem localIntegralHomologyFiniteSix :
    IntegralHomologyFiniteSix A.openEmbeddingStarData.central ∧
      (∀ i : Fin 3, IntegralHomologyFiniteSix (A.openEmbeddingStarData.filling i)) ∧
      (∀ i : Fin 3, IntegralHomologyFiniteSix
        (A.openEmbeddingStarData.collarSource i)) :=
  A.localIntegralHomologyFiniteSix_of_cuspRetraction
    A.cuspCentralFiberRetractionData

/-- The unconditional local Section 7 Euler expression is two. -/
public theorem localEulerExpression_eq_two :
    A.openEmbeddingStarData.sectionSevenLocalEulerExpression = 2 :=
  A.localEulerExpression_eq_two_of_cuspRetraction
    A.cuspCentralFiberRetractionData

end SphereSixComplex.Geometry.PaperAnalyticData
