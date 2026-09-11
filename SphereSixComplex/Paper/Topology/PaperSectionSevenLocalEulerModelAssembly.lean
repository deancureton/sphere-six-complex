module

public import SphereSixComplex.Paper.Topology.PaperActualCollarMappingTorusEuler
public import SphereSixComplex.Paper.Topology.PaperCentralFamilyMayerVietorisEuler

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



/-- Assemble the seven local models using the standard phase-spread cusp retraction. -/
public noncomputable def localEulerModels :
    A.LocalEulerModels :=
  A.localEulerModelsOfCuspRetraction A.cuspCentralFiberRetractionData



end SphereSixComplex.Geometry.PaperAnalyticData
