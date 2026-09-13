module

public import SphereSixComplex.Paper.Topology.PaperActualCollarMappingTorusEuler
public import SphereSixComplex.Paper.Topology.PaperCentralFamilyMayerVietorisEuler
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralFiberEuler

/-!
# Assembly of the actual Section 7 local Euler models

All central, collar, cusp-cell, and elliptic-cover models are now constructed independently.  This
file combines them.  The only input is the actual equivariant cusp central-fibre retraction; its
existence is neither assumed nor asserted here.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.AnalyticData

open CuspCollar

variable (A : AnalyticData)

/-- Assemble every local Euler model from an explicitly supplied actual cusp retraction. -/
public noncomputable def localEulerModelsOfCuspRetraction
    (R : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness) :
    A.LocalEulerModels := by
  obtain ⟨hf, he⟩ := InfiniteA2Toric.Construction.CentralFiberHomology.finite_homology_and_euler_eq_two
    A.starCuspWitness R
  let e := actualLocalCuspCentralOrbitCoreHomeomorph A.starCuspWitness R
  exact LocalEulerModels.ofCuspCentralModelAndCollarMappingTorusModels A
    R A.centralHomologyEulerModel
      (hf.homeomorph e)
      ((integralHomologyEulerCharacteristicSix_homeomorph e).symm.trans he)
      A.actualCollarCircleMappingTorusModel



/-- Assemble the seven local models using the standard phase-spread cusp retraction. -/
public noncomputable def localEulerModels :
    A.LocalEulerModels :=
  A.localEulerModelsOfCuspRetraction A.cuspCentralFiberRetractionData



end SphereSixComplex.Geometry.AnalyticData
