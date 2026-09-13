module

public import SphereSixComplex.Paper.Topology.SectionSevenLocalEulerModels

/-!
# Reduced elliptic central-fibre covering API

Compatibility re-export of the explicit reduced-central-fibre covering constructions and the
Section Seven local-model constructor.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

namespace Geometry.AnalyticData.LocalEulerModels

open CuspCollar
open EllipticFilling

variable (A : AnalyticData)

/-- Supply direct central homology and Euler data together with the actual collars' explicit
circle mapping-torus models. -/
public noncomputable def ofCuspCentralModelAndCollarMappingTorusModels
    (cuspRetraction : ActualLocalCuspCentralFiberRetractionData A.starCuspWitness)
    (centralModel : CentralHomologyEulerModel A.openEmbeddingStarData.central)
    (cuspHomologyFinite : IntegralHomologyFiniteSix
      (cuspRetraction.quotientCentralFiber A.starCuspWitness))
    (cuspEuler_eq_two : integralHomologyEulerCharacteristicSix
      (cuspRetraction.quotientCentralFiber A.starCuspWitness) = 2)
    (collarMappingTorus : ∀ i : Fin 3, FourTorusCircleMappingTorusModel
      (A.openEmbeddingStarData.collarSource i)) :
    A.LocalEulerModels where
  cuspRetraction := cuspRetraction
  orderThreeRadialChart := orderThreeSelectedAffineRadialCompatibility A
  orderFourRadialChart := orderFourSelectedAffineRadialCompatibility A
  centralModel := centralModel
  cuspHomologyFinite := cuspHomologyFinite
  cuspEuler_eq_two := cuspEuler_eq_two
  collarModel := collarMappingTorus

end Geometry.AnalyticData.LocalEulerModels

end SphereSixComplex

end

end
