module

public import SphereSixComplex.Topology.FiniteBouquetMappingTorusEuler
public import SphereSixComplex.Topology.PaperCuspGeometricSpecialization

/-!
# Euler characteristic of the three actual collar pieces

Each collar has an explicit radial mapping-torus model.  Removing the contractible radial
coordinate and applying the Wang-sequence Euler calculation proves finiteness and Euler zero
without using the abstract finite-CW bundle realization.
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open AnalyticTorusFamily EllipticFamilySpecialization
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspRadialClutchingConstruction

variable (A : PaperAnalyticData)

/-- The actual cusp collar as a circle mapping torus with four-torus fibre. -/
public noncomputable def actualCuspCollarCircleMappingTorusModel :
    FourTorusCircleMappingTorusModel (A.openEmbeddingStarData.collarSource 0) := by
  let W := A.starCuspWitness
  let s := markedCuspParameter W
  let p := cuspBasePoint A.cuspCoordinate s
  let φ := cuspFiberClutching p
  exact
    { Fiber := AdditiveTorus p.1
      fiberTopology := inferInstance
      fiberPathConnected := inferInstance
      clutching := φ
      totalPathConnected := pathConnectedSpace_circleMappingTorus φ
      fiberHomology :=
        EstablishedFiniteCWTopology.additiveTorusFourTorusHomologicalModel p.1
          (GlobalTorusFamily.fullRankDomain p)
      totalHomotopyEquiv :=
        (puncturedLocalCuspQuotientHomeomorph W s).toHomotopyEquiv.trans
          (openRadialIntervalProdHomotopyEquiv W.localWitness.radius_pos) }

/-- The actual cusp collar has finite integral homology supported in degrees at most six. -/
public theorem actualCuspCollar_integralHomologyFiniteSix :
    IntegralHomologyFiniteSix (A.openEmbeddingStarData.collarSource 0) :=
  A.actualCuspCollarCircleMappingTorusModel.integralHomologyFiniteSix

/-- The actual cusp collar has Euler characteristic zero. -/
public theorem actualCuspCollar_euler_eq_zero :
    integralHomologyEulerCharacteristicSix
      (A.openEmbeddingStarData.collarSource 0) = 0 :=
  A.actualCuspCollarCircleMappingTorusModel.euler_eq_zero

/-- The actual order-three elliptic collar as a circle mapping torus with four-torus fibre. -/
public noncomputable def actualOrderThreeCollarCircleMappingTorusModel :
    FourTorusCircleMappingTorusModel (A.openEmbeddingStarData.collarSource 1) := by
  let p := parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne
  let hp := ComplexTorus.FullRank.ofSetupInequalities p.1 p.2
  let φ := orderThreeAffineClutchingHomeomorph A.periods
  exact
    { Fiber := AdditiveTorus p.1
      fiberTopology := inferInstance
      fiberPathConnected := inferInstance
      clutching := φ
      totalPathConnected := pathConnectedSpace_circleMappingTorus φ
      fiberHomology :=
        EstablishedFiniteCWTopology.additiveTorusFourTorusHomologicalModel p.1 hp
      totalHomotopyEquiv :=
        A.orderThreeCollarRadialMappingTorusHomeomorph.toHomotopyEquiv.trans
          (openRadialIntervalProdHomotopyEquiv A.starSeparation.orderThree.radius_pos) }

/-- The actual order-three elliptic collar has finite integral homology supported in degrees at
most six. -/
public theorem actualOrderThreeCollar_integralHomologyFiniteSix :
    IntegralHomologyFiniteSix (A.openEmbeddingStarData.collarSource 1) :=
  A.actualOrderThreeCollarCircleMappingTorusModel.integralHomologyFiniteSix

/-- The actual order-three elliptic collar has Euler characteristic zero. -/
public theorem actualOrderThreeCollar_euler_eq_zero :
    integralHomologyEulerCharacteristicSix
      (A.openEmbeddingStarData.collarSource 1) = 0 :=
  A.actualOrderThreeCollarCircleMappingTorusModel.euler_eq_zero

/-- The actual order-four elliptic collar as a circle mapping torus with four-torus fibre. -/
public noncomputable def actualOrderFourCollarCircleMappingTorusModel :
    FourTorusCircleMappingTorusModel (A.openEmbeddingStarData.collarSource 2) := by
  let p := parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zTwo
  let hp := ComplexTorus.FullRank.ofSetupInequalities p.1 p.2
  let φ := orderFourAffineClutchingHomeomorph A.periods
  exact
    { Fiber := AdditiveTorus p.1
      fiberTopology := inferInstance
      fiberPathConnected := inferInstance
      clutching := φ
      totalPathConnected := pathConnectedSpace_circleMappingTorus φ
      fiberHomology :=
        EstablishedFiniteCWTopology.additiveTorusFourTorusHomologicalModel p.1 hp
      totalHomotopyEquiv :=
        A.orderFourCollarRadialMappingTorusHomeomorph.toHomotopyEquiv.trans
          (openRadialIntervalProdHomotopyEquiv A.starSeparation.orderFour.radius_pos) }

/-- The actual order-four elliptic collar has finite integral homology supported in degrees at
most six. -/
public theorem actualOrderFourCollar_integralHomologyFiniteSix :
    IntegralHomologyFiniteSix (A.openEmbeddingStarData.collarSource 2) :=
  A.actualOrderFourCollarCircleMappingTorusModel.integralHomologyFiniteSix

/-- The actual order-four elliptic collar has Euler characteristic zero. -/
public theorem actualOrderFourCollar_euler_eq_zero :
    integralHomologyEulerCharacteristicSix
      (A.openEmbeddingStarData.collarSource 2) = 0 :=
  A.actualOrderFourCollarCircleMappingTorusModel.euler_eq_zero

/-- Every actual collar, uniformly packaged by its explicit circle mapping-torus model. -/
public noncomputable def actualCollarCircleMappingTorusModel (i : Fin 3) :
    FourTorusCircleMappingTorusModel (A.openEmbeddingStarData.collarSource i) := by
  refine Fin.cases A.actualCuspCollarCircleMappingTorusModel ?_ i
  intro j
  refine Fin.cases A.actualOrderThreeCollarCircleMappingTorusModel ?_ j
  intro k
  have hk : k = 0 := Fin.eq_zero k
  subst k
  exact A.actualOrderFourCollarCircleMappingTorusModel

/-- Every actual collar has finite integral homology supported in degrees at most six. -/
public theorem actualCollar_integralHomologyFiniteSix (i : Fin 3) :
    IntegralHomologyFiniteSix (A.openEmbeddingStarData.collarSource i) := by
  fin_cases i
  · exact A.actualCuspCollar_integralHomologyFiniteSix
  · exact A.actualOrderThreeCollar_integralHomologyFiniteSix
  · exact A.actualOrderFourCollar_integralHomologyFiniteSix

/-- Every actual collar has Euler characteristic zero. -/
public theorem actualCollar_euler_eq_zero (i : Fin 3) :
    integralHomologyEulerCharacteristicSix
      (A.openEmbeddingStarData.collarSource i) = 0 := by
  fin_cases i
  · exact A.actualCuspCollar_euler_eq_zero
  · exact A.actualOrderThreeCollar_euler_eq_zero
  · exact A.actualOrderFourCollar_euler_eq_zero

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
