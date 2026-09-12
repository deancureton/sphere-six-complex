module

public import SphereSixComplex.Prerequisites.Topology.FiniteBouquetMappingTorusEuler
public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecialization

/-!
# Euler characteristic of the three actual collar pieces

Each collar has an explicit radial mapping-torus model.  Removing the contractible radial
coordinate and applying the Wang-sequence Euler calculation proves finiteness and Euler zero
without using the abstract finite-CW bundle realization.
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

open AnalyticTorusFamily EllipticFamilySpecialization
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.CuspRadialClutchingConstruction

variable (A : AnalyticData)

/-- The actual cusp collar as a circle mapping torus with four-torus fibre. -/
public noncomputable def cuspCollarCircleMappingTorusModel :
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
        StandardTorusHomology.additiveTorusFourTorusHomologicalModel p.1
          (GlobalTorusFamily.fullRankDomain p)
      totalHomotopyEquiv :=
        (puncturedLocalCuspQuotientHomeomorph W s).toHomotopyEquiv.trans
          (openRadialIntervalProdHomotopyEquiv W.localWitness.radius_pos) }



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
        StandardTorusHomology.additiveTorusFourTorusHomologicalModel p.1 hp
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
        StandardTorusHomology.additiveTorusFourTorusHomologicalModel p.1 hp
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
  refine Fin.cases A.cuspCollarCircleMappingTorusModel ?_ i
  intro j
  refine Fin.cases A.actualOrderThreeCollarCircleMappingTorusModel ?_ j
  intro k
  have hk : k = 0 := Fin.eq_zero k
  subst k
  exact A.actualOrderFourCollarCircleMappingTorusModel



end SphereSixComplex.Geometry.AnalyticData

end

end
