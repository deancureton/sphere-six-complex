module

public import SphereSixComplex.Topology.MappingTorusWangGenericAlgebra
public import SphereSixComplex.Topology.PaperAffineCyclicReducedFiberMappingTorus

/-!
# Homology of the reduced elliptic fibres from three-torus mapping-torus models

This is the source-specific replacement interface for the finite-CW models of the order-three
and order-four reduced central fibres.  The only geometric data are homeomorphisms to circle
mapping tori with standard three-torus fibres; Wang's sequence supplies finite homology and Euler
characteristic zero.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Topology.EllipticReducedFiberMappingTorusHomology

open Geometry Geometry.EllipticFamilySpecialization Periods
open PaperEllipticFillingRadialRetraction
open StandardTorusHomology

/-- The two source-specific geometric identifications needed in place of finite-CW models. -/
public structure ReducedFiberMappingTorusModels
    {U : TriangleUniformization} (F : PeriodFunctions U) where
  orderThreeClutching : StdTorus 3 ≃ₜ StdTorus 3
  orderThreeHomeomorph :
    OrderThreeReducedCentralFiber F ≃ₜ CircleMappingTorus orderThreeClutching
  orderFourClutching : StdTorus 3 ≃ₜ StdTorus 3
  orderFourHomeomorph :
    OrderFourReducedCentralFiber F ≃ₜ CircleMappingTorus orderFourClutching

namespace ReducedFiberMappingTorusModels

variable {U : TriangleUniformization} {F : PeriodFunctions U}

public theorem orderThreeIntegralHomologyFiniteSix
    (M : ReducedFiberMappingTorusModels F) :
    IntegralHomologyFiniteSix (OrderThreeReducedCentralFiber F) :=
  circleMappingTorus_integralHomologyFiniteSix_of_homeomorph M.orderThreeClutching
    (finite_homology_stdTorus 3)
    (fun k hk ↦ subsingleton_homology_stdTorus_of_lt 3 k (by omega))
    M.orderThreeHomeomorph

public theorem orderFourIntegralHomologyFiniteSix
    (M : ReducedFiberMappingTorusModels F) :
    IntegralHomologyFiniteSix (OrderFourReducedCentralFiber F) :=
  circleMappingTorus_integralHomologyFiniteSix_of_homeomorph M.orderFourClutching
    (finite_homology_stdTorus 3)
    (fun k hk ↦ subsingleton_homology_stdTorus_of_lt 3 k (by omega))
    M.orderFourHomeomorph

public theorem orderThreeEuler_eq_zero (M : ReducedFiberMappingTorusModels F) :
    integralHomologyEulerCharacteristicSix (OrderThreeReducedCentralFiber F) = 0 :=
  circleMappingTorus_euler_eq_zero_of_homeomorph M.orderThreeClutching
    (finite_homology_stdTorus 3)
    (fun k hk ↦ subsingleton_homology_stdTorus_of_lt 3 k (by omega))
    M.orderThreeHomeomorph

public theorem orderFourEuler_eq_zero (M : ReducedFiberMappingTorusModels F) :
    integralHomologyEulerCharacteristicSix (OrderFourReducedCentralFiber F) = 0 :=
  circleMappingTorus_euler_eq_zero_of_homeomorph M.orderFourClutching
    (finite_homology_stdTorus 3)
    (fun k hk ↦ subsingleton_homology_stdTorus_of_lt 3 k (by omega))
    M.orderFourHomeomorph

end ReducedFiberMappingTorusModels

open PaperAffineCyclicReducedFiberMappingTorus

/-- The explicit affine cyclic normal forms supply the mapping-torus models for both elliptic
reduced central fibres. -/
public noncomputable def paperReducedFiberMappingTorusModels
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    ReducedFiberMappingTorusModels F where
  orderThreeClutching := orderThreeThreeTorusClutching
  orderThreeHomeomorph := orderThreeReducedCentralFiberCircleMappingTorusHomeomorph F
  orderFourClutching := orderFourThreeTorusClutching
  orderFourHomeomorph := orderFourReducedCentralFiberCircleMappingTorusHomeomorph F

/-- Direct homological finiteness for the order-three reduced central fibre. -/
public theorem orderThreeIntegralHomologyFiniteSix
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    IntegralHomologyFiniteSix (OrderThreeReducedCentralFiber F) :=
  (paperReducedFiberMappingTorusModels F).orderThreeIntegralHomologyFiniteSix

/-- Direct homological finiteness for the order-four reduced central fibre. -/
public theorem orderFourIntegralHomologyFiniteSix
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    IntegralHomologyFiniteSix (OrderFourReducedCentralFiber F) :=
  (paperReducedFiberMappingTorusModels F).orderFourIntegralHomologyFiniteSix

/-- The order-three reduced central fibre has Euler characteristic zero directly from its
mapping-torus model. -/
public theorem orderThreeEuler_eq_zero
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    integralHomologyEulerCharacteristicSix (OrderThreeReducedCentralFiber F) = 0 :=
  (paperReducedFiberMappingTorusModels F).orderThreeEuler_eq_zero

/-- The order-four reduced central fibre has Euler characteristic zero directly from its
mapping-torus model. -/
public theorem orderFourEuler_eq_zero
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    integralHomologyEulerCharacteristicSix (OrderFourReducedCentralFiber F) = 0 :=
  (paperReducedFiberMappingTorusModels F).orderFourEuler_eq_zero

end SphereSixComplex.Topology.EllipticReducedFiberMappingTorusHomology

end

end
