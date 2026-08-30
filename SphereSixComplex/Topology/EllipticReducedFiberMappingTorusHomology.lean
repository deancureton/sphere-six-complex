module

public import SphereSixComplex.Topology.MappingTorusWangGenericAlgebra
public import SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction

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

end SphereSixComplex.Topology.EllipticReducedFiberMappingTorusHomology

end

end
