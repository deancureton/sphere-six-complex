module

public import SphereSixComplex.Prerequisites.Topology.BinaryOpenCoverOrientedRefinementNaturality
public import SphereSixComplex.Prerequisites.Topology.CanonicalProductWangBoundaryNaturality
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspMarkedConnectingNaturalityProof
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspFiberBandTopologicalSquare
public import SphereSixComplex.Prerequisites.Topology.WangHomologyPresentationProof
public import SphereSixComplex.Prerequisites.Topology.BinaryOpenCoverAssembly

/-!
# Phase comparison for the cusp radial mapping torus

The radial homotopy equivalence forgets only the contractible radial coordinate.  This file
compares its mapping-torus coordinate with the additive cusp parameter modulo integral shifts.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContinuousMap

open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.CuspPeriodExpansion

namespace SphereSixComplex.Geometry.CuspCollar

variable {E : Periods.FuchsianModularLift}
  {D : Periods.FuchsianPeriodLocalData E}
  {N : CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D}
  {M : InfiniteA2Toric.Model}
  {W : ActualPuncturedCuspCollarWitness N M}

/-- The two standard presentations of an interval point define the same mapping-torus point. -/
public theorem realMappingTorusHomeomorph_intervalProjection
    {T : Type} [TopologicalSpace T] (phi : T ≃ₜ T) (p : unitInterval × T) :
    realMappingTorusHomeomorph phi (realMappingTorusIntervalProjection phi p) =
      circleMappingTorusCylinderProjection phi p := by
  let C := realMappingTorusClutchingData phi
  let e : CircleMappingTorus phi ≃ RealMappingTorus phi :=
    Equiv.ofBijective C.circleToTotal C.circleToTotal_bijective
  apply e.injective
  change C.circleToTotal
      (C.totalHomeomorphCircleMappingTorus (C.projection p)) =
    C.circleToTotal (circleMappingTorusCylinderProjection phi p)
  rw [show C.circleToTotal
      (C.totalHomeomorphCircleMappingTorus (C.projection p)) = C.projection p by
    exact C.totalHomeomorphCircleMappingTorus.symm_apply_apply _]
  exact C.circleToTotal_mk p

end SphereSixComplex.Geometry.CuspCollar

end

end
