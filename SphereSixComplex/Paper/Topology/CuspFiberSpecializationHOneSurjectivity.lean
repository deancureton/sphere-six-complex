module

public import SphereSixComplex.Paper.Topology.CuspFiberSpecializationBasisNormalization
public import SphereSixComplex.Paper.Topology.PaperCuspUnwrappedFillingCover

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex



namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.InfiniteA2Toric

variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- The actual cusp-collar inclusion is onto on first integral homology. -/
public theorem puncturedLocalCuspToFilling_homologyOne_surjective
    (W : ActualPuncturedCuspCollarWitness N M)
    (b : PuncturedLocalCuspQuotient W) :
    Function.Surjective (integralSingularHomologyMap 1
      ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩) := by
  let _ := paperCuspBoundaryDeckAction W
  let _ := paperCuspFillingDeckAction W
  let U := paperCuspUnwrappedFillingCover W b
  let _ : SimplyConnectedSpace (additiveCuspRadiusCover W.localWitness.radius) :=
    U.boundarySimplyConnected
  let _ : SimplyConnectedSpace (CuspLocalPhaseAction.localCarrier M W.localWitness.radius) :=
    U.fillingSimplyConnected
  let _ : PathConnectedSpace (PuncturedLocalCuspQuotient W) :=
    U.boundaryQuotient.surjective.pathConnectedSpace U.boundaryProjection.continuous
  let _ : PathConnectedSpace (ActualLocalCuspFilling W) :=
    U.fillingQuotient.surjective.pathConnectedSpace U.fillingProjection.continuous
  exact Hurewicz.homologyOneMap_surjective_of_pi1Map_surjective
    U.baseMap (U.boundaryProjection U.base) U.fundamentalGroupData.map_surjective

namespace CuspFiberSpecializationNormalization

/-- The basis-free degree-one total specialization is onto. -/
public theorem rawDegreeOneTotalSpecialization_surjective
    {W : ActualPuncturedCuspCollarWitness N M}
    (G : ActualCuspRadialClutchingData W) (b : PuncturedLocalCuspQuotient W) :
    Function.Surjective (rawDegreeOneTotalSpecialization G) := by
  let _ := G.fiberTopology
  let e := integralSingularHomologyEquivOfHomotopyEquiv 1
    G.toUnnormalizedCuspRadialClutchingData.totalHomotopyEquiv
  intro y
  obtain ⟨x, hx⟩ := puncturedLocalCuspToFilling_homologyOne_surjective W b y
  refine ⟨e x, ?_⟩
  change integralSingularHomologyMap 1
      ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩
        (e.symm (e x)) = y
  rw [e.symm_apply_apply, hx]

end CuspFiberSpecializationNormalization

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex

end

end
