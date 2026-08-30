module

public import SphereSixComplex.Topology.CuspFiberSpecializationBasisNormalization
public import SphereSixComplex.Topology.EstablishedFirstHurewicz
public import SphereSixComplex.Topology.PaperCuspUnwrappedFillingCover

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex

namespace Topology.EstablishedFirstHurewicz

/-- A surjective group homomorphism remains surjective after abelianization. -/
public theorem abelianizationMap_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (Abelianization.map f) := by
  intro y
  induction y using Quotient.inductionOn with
  | _ y =>
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨Abelianization.of x, rfl⟩

/-- A map surjective on fundamental groups is surjective on first integral homology. -/
public theorem integralSingularHomologyMap_one_surjective_of_fundamentalGroupMap_surjective
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) (b : X)
    (hf : Function.Surjective (FundamentalGroup.map f b)) :
    Function.Surjective (integralSingularHomologyMap 1 f) := by
  let HX := establishedFirstHurewiczData X b
  let HY := establishedFirstHurewiczData Y (f b)
  intro y
  obtain ⟨a, rfl⟩ := HY.equiv.surjective y
  have hab : Function.Surjective (abelianPi1Map f b) :=
    abelianizationMap_surjective (FundamentalGroup.map f b) hf
  obtain ⟨x, rfl⟩ := hab a
  exact ⟨HX.equiv x, (establishedFirstHurewiczData_naturality f b x).symm⟩

end Topology.EstablishedFirstHurewicz

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- The actual cusp-collar inclusion is onto on first integral homology. -/
public theorem puncturedLocalCuspToFilling_homologyOne_surjective
    (W : ActualPuncturedCuspCollarWitness N M)
    (b : puncturedLocalCuspQuotient W) :
    Function.Surjective (integralSingularHomologyMap 1
      ⟨puncturedLocalCuspToFilling W, puncturedLocalCuspToFilling_continuous W⟩) := by
  let _ := paperCuspBoundaryDeckAction W
  let _ := paperCuspFillingDeckAction W
  let U := paperCuspUnwrappedFillingCover W b
  let _ : SimplyConnectedSpace (additiveCuspRadiusCover W.localWitness.radius) :=
    U.boundarySimplyConnected
  let _ : SimplyConnectedSpace (CuspLocalPhaseAction.LocalCarrier M W.localWitness.radius) :=
    U.fillingSimplyConnected
  let _ : PathConnectedSpace (puncturedLocalCuspQuotient W) :=
    U.boundaryQuotient.surjective.pathConnectedSpace U.boundaryProjection.continuous
  let _ : PathConnectedSpace (actualLocalCuspFilling W) :=
    U.fillingQuotient.surjective.pathConnectedSpace U.fillingProjection.continuous
  exact SphereSixComplex.Topology.EstablishedFirstHurewicz.integralSingularHomologyMap_one_surjective_of_fundamentalGroupMap_surjective
    U.baseMap (U.boundaryProjection U.base) U.fundamentalGroupData.map_surjective

namespace CuspFiberSpecializationNormalization

/-- The basis-free degree-one total specialization is onto. -/
public theorem rawDegreeOneTotalSpecialization_surjective
    {W : ActualPuncturedCuspCollarWitness N M}
    (G : ActualCuspRadialClutchingData W) (b : puncturedLocalCuspQuotient W) :
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
