module

public import SphereSixComplex.Topology.EstablishedFirstHurewicz
public import SphereSixComplex.Topology.PaperAffineCyclicQuotientCovering

open AlgebraicTopology MulOpposite Topology

namespace SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
namespace EstablishedAffineCyclicQuotientHomology

open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.EstablishedFirstHurewicz

noncomputable section

variable {m : ℕ} [NeZero m]
variable {p : SphereSixComplex.Periods.Parameters}
variable {D : RadialEllipticActionData m
  (SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus p)}

public noncomputable def establishedAffineCyclicDeckHurewiczComparison
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    AffineCyclicDeckHurewiczComparison P := by
  let _ := affineCyclicFillingDeckAction P
  let q := complexTwoReducedCentralFiberProjection (D := D)
  let _ : PathConnectedSpace D.reducedCentralFiber :=
    reducedCentralFiber_pathConnectedSpace D
  let hp : IsQuotientCoveringMap q
      (affineCyclicBoundaryDeckData P).FillingDeck :=
    affineCyclicFilling_isQuotientCoveringMap P
      P.lift_continuous P.lift_symm_continuous
  let b : D.reducedCentralFiber := q 0
  let e := hp.fundamentalGroupEquiv (⟨0, rfl⟩ : q ⁻¹' {b})
  let hOneEquiv := deckHOneEquivOfFundamentalGroupEquivOpposite b e
  refine { hOneEquiv := hOneEquiv, projection := ?_ }
  intro x
  apply deckHOneEquivOfFundamentalGroupEquivOpposite_marked
    b e (fun y : Lattice ↦ affineCyclicKernelIncl P y)
      (fun y ↦ projectedStraightPeriodLoop P y) (coverProjectionLatticeMap P)
  · exact projectedStraightPeriodLoop_fundamentalGroupEquiv P hp
  · exact projectedStraightPeriodLoop_homologyClass_eq_coverProjectionLatticeMap P

end

end EstablishedAffineCyclicQuotientHomology
end SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
