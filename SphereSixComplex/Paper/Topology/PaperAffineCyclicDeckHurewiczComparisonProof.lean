module

public import SphereSixComplex.Prerequisites.Topology.EstablishedFirstHurewicz
public import SphereSixComplex.Paper.Topology.PaperAffineCyclicQuotientCovering

open AlgebraicTopology MulOpposite Topology

namespace SphereSixComplex.AffineCyclicQuotientHomology
end SphereSixComplex.AffineCyclicQuotientHomology

namespace SphereSixComplex.AffineCyclicQuotientHomology
open SphereSixComplex SphereSixComplex.Topology
open SphereSixComplex.AffineCyclicQuotientHomology

open _root_.SphereSixComplex.AffineCyclicQuotientHomology
open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.LatticeData
open SphereSixComplex.Periods
open SphereSixComplex.EllipticFilling
open Hurewicz

noncomputable section

variable {m : ℕ} [NeZero m]
variable {p : SphereSixComplex.Periods.Parameters}
variable {D : RadialEllipticActionData m
  (SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus p)}

public noncomputable def deckHurewiczComparison
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
  let hOneEquiv := homologyOneEquivOfPi1Opposite b e
  refine { hOneEquiv := hOneEquiv, projection := ?_ }
  intro x
  apply homologyOneEquivOfPi1Opposite_apply_marked
    b e (fun y : Lattice ↦ affineCyclicKernelIncl P y)
      (fun y ↦ projectedStraightPeriodLoop P y) (coverProjectionLatticeMap P)
  · exact projectedStraightPeriodLoop_fundamentalGroupEquiv P hp
  · exact projectedStraightPeriodLoop_homologyClass_eq_coverProjectionLatticeMap P

end

end SphereSixComplex.AffineCyclicQuotientHomology

namespace SphereSixComplex.AffineCyclicQuotientHomology

end SphereSixComplex.AffineCyclicQuotientHomology
