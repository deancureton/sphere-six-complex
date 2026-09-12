module
public import SphereSixComplex.Paper.Topology.CuspThirdSweep
public import SphereSixComplex.Paper.Topology.RegularPeriodCircleTransport

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open GlobalTorusFamily CuspCollar CuspRadialClutchingConstruction
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open ComplexTorus TorusFamily CuspPeriodExpansion
open EllipticTwoDiscCoverData

public theorem cuspFullFiberSlice_coordinateCircle_real (A : AnalyticData)
    (i : Fin 4) (s : ℂ) (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius) (t : ℝ) :
    actualCuspFullFiberSlice (A := A) s hs
      (cuspCoordinateCircle (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness)) i (fun _ ↦ (t : UnitAddCircle))) =
    additiveCuspBoundaryProjection A.starCuspWitness
      ⟨(t • periodVector (cuspBasePoint A.cuspCoordinate s).1 (Pi.single i 1), s), hs⟩ := by
  rw [cuspCoordinateCircle_real]
  have h : collarFiberEquiv A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness) s
      (t • periodVector (cuspBasePoint A.cuspCoordinate s).1 (Pi.single i 1)) =
      t • periodVector (cuspBasePoint A.cuspCoordinate
        (markedCuspParameter A.starCuspWitness)).1 (Pi.single i 1) := by
    rw [collarFiberEquiv_apply]
    change (fullRankDomain _).realEquiv ((fullRankDomain _).realEquiv.symm
      (t • periodVector _ (Pi.single i 1))) = _
    rw [map_smul, realEquiv_symm_periodVector, map_smul,
      (fullRankDomain _).map_integer]
  rw [← h]
  exact actualCuspFullFiberSlice_additiveTorusProjection s hs _

public theorem cuspFullFiberSlice_coordinateCircle_central (A : AnalyticData)
    (i : Fin 4) (s : ℂ) (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius)
    (t : UnitAddCircle) :
    A.starToCentral 0
      (actualCuspFullFiberSlice (A := A) s hs
        (cuspCoordinateCircle (cuspBasePoint A.cuspCoordinate
          (markedCuspParameter A.starCuspWitness)) i (fun _ ↦ t))) =
    regularPeriodCircleInGlobal A.periods (Pi.single i 1)
      (t, (additiveCuspBundleHomeomorph A.starCuspWitness ⟨(0, s), hs⟩).1.1) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [cuspFullFiberSlice_coordinateCircle_real]
  trans additiveCuspCoverToGlobal A.starCuspWitness
    ⟨(r • periodVector (cuspBasePoint A.cuspCoordinate s).1 (Pi.single i 1), s), hs⟩
  · exact puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection A.starCuspWitness _
  rw [additiveCuspCoverToGlobal_eq_quotientProjections]
  change _ = A.centralQuotientProjection (regularPeriodCircle A.periods (Pi.single i 1) _)
  rw [regularPeriodCircle_real]
  rfl









end SphereSixComplex.Geometry.AnalyticData
end
end
