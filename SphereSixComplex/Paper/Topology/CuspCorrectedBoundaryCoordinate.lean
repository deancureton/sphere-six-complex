module
public import SphereSixComplex.Paper.Topology.CuspNormalizedBandMarking
public import SphereSixComplex.Paper.Topology.CuspFourthSweepCentralImage

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex SphereSixComplex.Topology
open EllipticTwoDiscCoverData EllipticInteriorMarkedCycleData

public theorem cuspPulledBackBoundaryCoordinateHom_eq_rawFour {A : AnalyticData}
    (R : A.AffineRadialCompletionInput) :
    R.twoDiscCover.cuspPulledBackBoundaryCoordinateHom R.homologyAlignment =
      coordinateAfterAddEquiv A.cuspRawHomologyTwoEquiv 4 := by
  apply addMonoidHom_ext_of_equiv_pi_single_one A.cuspRawHomologyTwoEquiv
  intro i
  by_cases hi : i.val < 4
  · let j : Fin 4 := ⟨i.val, hi⟩
    have hij : Fin.castAdd 2 j = i := Fin.ext rfl
    rw [← hij]
    have hz := cuspPulledBackMarkedBoundary_rawBasis_castAdd_eq_zero R j
    change R.twoDiscCover.cuspPulledBackBoundaryCoordinateHom R.homologyAlignment
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (Fin.castAdd 2 j) 1)) = 0 at hz
    rw [hz, coordinateAfterAddEquiv_apply, AddEquiv.apply_symm_apply,
      Pi.single_eq_of_ne (by omega : (4 : Fin 6) ≠ Fin.castAdd 2 j)]
  · have hi45 : i = 4 ∨ i = 5 := by omega
    rcases hi45 with rfl | rfl
    · rw [cuspRawFour_pulled_back_scalar_one]
      simp [coordinateAfterAddEquiv_apply]
    · rw [cuspPulledBackBoundaryCoordinateHom_apply_eq_bandCoordinate]
      change R.homologyAlignment.actualHomologyCoordinates.bandOne
        (R.twoDiscCover.cuspPulledBackBoundaryHom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))) 3 = _
      rw [cuspRawFive_pulled_back_boundary_zero, map_zero]
      simp [coordinateAfterAddEquiv_apply]

end SphereSixComplex.Geometry.AnalyticData
end
