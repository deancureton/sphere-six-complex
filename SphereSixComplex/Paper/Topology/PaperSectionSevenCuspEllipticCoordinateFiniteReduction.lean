module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspPrismGeometricDataProof

/-!
# Reduction of the remaining cusp coordinates

This conditional old-marking route compares two coordinate homomorphisms. Eight scalar
evaluations are consequences, and conversely the finite evaluations reconstruct the identities.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open EllipticInteriorMarkedCycleData
open EllipticTwoDiscCoverData

variable {A : PaperAnalyticData}

namespace EstablishedSectionSevenCuspTopology

/-- The remaining finite calculation: three meridian values, four vanishing fibre values, and
the orientation of the first invariant-suspension class. -/
public structure ActualCuspFiberEllipticMarkedCoordinateCalculation
    (R : A.AffineRadialCompletionInput)
    (G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment) : Prop where
  degreeOne : ∀ i : Fin 3,
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ((R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
        (integralSingularHomologyMap 1
          R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap))
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm (Pi.single i 1)) =
        cuspEllipticDegreeOneRawCoordinate (Pi.single i 1)
  degreeTwoFiberCoinvariant : ∀ i : Fin 6, i ≠ 4 → i ≠ 5 →
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        G₀
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1))) =
      cuspEllipticDegreeTwoFiberRawCoordinate (Pi.single i 1)
  degreeTwoIndexFour :
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        G₀
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 1


/-- The three marked degree-one evaluations follow from meridian naturality. -/
public theorem cuspCoordinateComparison_degreeOne_basis
    {R : A.AffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment}
    (C : R.twoDiscCover.CuspEllipticMappingTorusCoordinateComparison R.homologyAlignment G₀) (i : Fin 3) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ((R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
        (integralSingularHomologyMap 1
          R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap))
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm (Pi.single i 1)) =
        cuspEllipticDegreeOneRawCoordinate (Pi.single i 1) := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  have hi := DFunLike.congr_fun C.degreeOne
    (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
      (Pi.single i 1))
  change _ = cuspEllipticDegreeOneRawCoordinate
    (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHOneAddEquiv
      (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
        (Pi.single i 1))) at hi
  rw [AddEquiv.apply_symm_apply] at hi
  exact hi

/-- The five non-boundary degree-two evaluations follow from fibre-coordinate naturality. -/
public theorem cuspCoordinateComparison_degreeTwo_basis
    {R : A.AffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment}
    (C : R.twoDiscCover.CuspEllipticMappingTorusCoordinateComparison R.homologyAlignment G₀)
    (i : Fin 6) (_hi5 : i ≠ 5) :
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        G₀
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1))) =
      cuspEllipticDegreeTwoFiberRawCoordinate (Pi.single i 1) := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  rw [← cuspMappingTorusToEllipticInteriorMap_basis (D := R.twoDiscCover) i]
  have hi := DFunLike.congr_fun C.degreeTwoFiber
    (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
      (Pi.single i 1))
  change _ = cuspEllipticDegreeTwoFiberRawCoordinate
    (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHTwoAddEquiv
      (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
        (Pi.single i 1))) at hi
  rw [AddEquiv.apply_symm_apply] at hi
  exact hi

/-- The finite coordinate package follows from the exact three residual geometric inputs: the
degree-one coordinate homomorphism, vanishing on the four fibre-coinvariant basis classes, and
normalization of the first invariant-suspension class. -/
public theorem cuspCoordinateComparison_of_basisValues
    {R : A.AffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment}
    (hOne :
      (R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
          (integralSingularHomologyMap 1
            R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap) =
        let G := A.actualCuspRadialClutchingData
        let _ := G.fiberTopology
        actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
          G.geometricWangSections.circleMappingTorusHOneAddEquiv)
    (hFiber : ∀ i : Fin 6, i ≠ 4 → i ≠ 5 →
      R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
          G₀
          (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
            (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1))) =
        cuspEllipticDegreeTwoFiberRawCoordinate (Pi.single i 1))
    (hFour :
      R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
          G₀
          (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
            (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 1) :
    R.twoDiscCover.CuspEllipticMappingTorusCoordinateComparison R.homologyAlignment G₀ where
  degreeOne := hOne
  degreeTwoFiber := by
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    apply addMonoidHom_ext_of_equiv_pi_single_one
      G.geometricWangSections.circleMappingTorusHTwoAddEquiv
    intro i
    rw [AddMonoidHom.comp_apply,
      cuspMappingTorusToEllipticInteriorMap_basis (D := R.twoDiscCover) i]
    change _ = cuspEllipticDegreeTwoFiberRawCoordinate
      (G.geometricWangSections.circleMappingTorusHTwoAddEquiv
        (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
          (Pi.single i 1)))
    rw [AddEquiv.apply_symm_apply]
    by_cases hi4 : i = 4
    · subst i
      simpa [cuspEllipticDegreeTwoFiberRawCoordinate] using hFour
    · by_cases hi5 : i = 5
      · subst i
        let E := R.homologyAlignment.actualHomologyCoordinates
          |>.normalizedEllipticInteriorHomologyTwoEquiv
            (R.twoDiscCover.cuspNormalizedDegreeTwoSplitting R.homologyAlignment
              G₀)
        change
          E (integralSingularHomologyMap 2
            R.twoDiscCover.cuspToEllipticInteriorMap.hom
            (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))) 0 = 0
        rw [← normalizedEllipticInteriorHomologyTwoEquiv_symm_single_one
          (D := R.twoDiscCover) (N := R.homologyAlignment)
          (G₀ := G₀), AddEquiv.apply_symm_apply]
        simp
      · exact hFiber i hi4 hi5


/-- The eight marked evaluations are exactly equivalent to the complete coordinate comparison. -/
public theorem markedCoordinateCalculation_iff_finiteCoordinateIdentities
    {R : A.AffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment} :
    ActualCuspFiberEllipticMarkedCoordinateCalculation R G₀ ↔
      R.twoDiscCover.CuspEllipticMappingTorusCoordinateComparison R.homologyAlignment G₀ := by
  constructor
  · intro C
    apply cuspCoordinateComparison_of_basisValues
    · let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      apply addMonoidHom_ext_of_equiv_pi_single_one
        G.geometricWangSections.circleMappingTorusHOneAddEquiv
      intro i
      rw [AddMonoidHom.comp_apply]
      change _ = cuspEllipticDegreeOneRawCoordinate
        (G.geometricWangSections.circleMappingTorusHOneAddEquiv
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
            (Pi.single i 1)))
      rw [AddEquiv.apply_symm_apply]
      exact C.degreeOne i
    · exact C.degreeTwoFiberCoinvariant
    · exact C.degreeTwoIndexFour
  · intro C
    exact {
      degreeOne := cuspCoordinateComparison_degreeOne_basis C
      degreeTwoFiberCoinvariant := by
        intro i hi4 hi5
        simpa [hi4] using cuspCoordinateComparison_degreeTwo_basis C i hi5
      degreeTwoIndexFour := by
        simpa [cuspEllipticDegreeTwoFiberRawCoordinate] using
          cuspCoordinateComparison_degreeTwo_basis C 4 (by decide) }


/-- The four non-suspension degree-two evaluations are precisely fibre-coinvariant
vanishing. -/
public theorem cuspCoordinateComparison_degreeTwo_fiberBasis
    {R : A.AffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment}
    (C : R.twoDiscCover.CuspEllipticMappingTorusCoordinateComparison R.homologyAlignment G₀) :
    ∀ i : Fin 6, i ≠ 4 → i ≠ 5 →
      R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
          G₀
          (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
            (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1))) =
        cuspEllipticDegreeTwoFiberRawCoordinate (Pi.single i 1) := by
  intro i hi4 hi5
  exact cuspCoordinateComparison_degreeTwo_basis C i hi5

/-- The remaining degree-two evaluation is exactly the normalization of the first invariant
suspension class. -/
public theorem cuspCoordinateComparison_degreeTwo_indexFour
    {R : A.AffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment}
    (C : R.twoDiscCover.CuspEllipticMappingTorusCoordinateComparison R.homologyAlignment G₀) :
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        G₀
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 1 := by
  simpa [cuspEllipticDegreeTwoFiberRawCoordinate] using
    cuspCoordinateComparison_degreeTwo_basis C 4 (by decide)


end EstablishedSectionSevenCuspTopology

end SphereSixComplex.Geometry.PaperAnalyticData

end
