module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspPrismGeometricDataProof

/-!
# Reduction of the remaining cusp coordinates

The trusted input is expressed as two naturality identities between coordinate homomorphisms.
The previously trusted eight scalar evaluations are consequences, and conversely the old finite
package reconstructs these two identities.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open EllipticInteriorMarkedCycleData
open EllipticTwoDiscCoverData

variable {A : PaperAnalyticData}

namespace EstablishedSectionSevenCuspTopology

/-- The two coordinate-homomorphism identities remaining in the cusp-to-elliptic comparison. -/
public structure ActualCuspFiberEllipticFiniteCoordinateIdentities
    (R : A.AffineRadialCompletionInput)
    (G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment) : Prop where
  coordinateComparison :
    R.twoDiscCover.CuspEllipticMappingTorusCoordinateComparison R.homologyAlignment
      G₀

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

namespace ActualCuspFiberEllipticFiniteCoordinateIdentities

/-- The three marked degree-one evaluations follow from meridian naturality. -/
public theorem degreeOne
    {R : A.AffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment}
    (C : ActualCuspFiberEllipticFiniteCoordinateIdentities R G₀) (i : Fin 3) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ((R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
        (integralSingularHomologyMap 1
          R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap))
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm (Pi.single i 1)) =
        cuspEllipticDegreeOneRawCoordinate (Pi.single i 1) := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  have hi := DFunLike.congr_fun C.coordinateComparison.degreeOne
    (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
      (Pi.single i 1))
  change _ = cuspEllipticDegreeOneRawCoordinate
    (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHOneAddEquiv
      (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
        (Pi.single i 1))) at hi
  rw [AddEquiv.apply_symm_apply] at hi
  exact hi

/-- The five non-boundary degree-two evaluations follow from fibre-coordinate naturality. -/
public theorem degreeTwo
    {R : A.AffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment}
    (C : ActualCuspFiberEllipticFiniteCoordinateIdentities R G₀)
    (i : Fin 6) (_hi5 : i ≠ 5) :
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        G₀
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1))) =
      cuspEllipticDegreeTwoFiberRawCoordinate (Pi.single i 1) := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  rw [← cuspMappingTorusToEllipticInteriorMap_basis (D := R.twoDiscCover) i]
  have hi := DFunLike.congr_fun C.coordinateComparison.degreeTwoFiber
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
public theorem of_coordinateIdentities
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
    ActualCuspFiberEllipticFiniteCoordinateIdentities R G₀ where
  coordinateComparison :=
    { degreeOne := hOne
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
          · exact hFiber i hi4 hi5 }

end ActualCuspFiberEllipticFiniteCoordinateIdentities

/-- The eight marked evaluations are exactly equivalent to the complete coordinate comparison. -/
public theorem markedCoordinateCalculation_iff_finiteCoordinateIdentities
    {R : A.AffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment} :
    ActualCuspFiberEllipticMarkedCoordinateCalculation R G₀ ↔
      ActualCuspFiberEllipticFiniteCoordinateIdentities R G₀ := by
  constructor
  · intro C
    apply ActualCuspFiberEllipticFiniteCoordinateIdentities.of_coordinateIdentities
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
      degreeOne := C.degreeOne
      degreeTwoFiberCoinvariant := by
        intro i hi4 hi5
        simpa [hi4] using C.degreeTwo i hi5
      degreeTwoIndexFour := by
        simpa [cuspEllipticDegreeTwoFiberRawCoordinate] using
          C.degreeTwo 4 (by decide) }

namespace ActualCuspFiberEllipticFiniteCoordinateIdentities

/-- The three degree-one evaluations determine the complete coordinate homomorphism. -/
public theorem degreeOneHom
    {R : A.AffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment}
    (C : ActualCuspFiberEllipticFiniteCoordinateIdentities R G₀) :
    (R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
        (integralSingularHomologyMap 1
          R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap) =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      actualCuspEllipticDegreeOneCoordinateAfterAddEquiv
        G.geometricWangSections.circleMappingTorusHOneAddEquiv :=
  C.coordinateComparison.degreeOne

/-- The four non-suspension degree-two evaluations are precisely fibre-coinvariant
vanishing. -/
public theorem degreeTwoFiberCoinvariantValues
    {R : A.AffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment}
    (C : ActualCuspFiberEllipticFiniteCoordinateIdentities R G₀) :
    ∀ i : Fin 6, i ≠ 4 → i ≠ 5 →
      R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
          G₀
          (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
            (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1))) =
        cuspEllipticDegreeTwoFiberRawCoordinate (Pi.single i 1) := by
  intro i hi4 hi5
  exact C.degreeTwo i hi5

/-- The remaining degree-two evaluation is exactly the normalization of the first invariant
suspension class. -/
public theorem degreeTwoIndexFour
    {R : A.AffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment}
    (C : ActualCuspFiberEllipticFiniteCoordinateIdentities R G₀) :
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        G₀
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 1 := by
  simpa [cuspEllipticDegreeTwoFiberRawCoordinate] using
    C.degreeTwo 4 (by decide)

end ActualCuspFiberEllipticFiniteCoordinateIdentities

end EstablishedSectionSevenCuspTopology

end SphereSixComplex.Geometry.PaperAnalyticData

end
