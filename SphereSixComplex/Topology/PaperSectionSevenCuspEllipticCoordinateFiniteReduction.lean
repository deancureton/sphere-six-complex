module

public import SphereSixComplex.Topology.PaperSectionSevenCuspPrismGeometricDataProof

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

open SectionSevenEllipticInteriorMarkedCycleData
open SectionSevenEllipticTwoDiscCoverData

variable {A : PaperAnalyticData}

namespace EstablishedSectionSevenCuspTopology

/-- The two coordinate-homomorphism identities remaining in the cusp-to-elliptic comparison. -/
public structure ActualCuspFiberEllipticFiniteCoordinateIdentities
    (R : A.SectionSevenAffineRadialCompletionInput)
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment) : Prop where
  coordinateComparison :
    R.twoDiscCover.CuspEllipticMappingTorusCoordinateComparison R.homologyAlignment
      W.pulledBackBoundaryBasisBridge

/-- The remaining finite calculation: three meridian values, four vanishing fibre values, and
the orientation of the first invariant-suspension class. -/
public structure ActualCuspFiberEllipticMarkedCoordinateCalculation
    (R : A.SectionSevenAffineRadialCompletionInput)
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment) : Prop where
  degreeOne : ∀ i : Fin 3,
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ((R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
        (integralSingularHomologyMap 1
          R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap))
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm (Pi.single i 1)) =
        (Pi.single i 1 : Fin 3 → ℤ) 2
  degreeTwoFiberCoinvariant : ∀ i : Fin 6, i ≠ 4 → i ≠ 5 →
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        W.pulledBackBoundaryBasisBridge
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) = 0
  degreeTwoIndexFour :
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        W.pulledBackBoundaryBasisBridge
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 1

/-- The remaining paper-specific input, reduced to the eight non-formal marked evaluations. -/
public axiom establishedActualCuspFiberEllipticMarkedCoordinateCalculation
    (R : A.SectionSevenAffineRadialCompletionInput)
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment) :
    ActualCuspFiberEllipticMarkedCoordinateCalculation R W

namespace ActualCuspFiberEllipticFiniteCoordinateIdentities

/-- The three marked degree-one evaluations follow from meridian naturality. -/
public theorem degreeOne
    {R : A.SectionSevenAffineRadialCompletionInput}
    {W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment}
    (C : ActualCuspFiberEllipticFiniteCoordinateIdentities R W) (i : Fin 3) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ((R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
        (integralSingularHomologyMap 1
          R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap))
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm (Pi.single i 1)) =
        (Pi.single i 1 : Fin 3 → ℤ) 2 := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  have hi := DFunLike.congr_fun C.coordinateComparison.degreeOne
    (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
      (Pi.single i 1))
  simpa only [coordinateAfterAddEquiv_apply, AddEquiv.apply_symm_apply] using hi

/-- The five non-boundary degree-two evaluations follow from fibre-coordinate naturality. -/
public theorem degreeTwo
    {R : A.SectionSevenAffineRadialCompletionInput}
    {W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment}
    (C : ActualCuspFiberEllipticFiniteCoordinateIdentities R W) (i : Fin 6) (_hi5 : i ≠ 5) :
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        W.pulledBackBoundaryBasisBridge
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) =
      if i = 4 then 1 else 0 := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  rw [← cuspMappingTorusToEllipticInteriorMap_basis (D := R.twoDiscCover) i]
  have hi := DFunLike.congr_fun C.coordinateComparison.degreeTwoFiber
    (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
      (Pi.single i 1))
  calc
    _ = (Pi.single i 1 : Fin 6 → ℤ) 4 := by
      simpa only [AddMonoidHom.comp_apply, coordinateAfterAddEquiv_apply,
        AddEquiv.apply_symm_apply] using hi
    _ = if i = 4 then 1 else 0 := by
      classical
      simp only [Pi.single_apply, eq_comm]

/-- The finite coordinate package follows from the exact three residual geometric inputs: the
degree-one coordinate homomorphism, vanishing on the four fibre-coinvariant basis classes, and
normalization of the first invariant-suspension class. -/
public theorem of_coordinateIdentities
    {R : A.SectionSevenAffineRadialCompletionInput}
    {W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment}
    (hOne :
      (R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
          (integralSingularHomologyMap 1
            R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap) =
        let G := A.actualCuspRadialClutchingData
        let _ := G.fiberTopology
        coordinateAfterAddEquiv G.geometricWangSections.circleMappingTorusHOneAddEquiv 2)
    (hVanish : ∀ i : Fin 6, i ≠ 4 → i ≠ 5 →
      R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
          W.pulledBackBoundaryBasisBridge
          (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) = 0)
    (hFour :
      R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
          W.pulledBackBoundaryBasisBridge
          (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 1) :
    ActualCuspFiberEllipticFiniteCoordinateIdentities R W where
  coordinateComparison :=
    { degreeOne := hOne
      degreeTwoFiber := by
        let G := A.actualCuspRadialClutchingData
        let _ := G.fiberTopology
        apply addMonoidHom_ext_of_equiv_pi_single_one
          G.geometricWangSections.circleMappingTorusHTwoAddEquiv
        intro i
        rw [AddMonoidHom.comp_apply, coordinateAfterAddEquiv_apply,
          AddEquiv.apply_symm_apply,
          cuspMappingTorusToEllipticInteriorMap_basis (D := R.twoDiscCover) i]
        by_cases hi4 : i = 4
        · subst i
          simpa using hFour
        · by_cases hi5 : i = 5
          · subst i
            let E := R.homologyAlignment.actualHomologyCoordinates
              |>.normalizedEllipticInteriorHomologyTwoEquiv
                (R.twoDiscCover.cuspNormalizedDegreeTwoSplitting R.homologyAlignment
                  W.pulledBackBoundaryBasisBridge)
            change
              E (integralSingularHomologyMap 2
                R.twoDiscCover.cuspToEllipticInteriorMap.hom
                (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))) 0 = 0
            rw [← normalizedEllipticInteriorHomologyTwoEquiv_symm_single_one
              (D := R.twoDiscCover) (N := R.homologyAlignment)
              (G₀ := W.pulledBackBoundaryBasisBridge), AddEquiv.apply_symm_apply]
            simp
          · rw [Pi.single_eq_of_ne (Ne.symm hi4)]
            exact hVanish i hi4 hi5 }

end ActualCuspFiberEllipticFiniteCoordinateIdentities

/-- The eight marked evaluations are exactly equivalent to the complete coordinate comparison. -/
public theorem markedCoordinateCalculation_iff_finiteCoordinateIdentities
    {R : A.SectionSevenAffineRadialCompletionInput}
    {W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment} :
    ActualCuspFiberEllipticMarkedCoordinateCalculation R W ↔
      ActualCuspFiberEllipticFiniteCoordinateIdentities R W := by
  constructor
  · intro C
    apply ActualCuspFiberEllipticFiniteCoordinateIdentities.of_coordinateIdentities
    · let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      apply addMonoidHom_ext_of_equiv_pi_single_one
        G.geometricWangSections.circleMappingTorusHOneAddEquiv
      intro i
      rw [AddMonoidHom.comp_apply, coordinateAfterAddEquiv_apply,
        AddEquiv.apply_symm_apply]
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
        simpa using C.degreeTwo 4 (by decide) }

/-- The finite marked calculation implies the complete coordinate-homomorphism identities. -/
public theorem actualCuspFiberEllipticFiniteCoordinateIdentities
    (R : A.SectionSevenAffineRadialCompletionInput)
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment) :
    ActualCuspFiberEllipticFiniteCoordinateIdentities R W :=
  markedCoordinateCalculation_iff_finiteCoordinateIdentities.mp
    (establishedActualCuspFiberEllipticMarkedCoordinateCalculation R W)

namespace ActualCuspFiberEllipticFiniteCoordinateIdentities

/-- The three degree-one evaluations determine the complete coordinate homomorphism. -/
public theorem degreeOneHom
    {R : A.SectionSevenAffineRadialCompletionInput}
    {W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment}
    (C : ActualCuspFiberEllipticFiniteCoordinateIdentities R W) :
    (R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
        (integralSingularHomologyMap 1
          R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap) =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      coordinateAfterAddEquiv G.geometricWangSections.circleMappingTorusHOneAddEquiv 2 :=
  C.coordinateComparison.degreeOne

/-- The four non-suspension degree-two evaluations are precisely fibre-coinvariant
vanishing. -/
public theorem degreeTwoFiberCoinvariantVanishing
    {R : A.SectionSevenAffineRadialCompletionInput}
    {W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment}
    (C : ActualCuspFiberEllipticFiniteCoordinateIdentities R W) :
    ∀ i : Fin 6, i ≠ 4 → i ≠ 5 →
      R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
          W.pulledBackBoundaryBasisBridge
          (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) = 0 := by
  intro i hi4 hi5
  simpa [hi4] using C.degreeTwo i hi5

/-- The remaining degree-two evaluation is exactly the normalization of the first invariant
suspension class. -/
public theorem degreeTwoIndexFour
    {R : A.SectionSevenAffineRadialCompletionInput}
    {W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment}
    (C : ActualCuspFiberEllipticFiniteCoordinateIdentities R W) :
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        W.pulledBackBoundaryBasisBridge
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 1 := by
  simpa using C.degreeTwo 4 (by decide)

end ActualCuspFiberEllipticFiniteCoordinateIdentities

end EstablishedSectionSevenCuspTopology

end SphereSixComplex.Geometry.PaperAnalyticData

end
