module

public import SphereSixComplex.Topology.PaperSectionSevenCuspPrismGeometricDataProof

/-!
# Finite reduction of the remaining cusp coordinates

The degree-one identity in the cusp comparison is an equality of homomorphisms out of a free
rank-three group.  It is therefore enough to check the three marked basis classes.  Together
with the five degree-two basis evaluations already used by the comparison, this gives a finite
statement of the remaining geometric input.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticInteriorMarkedCycleData
open SectionSevenEllipticTwoDiscCoverData

variable {A : PaperAnalyticData}

namespace EstablishedSectionSevenCuspTopology

/-- The eight marked scalar evaluations remaining in the cusp-to-elliptic comparison. -/
public structure ActualCuspFiberEllipticFiniteCoordinateIdentities
    (R : A.SectionSevenAffineRadialCompletionInput)
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment) : Prop where
  /-- The three marked degree-one basis classes have the meridian coordinate. -/
  degreeOne :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ∀ i : Fin 3,
      ((R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
          (integralSingularHomologyMap 1
            R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap))
        (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm (Pi.single i 1)) =
          (Pi.single i 1 : Fin 3 → ℤ) 2
  /-- The five non-boundary degree-two basis classes have the marked fibre coordinate. -/
  degreeTwo : ∀ i : Fin 6, i ≠ 5 →
    R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        W.pulledBackBoundaryBasisBridge
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) =
      if i = 4 then 1 else 0

/-- The remaining geometric input, reduced to eight scalar evaluations on marked bases. -/
public axiom actualCuspFiberEllipticFiniteCoordinateIdentities
    (R : A.SectionSevenAffineRadialCompletionInput)
    (W : R.twoDiscCover.SectionSevenCuspWangBandCompatibility R.homologyAlignment) :
    ActualCuspFiberEllipticFiniteCoordinateIdentities R W

namespace ActualCuspFiberEllipticFiniteCoordinateIdentities

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
  degreeOne := by
    dsimp only
    let _ := A.actualCuspRadialClutchingData.fiberTopology
    intro i
    have hi := DFunLike.congr_fun hOne
      (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
        (Pi.single i 1))
    simpa only [coordinateAfterAddEquiv_apply, AddEquiv.apply_symm_apply] using hi
  degreeTwo i hi5 := by
    by_cases hi4 : i = 4
    · subst i
      simpa using hFour
    · simp only [hi4, ite_false]
      exact hVanish i hi4 hi5

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
      coordinateAfterAddEquiv G.geometricWangSections.circleMappingTorusHOneAddEquiv 2 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply addMonoidHom_ext_of_equiv_pi_single_one
    G.geometricWangSections.circleMappingTorusHOneAddEquiv
  intro i
  rw [coordinateAfterAddEquiv_apply, AddEquiv.apply_symm_apply]
  exact C.degreeOne i

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
