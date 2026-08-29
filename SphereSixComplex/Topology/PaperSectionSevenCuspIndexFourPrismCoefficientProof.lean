module

public import SphereSixComplex.Topology.PaperSectionSevenCuspInvariantSuspensionPrismNaturality

/-!
# The index-four prism coefficient

The fourth target prism of a cusp prism geometric package is the image of the first invariant
suspension class of the actual cusp collar.  Its two normalized elliptic-interior coordinates are
therefore intrinsic to the collar inclusion: the swept one already vanishes, and the fibre one is
the fourth raw cusp fibre coordinate.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscCoverData
open SectionSevenEllipticTwoDiscHomologyCoordinates
open SectionSevenEllipticInteriorMarkedCycleData
open SphereSixComplex.CircleMappingTorusHomologyBases

variable {A : PaperAnalyticData} {D : A.SectionSevenEllipticTwoDiscCoverData}
  {N : A.EllipticBandHomologyAlignment D}
  {G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- The fibre coordinate of the fourth target prism is the fibre coordinate of the included
fourth raw cusp basis class. -/
public theorem indexFourPrismCoefficient_eq_cuspFiberCoordinate
    (C : D.CuspEllipticMappingTorusPrismGeometricData N G₀) :
    (N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
        (D.cuspNormalizedDegreeTwoSplitting N G₀))
        (C.targetImageCycle 4).homologyClass 0 =
      N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
        (D.cuspNormalizedDegreeTwoSplitting N G₀)
        (cuspToEllipticUnionHomology D 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) 0 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let E := N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv
    (D.cuspNormalizedDegreeTwoSplitting N G₀)
  let x := A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)
  have hx :
      integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun x =
        G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
          (Pi.single (4 : Fin 6) 1) := by
    apply G.geometricWangSections.circleMappingTorusHTwoAddEquiv.injective
    rw [← actualCuspRawHomologyTwoEquiv_apply_mappingTorus A x]
    simp [x]
  have hhom := DFunLike.congr_fun
    (coordinate_comp_integralSingularHomologyMap_eq_of_homotopic
      C.modelHomotopy 2 (coordinateAfterAddEquiv E 0))
    (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
      (Pi.single (4 : Fin 6) 1))
  simp only [AddMonoidHom.comp_apply, coordinateAfterAddEquiv_apply] at hhom
  calc
    E (C.targetImageCycle 4).homologyClass 0 =
        E (integralSingularHomologyMap 2 C.referenceMap
          (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
            (Pi.single (4 : Fin 6) 1))) 0 := by
      rw [C.referenceMap_on_basis 4]
    _ = E (integralSingularHomologyMap 2 D.cuspMappingTorusToEllipticInteriorMap
          (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm
            (Pi.single (4 : Fin 6) 1))) 0 := hhom.symm
    _ = E (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x) 0 := by
      rw [D.cuspToEllipticInteriorMap_homology_mappingTorusModel 2 x, hx]
    _ = _ := D.ellipticInteriorDegreeTwoFiberCoordinateHom_cuspToEllipticInteriorMap N G₀ x

/-- Given the fourth raw cusp fibre coordinate, the index-four prism coefficient calculation
follows for every prism geometric package. -/
public theorem normalizedIndexFourPrismCoefficientCalculation_of_cuspFiberCoordinate
    (C : D.CuspEllipticMappingTorusPrismGeometricData N G₀)
    (h : N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
        (D.cuspNormalizedDegreeTwoSplitting N G₀)
        (cuspToEllipticUnionHomology D 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) 0 = 1) :
    D.NormalizedIndexFourPrismCoefficientCalculation C :=
  ⟨(indexFourPrismCoefficient_eq_cuspFiberCoordinate C).trans h⟩

/-- The residual scalar in its geometric form: the marked elliptic-interior fibre coordinate of
the included first invariant-suspension cusp class.  This is the same number as the normalized
union coordinate used above. -/
public theorem cuspFiberCoordinate_eq_ellipticInteriorDegreeTwoFiberCoordinateHom :
    N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
        (D.cuspNormalizedDegreeTwoSplitting N G₀)
        (cuspToEllipticUnionHomology D 2
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) 0 =
      D.ellipticInteriorDegreeTwoFiberCoordinateHom N G₀
        (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) :=
  (D.ellipticInteriorDegreeTwoFiberCoordinateHom_cuspToEllipticInteriorMap N G₀
    (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))).symm

/-- Wiring for the established Section 7 cusp completion: the single scalar identity for the
actual affine radial input discharges the index-four prism coefficient calculation for every
prism geometric package over that input. -/
public theorem normalizedIndexFourPrismCoefficientCalculation_of_actualCuspFiberCoordinate
    (R : A.SectionSevenAffineRadialCompletionInput)
    (G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment)
    (C : R.twoDiscCover.CuspEllipticMappingTorusPrismGeometricData R.homologyAlignment
      G₀)
    (h : R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment
        G₀
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 1) :
    R.twoDiscCover.NormalizedIndexFourPrismCoefficientCalculation C :=
  normalizedIndexFourPrismCoefficientCalculation_of_cuspFiberCoordinate C
    ((cuspFiberCoordinate_eq_ellipticInteriorDegreeTwoFiberCoordinateHom).trans h)

end SphereSixComplex.Geometry.PaperAnalyticData

end
