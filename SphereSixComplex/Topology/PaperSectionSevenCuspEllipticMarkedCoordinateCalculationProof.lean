module

public import SphereSixComplex.Topology.PaperSectionSevenCuspEllipticCoordinateFiniteReduction

/-!
# Finite cusp coordinate evaluations

The corrected marked coordinates are the values of the two integral linear functionals on the
standard raw cusp bases.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticInteriorMarkedCycleData
open SectionSevenEllipticTwoDiscCoverData

/-- The corrected degree-one functional has basis values `[12, 0, 1]`. -/
public theorem actualCuspEllipticDegreeOneRawCoordinate_basisValues :
    (fun i : Fin 3 ↦
      actualCuspEllipticDegreeOneRawCoordinate (Pi.single i 1)) = ![12, 0, 1] := by
  funext i
  fin_cases i <;> simp [actualCuspEllipticDegreeOneRawCoordinate]

/-- The corrected degree-two fibre functional has basis values `[0, 12, 2, 0, 1, 0]`. -/
public theorem actualCuspEllipticDegreeTwoFiberRawCoordinate_basisValues :
    (fun i : Fin 6 ↦
      actualCuspEllipticDegreeTwoFiberRawCoordinate (Pi.single i 1)) =
        ![0, 12, 2, 0, 1, 0] := by
  funext i
  fin_cases i <;> simp [actualCuspEllipticDegreeTwoFiberRawCoordinate]

namespace EstablishedSectionSevenCuspTopology

variable {A : PaperAnalyticData}

/-- Naturality for the actual cusp inclusion implies all eight marked basis evaluations. -/
public theorem actualCuspFiberEllipticMarkedCoordinateCalculation_of_inclusionNaturality
    {R : A.SectionSevenAffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment}
    (I : R.twoDiscCover.SectionSevenCuspEllipticInclusionNaturality
      R.homologyAlignment G₀) :
    ActualCuspFiberEllipticMarkedCoordinateCalculation R G₀ := by
  apply markedCoordinateCalculation_iff_finiteCoordinateIdentities.mpr
  refine { coordinateComparison := { degreeOne := ?_, degreeTwoFiber := ?_ } }
  · let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    apply addMonoidHom_ext_of_equiv_pi_single_one
      G.geometricWangSections.circleMappingTorusHOneAddEquiv
    intro i
    let x := A.actualCuspRawHomologyOneEquiv.symm (Pi.single i 1)
    have hx : integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun x =
        G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm (Pi.single i 1) := by
      apply G.geometricWangSections.circleMappingTorusHOneAddEquiv.injective
      rw [← actualCuspRawHomologyOneEquiv_apply_mappingTorus A x]
      simp [x]
    have hI := DFunLike.congr_fun I.degreeOne x
    change R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment
        (integralSingularHomologyMap 1 R.twoDiscCover.cuspToEllipticInteriorMap.hom x) =
      actualCuspEllipticDegreeOneRawCoordinate (A.actualCuspRawHomologyOneEquiv x) at hI
    rw [show A.actualCuspRawHomologyOneEquiv x = Pi.single i 1 by simp [x]] at hI
    rw [AddMonoidHom.comp_apply]
    change R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment
        (integralSingularHomologyMap 1 R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm (Pi.single i 1))) =
      actualCuspEllipticDegreeOneRawCoordinate
        (G.geometricWangSections.circleMappingTorusHOneAddEquiv
          (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm (Pi.single i 1)))
    rw [AddEquiv.apply_symm_apply]
    rw [← hx, ← R.twoDiscCover.cuspToEllipticInteriorMap_homology_mappingTorusModel 1 x]
    exact hI
  · let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    apply addMonoidHom_ext_of_equiv_pi_single_one
      G.geometricWangSections.circleMappingTorusHTwoAddEquiv
    intro i
    let x := A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)
    have hx : integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun x =
        G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1) := by
      apply G.geometricWangSections.circleMappingTorusHTwoAddEquiv.injective
      rw [← actualCuspRawHomologyTwoEquiv_apply_mappingTorus A x]
      simp [x]
    have hI := DFunLike.congr_fun I.degreeTwoFiber x
    change R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment G₀
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspToEllipticInteriorMap.hom x) =
      actualCuspEllipticDegreeTwoFiberRawCoordinate (A.actualCuspRawHomologyTwoEquiv x) at hI
    rw [show A.actualCuspRawHomologyTwoEquiv x = Pi.single i 1 by simp [x]] at hI
    rw [AddMonoidHom.comp_apply]
    change R.twoDiscCover.ellipticInteriorDegreeTwoFiberCoordinateHom R.homologyAlignment G₀
        (integralSingularHomologyMap 2 R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap
          (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1))) =
      actualCuspEllipticDegreeTwoFiberRawCoordinate
        (G.geometricWangSections.circleMappingTorusHTwoAddEquiv
          (G.geometricWangSections.circleMappingTorusHTwoAddEquiv.symm (Pi.single i 1)))
    rw [AddEquiv.apply_symm_apply]
    rw [← hx, ← R.twoDiscCover.cuspToEllipticInteriorMap_homology_mappingTorusModel 2 x]
    exact hI

/-- The paper's cycle-level cusp decomposition is sufficient for the marked calculation. -/
public theorem actualCuspFiberEllipticMarkedCoordinateCalculation_of_cycleDecomposition
    {R : A.SectionSevenAffineRadialCompletionInput}
    {G₀ : R.twoDiscCover.SectionSevenCuspPulledBackBoundaryBasisBridge
      R.homologyAlignment}
    (C : A.SectionSevenEllipticInteriorCycleDecomposition
      R.homologyAlignment.actualHomologyCoordinates
      (R.twoDiscCover.cuspNormalizedDegreeTwoSplitting R.homologyAlignment G₀)) :
    ActualCuspFiberEllipticMarkedCoordinateCalculation R G₀ :=
  actualCuspFiberEllipticMarkedCoordinateCalculation_of_inclusionNaturality
    (sectionSevenEllipticInteriorCycleDecomposition_iff_inclusionNaturality.mp C)

end EstablishedSectionSevenCuspTopology

end SphereSixComplex.Geometry.PaperAnalyticData

end
