module

public import
  SphereSixComplex.Topology.PaperSectionSevenCuspActualCoordinateScalarsFromExistingGeometry
public import
  SphereSixComplex.Topology.PaperSectionSevenCanonicalCuspFiberRadialHomotopyCompletion

/-!
# The remaining positive cusp-meridian coordinate

The first cusp fibre generator already has elliptic-interior coordinate `12`.  Consequently the
positive meridian has coordinate `1` exactly when, after inclusion in the elliptic interior,
twelve copies of that meridian equal the first fibre generator.  This is the integral-homology
form of the finite-meridian full-iterate relation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticInteriorMarkedCycleData
open SectionSevenEllipticTwoDiscCoverData

variable {A : PaperAnalyticData}

namespace EstablishedSectionSevenCuspTopology

/-- The geometric full-iterate relation left by the degree-one cusp calculation. -/
public def ActualCuspDegreeOneIndexTwoFullIterateRelation
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  (12 : ℤ) •
      integralSingularHomologyMap 1 R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap
        (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
          (Pi.single (2 : Fin 3) 1)) =
    integralSingularHomologyMap 1 R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
        (Pi.single (0 : Fin 3) 1))

/-- The full-iterate relation is exactly equivalent to the remaining scalar equality. -/
public theorem actualCuspDegreeOneIndexTwo_iff_fullIterateRelation
    (R : A.SectionSevenAffineRadialCompletionInput) :
    (let G := A.actualCuspRadialClutchingData
     let _ := G.fiberTopology
     ((R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment).comp
          (integralSingularHomologyMap 1
            R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap))
        (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
          (Pi.single (2 : Fin 3) 1)) = 1) ↔
      ActualCuspDegreeOneIndexTwoFullIterateRelation R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let E := R.homologyAlignment.actualHomologyCoordinates
    |>.normalizedEllipticInteriorHomologyOneEquiv
  let f := R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment
  let x₂ := integralSingularHomologyMap 1
    R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
        (Pi.single (2 : Fin 3) 1))
  let x₀ := integralSingularHomologyMap 1
    R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
        (Pi.single (0 : Fin 3) 1))
  have hx₀ : f x₀ = 12 := by
    let hTop := canonicalCuspFiberBandTopologicalCompatibility R
    simpa [f, x₀, SectionSevenEllipticTwoDiscCoverData.ellipticInteriorDegreeOneCoordinateHom,
      coordinateAfterAddEquiv_apply] using
        congrFun (affineActualCuspDegreeOneFiberBasis_scalarValues R hTop) 0
  constructor
  · intro hx₂
    change (12 : ℤ) • x₂ = x₀
    apply E.injective
    funext i
    fin_cases i
    change f ((12 : ℤ) • x₂) = f x₀
    rw [map_zsmul, hx₀]
    change (12 : ℤ) * f x₂ = 12
    simpa [f, x₂] using congrArg (fun z : ℤ ↦ (12 : ℤ) * z) hx₂
  · intro hrel
    change f x₂ = 1
    change (12 : ℤ) • x₂ = x₀ at hrel
    have h := congrArg f hrel
    rw [map_zsmul, hx₀] at h
    change (12 : ℤ) * f x₂ = 12 at h
    omega

end EstablishedSectionSevenCuspTopology

end SphereSixComplex.Geometry.PaperAnalyticData

end
