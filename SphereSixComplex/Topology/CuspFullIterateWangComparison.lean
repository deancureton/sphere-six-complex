module
public import SphereSixComplex.Topology.CuspEllipticHomologyFullIterate
public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianDegreeOneProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspDegreeOneIndexTwoProof

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex
open StandardCircleHomologyLiftDegree

public theorem loopHomologyClass_eq_of_pointwise {X : Type} [TopologicalSpace X]
    {x y : X} (p : Path x x) (q : Path y y) (h : ∀ t, p t = q t) :
    loopHomologyClass p = loopHomologyClass q := by
  have hxy : x = y := p.source.symm.trans ((h 0).trans q.source)
  erw [← loopHomologyClass_cast q hxy]
  congr 1
  ext t
  exact h t

namespace Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.Topology.FirstHurewiczProof
open CuspPuncturedCollarBridge CuspPuncturedCollarBridge.CuspFiberSpecializationNormalization
variable (A : PaperAnalyticData)

public theorem actualCuspBridgeMeridian_hurewicz :
    hurewiczFunction A.actualCuspOverlapBase A.actualCuspAffineBridgeMeridian =
      loopHomologyClass A.actualCuspAngularProjectedLoop := by
  erw [actualCuspAffineBridgeMeridian,
    A.actualCuspAffineBridgeMeridian_eq_angularProjectedLoop, hurewiczFunction_baseEq]
  rfl

public theorem actualCuspOverlapToInterior_comp_collar
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    A.actualCuspOverlapToEllipticInterior.comp
      (⟨A.cuspCollarToStarOverlapHomeomorph,
        A.cuspCollarToStarOverlapHomeomorph.continuous⟩ :
          C(puncturedLocalCuspQuotient A.starCuspWitness, _)) =
      D.cuspToEllipticInteriorMap.hom := by
  ext x
  rfl

public theorem actualCuspBridgeMeridian_homology_image
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    integralSingularHomologyMap 1 A.actualCuspOverlapToEllipticInterior
      (hurewiczFunction A.actualCuspOverlapBase A.actualCuspAffineBridgeMeridian) =
    integralSingularHomologyMap 1 D.cuspToEllipticInteriorMap.hom
      (loopHomologyClass A.actualCuspAngularPuncturedLoop) := by
  erw [A.actualCuspBridgeMeridian_hurewicz]
  erw [← A.actualCuspOverlapToInterior_comp_collar D]
  erw [integralSingularHomologyMap_loopHomologyClass,
    integralSingularHomologyMap_loopHomologyClass]
  apply loopHomologyClass_eq_of_pointwise
  intro t
  apply Subtype.ext
  rfl

public theorem actualCuspRawTwo_homology_image
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap 1 D.cuspMappingTorusToEllipticInteriorMap
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
        (Pi.single (2 : Fin 3) 1)) =
    -integralSingularHomologyMap 1 A.actualCuspOverlapToEllipticInterior
      (hurewiczFunction A.actualCuspOverlapBase A.actualCuspAffineBridgeMeridian) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change integralSingularHomologyMap 1 D.cuspMappingTorusToEllipticInteriorMap
    (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
      (Pi.single (2 : Fin 3) 1)) = _
  erw [A.actualCuspRawDegreeOneThirdBasis_eq_selectedPositiveMeridianClass,
    A.actualCuspSelectedPositiveMeridianClass_eq_neg_explicit, map_neg,
    A.cuspMappingTorusMeridianHomologyClass_eq_actualCuspAngularPuncturedLoop_image,
    ← D.cuspToEllipticInteriorMap_homology_mappingTorusModel]
  erw [A.actualCuspBridgeMeridian_homology_image D]
  rfl

end Geometry.PaperAnalyticData
end SphereSixComplex
end
