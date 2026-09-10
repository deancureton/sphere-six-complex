module
public import SphereSixComplex.Paper.Topology.CuspEllipticHomologyFullIterate
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspMeridianDegreeOneProof
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspDegreeOneIndexTwoProof

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
open SphereSixComplex.Topology Hurewicz.Chains
open CuspPuncturedCollarBridge CuspPuncturedCollarBridge.CuspFiberSpecializationNormalization
variable (A : PaperAnalyticData)

public theorem cuspBridgeMeridian_hurewicz :
    hurewiczFunction A.cuspOverlapBase A.cuspAffineBridgeMeridian =
      loopHomologyClass A.cuspAngularProjectedLoop := by
  erw [cuspAffineBridgeMeridian,
    A.cuspAffineBridgeMeridian_eq_angularProjectedLoop, hurewiczFunction_baseEq]
  rfl

public theorem cuspOverlapToInterior_comp_collar
    (D : A.EllipticTwoDiscCoverData) :
    A.cuspOverlapToEllipticInterior.comp
      (⟨A.cuspCollarToStarOverlapHomeomorph,
        A.cuspCollarToStarOverlapHomeomorph.continuous⟩ :
          C(puncturedLocalCuspQuotient A.starCuspWitness, _)) =
      D.cuspToEllipticInteriorMap.hom := by
  ext x
  rfl

public theorem cuspBridgeMeridian_homology_image
    (D : A.EllipticTwoDiscCoverData) :
    integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
      (hurewiczFunction A.cuspOverlapBase A.cuspAffineBridgeMeridian) =
    integralSingularHomologyMap 1 D.cuspToEllipticInteriorMap.hom
      (loopHomologyClass A.cuspAngularPuncturedLoop) := by
  erw [A.cuspBridgeMeridian_hurewicz]
  erw [← A.cuspOverlapToInterior_comp_collar D]
  erw [integralSingularHomologyMap_loopHomologyClass,
    integralSingularHomologyMap_loopHomologyClass]
  apply loopHomologyClass_eq_of_pointwise
  intro t
  apply Subtype.ext
  rfl

public theorem cuspRawTwo_homology_image
    (D : A.EllipticTwoDiscCoverData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap 1 D.cuspMappingTorusToEllipticInteriorMap
      (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
        (Pi.single (2 : Fin 3) 1)) =
    -integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
      (hurewiczFunction A.cuspOverlapBase A.cuspAffineBridgeMeridian) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change integralSingularHomologyMap 1 D.cuspMappingTorusToEllipticInteriorMap
    (G.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
      (Pi.single (2 : Fin 3) 1)) = _
  erw [A.cuspRawDegreeOneThirdBasis_eq_selectedPositiveMeridianClass,
    A.cuspSelectedPositiveMeridianClass_eq_neg_explicit, map_neg,
    A.cuspMappingTorusMeridianHomologyClass_eq_actualCuspAngularPuncturedLoop_image,
    ← D.cuspToEllipticInteriorMap_homology_mappingTorusModel]
  erw [A.cuspBridgeMeridian_homology_image D]
  rfl

end Geometry.PaperAnalyticData
end SphereSixComplex
end
