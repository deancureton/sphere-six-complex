module

public import SphereSixComplex.Topology.PaperSectionSevenCuspCycleDecompositionReduction

/-!
# Mapping-torus model for the cusp-to-elliptic inclusion

The radial cusp collar is homotopy equivalent to its circle mapping torus.  Conjugating the
actual cusp-to-elliptic map by this equivalence gives a canonical model map.  Homotopy invariance
then reduces the two remaining inclusion-coordinate identities to calculations on the mapping
torus in its geometric Wang coordinates.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open CategoryTheory
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

namespace SectionSevenEllipticTwoDiscCoverData

/-- The actual cusp-to-elliptic map, expressed on the radial circle mapping torus. -/
public noncomputable def cuspMappingTorusToEllipticInteriorMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(CircleMappingTorus G.clutching, A.SectionSevenEllipticInterior) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact D.cuspToEllipticInteriorMap.hom.comp G.totalHomotopyEquiv.invFun

/-- The actual collar map is homotopic to the mapping-torus model after radial normalization. -/
public theorem cuspToEllipticInteriorMap_homotopic_mappingTorusModel :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    D.cuspToEllipticInteriorMap.hom.Homotopic
      (D.cuspMappingTorusToEllipticInteriorMap.comp G.totalHomotopyEquiv.toFun) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  have h := ContinuousMap.Homotopic.comp
    (.refl D.cuspToEllipticInteriorMap.hom) G.totalHomotopyEquiv.left_inv
  exact h.symm

/-- On singular homology, the actual collar map factors through radial normalization and the
mapping-torus model. -/
public theorem cuspToEllipticInteriorMap_homology_mappingTorusModel (k : ℕ)
    (x : IntegralSingularHomology k (A.openEmbeddingStarData.collarSource 0)) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap k D.cuspToEllipticInteriorMap.hom x =
      integralSingularHomologyMap k D.cuspMappingTorusToEllipticInteriorMap
        (integralSingularHomologyMap k G.totalHomotopyEquiv.toFun x) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  calc
    integralSingularHomologyMap k D.cuspToEllipticInteriorMap.hom x =
        integralSingularHomologyMap k
          (D.cuspMappingTorusToEllipticInteriorMap.comp G.totalHomotopyEquiv.toFun) x := by
      change ConcreteCategory.hom
          (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
            (TopCat.ofHom D.cuspToEllipticInteriorMap.hom)) x = _
      rw [integralSingularHomologyMap_eq_of_homotopic
        D.cuspToEllipticInteriorMap_homotopic_mappingTorusModel k]
      rfl
    _ = _ := DFunLike.congr_fun (integralSingularHomologyMap_comp k _ _) x

/-- Raw degree-one cusp coordinates are the geometric Wang coordinates after radial
normalization. -/
public theorem actualCuspRawHomologyOneEquiv_apply_mappingTorus (A : PaperAnalyticData)
    (x : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0)) :
    A.actualCuspRawHomologyOneEquiv x =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.geometricWangSections.circleMappingTorusHOneAddEquiv
        (integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun x) := by
  rfl

/-- Raw degree-two cusp coordinates are the geometric Wang coordinates after radial
normalization. -/
public theorem actualCuspRawHomologyTwoEquiv_apply_mappingTorus (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    A.actualCuspRawHomologyTwoEquiv x =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.geometricWangSections.circleMappingTorusHTwoAddEquiv
        (integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun x) := by
  rfl

/-- Postcomposing induced singular-homology maps with any additive coordinate preserves
homotopy invariance. -/
public theorem coordinate_comp_integralSingularHomologyMap_eq_of_homotopic
    {X Y : Type} {M : Type*} [TopologicalSpace X] [TopologicalSpace Y] [AddMonoid M]
    {f g : C(X, Y)} (h : f.Homotopic g) (k : ℕ)
    (coordinate : IntegralSingularHomology k Y →+ M) :
    coordinate.comp (integralSingularHomologyMap k f) =
      coordinate.comp (integralSingularHomologyMap k g) := by
  apply AddMonoidHom.ext
  intro x
  apply congrArg coordinate
  change ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom f)) x =
    ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom g)) x
  rw [integralSingularHomologyMap_eq_of_homotopic h k]

/-- The exact remaining calculation on the radial mapping-torus model.  The model inclusion must
send the meridian to the first elliptic-interior coordinate and the first invariant suspension
class to the normalized elliptic fibre coordinate. -/
public structure CuspEllipticMappingTorusCoordinateComparison
    (N : A.EllipticBandHomologyAlignment D)
    (G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) : Prop where
  degreeOne :
    (D.ellipticInteriorDegreeOneCoordinateHom N).comp
        (integralSingularHomologyMap 1 D.cuspMappingTorusToEllipticInteriorMap) =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      coordinateAfterAddEquiv G.geometricWangSections.circleMappingTorusHOneAddEquiv 2
  degreeTwoFiber :
    (D.ellipticInteriorDegreeTwoFiberCoordinateHom N G₀).comp
        (integralSingularHomologyMap 2 D.cuspMappingTorusToEllipticInteriorMap) =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      coordinateAfterAddEquiv G.geometricWangSections.circleMappingTorusHTwoAddEquiv 4

/-- A geometric route to the two mapping-torus coordinate calculations.  A reference map has
explicit marked coordinates, and the actual mapping-torus model is homotopic to it. -/
public structure CuspEllipticMappingTorusGeometricComparison
    (N : A.EllipticBandHomologyAlignment D)
    (G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N) where
  referenceMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(CircleMappingTorus G.clutching, A.SectionSevenEllipticInterior)
  modelHomotopy :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    D.cuspMappingTorusToEllipticInteriorMap.Homotopic referenceMap
  referenceDegreeOne :
    (D.ellipticInteriorDegreeOneCoordinateHom N).comp
        (integralSingularHomologyMap 1 referenceMap) =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      coordinateAfterAddEquiv G.geometricWangSections.circleMappingTorusHOneAddEquiv 2
  referenceDegreeTwoFiber :
    (D.ellipticInteriorDegreeTwoFiberCoordinateHom N G₀).comp
        (integralSingularHomologyMap 2 referenceMap) =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      coordinateAfterAddEquiv G.geometricWangSections.circleMappingTorusHTwoAddEquiv 4

namespace CuspEllipticMappingTorusGeometricComparison

variable {D : A.SectionSevenEllipticTwoDiscCoverData}
variable {N : A.EllipticBandHomologyAlignment D}
variable {G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- Homotopy invariance transports the marked reference-map calculation to the actual model. -/
public theorem coordinateComparison
    (C : D.CuspEllipticMappingTorusGeometricComparison N G₀) :
    D.CuspEllipticMappingTorusCoordinateComparison N G₀ where
  degreeOne := by
    rw [coordinate_comp_integralSingularHomologyMap_eq_of_homotopic C.modelHomotopy]
    exact C.referenceDegreeOne
  degreeTwoFiber := by
    rw [coordinate_comp_integralSingularHomologyMap_eq_of_homotopic C.modelHomotopy]
    exact C.referenceDegreeTwoFiber

end CuspEllipticMappingTorusGeometricComparison

namespace CuspEllipticMappingTorusCoordinateComparison

variable {D : A.SectionSevenEllipticTwoDiscCoverData}
variable {N : A.EllipticBandHomologyAlignment D}
variable {G₀ : D.SectionSevenCuspPulledBackBoundaryBasisBridge N}

/-- The two mapping-torus coordinate calculations imply the two actual inclusion-naturality
squares. -/
public theorem inclusionNaturality
    (C : D.CuspEllipticMappingTorusCoordinateComparison N G₀) :
    D.SectionSevenCuspEllipticInclusionNaturality N G₀ where
  degreeOne := by
    apply AddMonoidHom.ext
    intro x
    change D.ellipticInteriorDegreeOneCoordinateHom N
      (integralSingularHomologyMap 1 D.cuspToEllipticInteriorMap.hom x) = _
    rw [D.cuspToEllipticInteriorMap_homology_mappingTorusModel 1 x]
    have hx := DFunLike.congr_fun C.degreeOne
      (integralSingularHomologyMap 1
        A.actualCuspRadialClutchingData.totalHomotopyEquiv.toFun x)
    rw [coordinateAfterAddEquiv_apply,
      actualCuspRawHomologyOneEquiv_apply_mappingTorus]
    exact hx
  degreeTwoFiber := by
    apply AddMonoidHom.ext
    intro x
    change D.ellipticInteriorDegreeTwoFiberCoordinateHom N G₀
      (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x) = _
    rw [D.cuspToEllipticInteriorMap_homology_mappingTorusModel 2 x]
    have hx := DFunLike.congr_fun C.degreeTwoFiber
      (integralSingularHomologyMap 2
        A.actualCuspRadialClutchingData.totalHomotopyEquiv.toFun x)
    rw [coordinateAfterAddEquiv_apply,
      actualCuspRawHomologyTwoEquiv_apply_mappingTorus]
    exact hx

end CuspEllipticMappingTorusCoordinateComparison

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end
