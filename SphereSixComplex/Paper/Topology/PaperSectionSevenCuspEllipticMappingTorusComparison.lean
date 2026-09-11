module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCompletionReduction
public import SphereSixComplex.Paper.Geometry.CuspCollarPairProperness
public import SphereSixComplex.Paper.Geometry.EllipticRealPeriodProductTrivialization
public import SphereSixComplex.Paper.Topology.PaperCuspBoundaryUniversalCover

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
open EllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData} (D : A.EllipticTwoDiscCoverData)

namespace EllipticTwoDiscCoverData

/-- The actual cusp-to-elliptic map, expressed on the radial circle mapping torus. -/
public noncomputable def cuspMappingTorusToEllipticInteriorMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(CircleMappingTorus G.clutching, A.ellipticInterior) := by
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
    A.cuspRawHomologyOneEquiv x =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.geometricWangSections.circleMappingTorusHOneAddEquiv
        (integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun x) := by
  rfl

/-- Raw degree-two cusp coordinates are the geometric Wang coordinates after radial
normalization. -/
public theorem actualCuspRawHomologyTwoEquiv_apply_mappingTorus (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    A.cuspRawHomologyTwoEquiv x =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.geometricWangSections.circleMappingTorusHTwoAddEquiv
        (integralSingularHomologyMap 2 G.totalHomotopyEquiv.toFun x) := by
  rfl




end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end
