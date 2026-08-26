module

public import SphereSixComplex.Topology.PaperSectionSevenCanonicalCuspFiberBandMap

/-!
# The topological cusp-fibre-to-band square

The radial clutching model includes its fibre into the actual cusp collar.  Independently, the
period marking gives a canonical map from that fibre into the overlap of the two elliptic sides.
This file states the precise space-level compatibility needed before any naturality comparison
between the Wang and Mayer--Vietoris connecting morphisms can be made.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

namespace SectionSevenEllipticTwoDiscCoverData

/-- Include the mapping-torus fibre into the actual punctured cusp collar. -/
public noncomputable def actualCuspMappingTorusFiberToCollarMap (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber, A.openEmbeddingStarData.collarSource 0) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact G.totalHomotopyEquiv.invFun.comp
    (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching))

/-- Map the mapping-torus fibre into the elliptic interior through the actual cusp collar. -/
public noncomputable def actualCuspMappingTorusFiberToEllipticInteriorMap
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber, A.SectionSevenEllipticInterior) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact D.cuspToEllipticInteriorMap.hom.comp (actualCuspMappingTorusFiberToCollarMap A)

/-- Map the same fibre into the elliptic interior through the canonical central-band map. -/
public noncomputable def canonicalCuspFiberToEllipticInteriorMap
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber, A.SectionSevenEllipticInterior) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact (⟨Subtype.val, continuous_subtype_val⟩ :
      C((D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior),
        A.SectionSevenEllipticInterior)).comp D.canonicalCuspFiberToBandMap

/-- The missing geometric compatibility: the period-marked fibre map is the restriction of the
actual cusp-to-elliptic map to the fibre of the radial mapping torus, up to homotopy. -/
public def CanonicalCuspFiberBandTopologicalCompatibility : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  ContinuousMap.Homotopic (actualCuspMappingTorusFiberToEllipticInteriorMap D)
    (canonicalCuspFiberToEllipticInteriorMap D)

/-- The space-level compatibility induces the corresponding equality on singular homology. -/
public theorem canonicalCuspFiberBand_homology_naturality
    (h : D.CanonicalCuspFiberBandTopologicalCompatibility) (k : ℕ) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    integralSingularHomologyMap k (actualCuspMappingTorusFiberToEllipticInteriorMap D) =
      integralSingularHomologyMap k (canonicalCuspFiberToEllipticInteriorMap D) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  ext x
  change ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (actualCuspMappingTorusFiberToEllipticInteriorMap D))) x =
    ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (canonicalCuspFiberToEllipticInteriorMap D))) x
  rw [integralSingularHomologyMap_eq_of_homotopic h k]

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
