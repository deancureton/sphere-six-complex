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

/-- The fibre over the lower overlap collar in the explicit vertex--edge cover of the actual
cusp mapping torus. -/
public noncomputable def actualCuspMappingTorusLowOverlapFiberMap (A : PaperAnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber, (vertexPiece (fun _ : Unit ↦ G.clutching) ∩
      edgePiece (fun _ : Unit ↦ G.clutching) :
        Set (CircleMappingTorus G.clutching))) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact overlapPt (fun _ : Unit ↦ G.clutching) uQuarter_mem_overlapBand ()

/-- Map the oriented lower-overlap fibre into the elliptic interior through the radial cusp
model. -/
public noncomputable def actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber, A.SectionSevenEllipticInterior) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact D.cuspToEllipticInteriorMap.hom.comp
    (G.totalHomotopyEquiv.invFun.comp
      ((⟨Subtype.val, continuous_subtype_val⟩ :
        C((vertexPiece (fun _ : Unit ↦ G.clutching) ∩
            edgePiece (fun _ : Unit ↦ G.clutching) :
              Set (CircleMappingTorus G.clutching)),
          CircleMappingTorus G.clutching)).comp
        (actualCuspMappingTorusLowOverlapFiberMap A)))

/-- After forgetting that the lower fibre lies in the overlap, it is the mapping-torus slice at
the quarter point. -/
public theorem actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap_eq :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap =
      D.cuspToEllipticInteriorMap.hom.comp
        (G.totalHomotopyEquiv.invFun.comp
          (torusPt (fun _ : Unit ↦ G.clutching) () uQuarter)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply ContinuousMap.ext
  intro x
  rfl

/-- Moving the mapping-torus fibre from the vertex to the oriented lower overlap gives a
homotopic map into the elliptic interior. -/
public theorem actualCuspMappingTorusFiberToEllipticInteriorMap_homotopic_lowOverlap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ContinuousMap.Homotopic
      D.actualCuspMappingTorusFiberToEllipticInteriorMap
      D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap_eq]
  exact ContinuousMap.Homotopic.comp
    (.refl D.cuspToEllipticInteriorMap.hom)
    (ContinuousMap.Homotopic.comp
      (.refl G.totalHomotopyEquiv.invFun)
      ⟨(torusPtHomotopy (fun _ : Unit ↦ G.clutching) () uQuarter).symm⟩)

/-- The missing geometric compatibility: the period-marked fibre map is the restriction of the
actual cusp-to-elliptic map to the fibre of the radial mapping torus, up to homotopy. -/
public def CanonicalCuspFiberBandTopologicalCompatibility : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  ContinuousMap.Homotopic (actualCuspMappingTorusFiberToEllipticInteriorMap D)
    (canonicalCuspFiberToEllipticInteriorMap D)

/-- The topological cusp--band square is equivalent to its oriented low-overlap form.  Thus the
remaining comparison is exactly between the explicit overlap leg of the Wang cover and the
canonical affine-band map. -/
public theorem canonicalCuspFiberBandTopologicalCompatibility_iff_lowOverlap :
    D.CanonicalCuspFiberBandTopologicalCompatibility ↔
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      ContinuousMap.Homotopic
        D.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap
        D.canonicalCuspFiberToEllipticInteriorMap := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  unfold CanonicalCuspFiberBandTopologicalCompatibility
  constructor
  · intro h
    exact D.actualCuspMappingTorusFiberToEllipticInteriorMap_homotopic_lowOverlap.symm.trans h
  · intro h
    exact D.actualCuspMappingTorusFiberToEllipticInteriorMap_homotopic_lowOverlap.trans h

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
