module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenPositiveDegreeRealization

/-!
# Pulling the elliptic two-disc cover back to the cusp collar

The actual cusp-to-elliptic inclusion pulls the two-disc cover back to a binary open cover of
the cusp collar.  Naturality of the canonical chain-level Mayer--Vietoris boundary then reduces
the orientation of the included cusp suspension class to a computation in this pulled-back
cover.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set TopologicalSpace

namespace SphereSixComplex.Geometry.AnalyticData

open EllipticTwoDiscHomologyCoordinates

variable {A : AnalyticData} (D : A.EllipticTwoDiscCoverData)

namespace EllipticTwoDiscCoverData

/-- The actual inclusion of the cusp collar into the cusp-free elliptic interior. -/
public def cuspToEllipticInteriorMap (_D : A.EllipticTwoDiscCoverData) :
    TopCat.of (A.openEmbeddingStarData.collarSource 0) ⟶
      TopCat.of A.ellipticInterior :=
  TopCat.ofHom ((IntegralMayerVietoris.interToLeft
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4))
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3)).comp
    ⟨A.cuspCollarToSectionSevenFinalOverlapHomeomorph,
      A.cuspCollarToSectionSevenFinalOverlapHomeomorph.continuous⟩)

/-- The pullback of the order-three side to the actual cusp collar. -/
public def cuspOrderThreeOpen : Opens (TopCat.of (A.openEmbeddingStarData.collarSource 0)) :=
  (Opens.map D.cuspToEllipticInteriorMap).obj (orderThreeOpen D)

/-- The pullback of the order-four side to the actual cusp collar. -/
public def cuspOrderFourOpen : Opens (TopCat.of (A.openEmbeddingStarData.collarSource 0)) :=
  (Opens.map D.cuspToEllipticInteriorMap).obj (orderFourOpen D)

/-- The pulled-back sides cover the cusp collar. -/
public theorem cuspOpenCover : D.cuspOrderThreeOpen ⊔ D.cuspOrderFourOpen = ⊤ := by
  unfold cuspOrderThreeOpen cuspOrderFourOpen
  change (Opens.map D.cuspToEllipticInteriorMap).obj
    (orderThreeOpen D ⊔ orderFourOpen D) = ⊤
  rw [ellipticOpenCover D]
  rfl

/-- The canonical homology comparison for the pulled-back cusp cover. -/
public noncomputable def cuspOpenCoverHomologyComparison :
    BinaryOpenCover.OpenCoverHomologyComparison
      D.cuspOrderThreeOpen D.cuspOrderFourOpen :=
  BinaryOpenCover.openCoverHomologyComparisonOfCover D.cuspOpenCover

/-- The canonical homology comparison for the elliptic two-disc cover. -/
public noncomputable def ellipticOpenCoverHomologyComparison :
    BinaryOpenCover.OpenCoverHomologyComparison (orderThreeOpen D) (orderFourOpen D) :=
  BinaryOpenCover.openCoverHomologyComparisonOfCover (ellipticOpenCover D)


/-- The canonical generated-cover comparisons satisfy the required pullback naturality. -/
public theorem cuspOpenCoverPullbackNaturality :
    (D.cuspOpenCoverHomologyComparison.PullbackNaturality D.cuspToEllipticInteriorMap
         (orderThreeOpen D) (orderFourOpen D) D.ellipticOpenCoverHomologyComparison) :=
  BinaryOpenCover.openCoverHomologyComparisonOfCover_pullbackNaturality
    D.cuspToEllipticInteriorMap (orderThreeOpen D) (orderFourOpen D)
      D.cuspOpenCover (ellipticOpenCover D)

/-- Compute the pulled-back cusp-cover boundary and transport it to the actual elliptic-side
intersection. -/
public noncomputable def cuspPulledBackBoundary
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    IntegralSingularHomology 1
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior) :=
  ConcreteCategory.hom
    (D.cuspOpenCoverHomologyComparison.boundary 1 ≫
      BinaryOpenCover.openIntersectionPullbackHomologyMap D.cuspToEllipticInteriorMap
        (orderThreeOpen D) (orderFourOpen D) 1 ≫
      (BinaryOpenCover.opensIntersectionHomologyIso
        (orderThreeOpen D) (orderFourOpen D) 1).inv) x

/-- The actual cusp inclusion on homology agrees with the union-subtype map used by the elliptic
Mayer--Vietoris presentation. -/
public theorem cuspToEllipticInteriorMap_homology
    (k : ℕ) (x : IntegralSingularHomology k (A.openEmbeddingStarData.collarSource 0)) :
    integralSingularHomologyMap k D.cuspToEllipticInteriorMap.hom x =
      integralSingularHomologyEquiv k
        (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.ellipticInterior)
          (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
        (cuspToEllipticUnionHomology D k x) := by
  simp [cuspToEllipticInteriorMap, cuspToEllipticUnionHomology,
    integralSingularHomologyMap_comp]

/-- The elliptic canonical boundary of an included cusp class is computed entirely in the
pulled-back cusp cover. -/
public theorem canonicalBoundary_cuspToEllipticUnionHomology
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    canonicalBoundary D 1 (cuspToEllipticUnionHomology D 2 x) =
      D.cuspPulledBackBoundary x := by
  let hNat := D.cuspOpenCoverPullbackNaturality
  have hn := BinaryOpenCover.OpenCoverHomologyComparison.boundary_pullback_naturality
    D.cuspToEllipticInteriorMap (orderThreeOpen D) (orderFourOpen D)
      D.cuspOpenCoverHomologyComparison D.ellipticOpenCoverHomologyComparison hNat 1
  unfold cuspPulledBackBoundary cuspOpenCoverHomologyComparison
    cuspOrderThreeOpen cuspOrderFourOpen at hn ⊢
  have hn' := congrArg (fun q ↦ q ≫
      (BinaryOpenCover.opensIntersectionHomologyIso
        (orderThreeOpen D) (orderFourOpen D) 1).inv) hn
  unfold canonicalBoundary canonicalMayerVietorisData
  change ConcreteCategory.hom
      ((BinaryOpenCover.opensUnionHomologyIso (orderThreeOpen D) (orderFourOpen D)
          (ellipticOpenCover D) 2).hom ≫
        D.ellipticOpenCoverHomologyComparison.boundary 1 ≫
        (BinaryOpenCover.opensIntersectionHomologyIso
          (orderThreeOpen D) (orderFourOpen D) 1).inv)
        (cuspToEllipticUnionHomology D 2 x) = _
  have hUnion : ConcreteCategory.hom
      (BinaryOpenCover.opensUnionHomologyIso (orderThreeOpen D) (orderFourOpen D)
        (ellipticOpenCover D) 2).hom
        (cuspToEllipticUnionHomology D 2 x) =
      integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x := by
    change integralSingularHomologyEquiv 2
        (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.ellipticInterior)
          (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
        (cuspToEllipticUnionHomology D 2 x) = _
    exact (D.cuspToEllipticInteriorMap_homology 2 x).symm
  calc
    _ = ConcreteCategory.hom
        (D.ellipticOpenCoverHomologyComparison.boundary 1 ≫
          (BinaryOpenCover.opensIntersectionHomologyIso
            (orderThreeOpen D) (orderFourOpen D) 1).inv)
          (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x) := by
      rw [← hUnion]
      rfl
    _ = ConcreteCategory.hom
        (((BinaryOpenCover.integralHomologyFunctor (1 + 1)).map
            D.cuspToEllipticInteriorMap ≫
          D.ellipticOpenCoverHomologyComparison.boundary 1) ≫
          (BinaryOpenCover.opensIntersectionHomologyIso
            (orderThreeOpen D) (orderFourOpen D) 1).inv) x := by
      rfl
    _ = _ := DFunLike.congr_fun (congrArg ConcreteCategory.hom hn'.symm) x



end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.AnalyticData
