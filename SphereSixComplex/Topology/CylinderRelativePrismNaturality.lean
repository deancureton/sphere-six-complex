module

public import SphereSixComplex.Topology.ClosedCylinderRelativePrism

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
namespace SphereSixComplex

public theorem cylinderRelativePrism_to_relativeHomotopy
    {X A' X' B Y : TopCat} (A : Set X) {i : A' ⟶ X'} {j : B ⟶ Y}
    [Mono (cylinderBaseInclusion A)] [Mono i]
    (F : CWTopologicalPairMap (cylinderBoundaryInclusion A) j)
    (u : CWTopologicalPairMap (cylinderBaseInclusion A) i)
    (f : CWTopologicalPairMap i j)
    (H : TopCat.Homotopy f.left f.left) (K : TopCat.Homotopy f.right f.right)
    (h : i ▷ TopCat.I ≫ K.h = H.h ≫ j)
    (hu : u.right ▷ TopCat.I ≫ K.h =
      (cylinderReversedSweep F.right).h) (n : ℕ) :
    homologyMap (cwRelativeIntegralSingularChainMapOfPair u) (n + 1) ≫
      closedPrismHomology (cwRelativeSingularHomotopy H K h) n =
        closedPrismHomology (closedCylinderRelativePrism A F) n := by
  have hc (p q : ℕ) :
      (cwRelativeIntegralSingularChainMapOfPair u).f p ≫
        (cwRelativeSingularHomotopy H K h).hom p q =
          (closedCylinderRelativePrism A F).hom p q := by
    let : Epi (cwRelativeIntegralSingularChainProjection (cylinderBaseInclusion A)) := by
      change Epi (cokernel.π _)
      infer_instance
    apply (cancel_epi ((cwRelativeIntegralSingularChainProjection
      (cylinderBaseInclusion A)).f p)).mp
    have hn := congrArg (fun c ↦ c.f p) (cwRelativeIntegralSingularChainProjection_natural u)
    change (cwRelativeIntegralSingularChainProjection (cylinderBaseInclusion A)).f p ≫
      (cwRelativeIntegralSingularChainMapOfPair u).f p =
        (cwIntegralSingularChainMapObj u.right).f p ≫
          (cwRelativeIntegralSingularChainProjection i).f p at hn
    rw [← Category.assoc, hn, Category.assoc,
      cwRelativeSingularHomotopy_projection H K h,
      closedCylinderRelativePrism_projection]
    have ht := topologicalPrism_naturality (cylinderReversedSweep F.right) K
      u.right (𝟙 Y) (by simpa using hu) (AddCommGrpCat.of ℤ) p q
    change (cwIntegralSingularChainMapObj u.right).f p ≫ _ =
      _ ≫ (cwIntegralSingularChainMapObj (𝟙 Y)).f q at ht
    rw [cwIntegralSingularChainMapObj_id, HomologicalComplex.id_f, Category.comp_id] at ht
    rw [← Category.assoc, ht]
  have hn := closedPrismHomology_naturality (closedCylinderRelativePrism A F) n
    (cwRelativeSingularHomotopy H K h)
    (cwRelativeIntegralSingularChainMapOfPair u) (𝟙 _) (by
      intro p q
      simpa only [HomologicalComplex.id_f, Category.comp_id] using hc p q)
  simpa only [homologyMap_id, Category.comp_id] using hn

end SphereSixComplex
