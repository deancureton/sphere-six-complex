module

public import SphereSixComplex.Prerequisites.Topology.MayerVietoris.IntegralSequence
import SphereSixComplex.Prerequisites.Topology.MayerVietoris.OrientedRefinement

/-! # Naturality of the Mayer–Vietoris boundary on set subtypes -/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped ContinuousMap
noncomputable section
namespace SphereSixComplex.BinaryOpenCover

/-- The canonical Mayer–Vietoris boundary is natural under maps of ordered open covers. -/
public theorem legacyBoundary_naturality {X Y : TopCat} (f : C(X, Y))
    {U V : Opens X} {U' V' : Opens Y}
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (hcover : U ⊔ V = ⊤) (hcover' : U' ⊔ V' = ⊤) (n : ℕ) :
    (integralSingularHomologyMap n ((f.restrictPreimage ((U' : Set Y) ∩ V')).comp
        (ContinuousMap.inclusion (hU.inter_inter hV)))).comp
      (((openCoverHomologyComparisonOfCover hcover).toIntegralMayerVietorisData
        hcover).legacyBoundary n) =
      (((openCoverHomologyComparisonOfCover hcover').toIntegralMayerVietorisData
        hcover').legacyBoundary n).comp
      (integralSingularHomologyMap (n + 1) ((f.restrictPreimage ((U' : Set Y) ∪ V')).comp
        (ContinuousMap.inclusion (hU.union_union hV)))) := by
  let F := TopCat.ofHom f
  have hp : (Opens.map F).obj U' ⊔ (Opens.map F).obj V' = ⊤ := by
    ext x
    change (f x ∈ U' ∨ f x ∈ V') ↔ True
    have hx : f x ∈ U' ⊔ V' := by rw [hcover']; trivial
    exact iff_true_intro hx
  have hU₀ : U ≤ (Opens.map F).obj U' := hU
  have hV₀ : V ≤ (Opens.map F).obj V' := hV
  have hn := OpenCoverHomologyComparison.boundary_refinement_pullback_naturality
    F U' V' hU₀ hV₀
    (openCoverHomologyComparisonOfCover hcover)
    (openCoverHomologyComparisonOfCover hp)
    (openCoverHomologyComparisonOfCover hcover')
    (openCoverHomologyComparisonOfCover_refinementNaturality hU₀ hV₀ hcover hp)
    (openCoverHomologyComparisonOfCover_pullbackNaturality F U' V' hp hcover') n
  have hi : (opensIntersectionHomologyIso U V n).inv ≫
      (integralHomologyFunctor n).map
        (TopCat.ofHom ((f.restrictPreimage ((U' : Set Y) ∩ V')).comp
        (ContinuousMap.inclusion (hU.inter_inter hV)))) =
      openIntersectionRefinementHomologyMap hU₀ hV₀ n ≫
        openIntersectionPullbackHomologyMap F U' V' n ≫
        (opensIntersectionHomologyIso U' V' n).inv := by
    simp only [opensIntersectionHomologyIso, Functor.mapIso_inv,
      openIntersectionRefinementHomologyMap, openIntersectionPullbackHomologyMap,
      ← Functor.map_comp]
    rfl
  have hu : (opensUnionHomologyIso U V hcover (n + 1)).hom ≫
      (integralHomologyFunctor (n + 1)).map F =
      (integralHomologyFunctor (n + 1)).map
        (TopCat.ofHom ((f.restrictPreimage ((U' : Set Y) ∪ V')).comp
        (ContinuousMap.inclusion (hU.union_union hV)))) ≫
        (opensUnionHomologyIso U' V' hcover' (n + 1)).hom := by
    simp only [opensUnionHomologyIso, Functor.mapIso_hom, ← Functor.map_comp]
    rfl
  apply AddMonoidHom.ext
  intro x
  change ConcreteCategory.hom
    ((opensUnionHomologyIso U V hcover (n + 1)).hom ≫
      (openCoverHomologyComparisonOfCover hcover).boundary n ≫
      (opensIntersectionHomologyIso U V n).inv ≫
      (integralHomologyFunctor n).map
        (TopCat.ofHom ((f.restrictPreimage ((U' : Set Y) ∩ V')).comp
        (ContinuousMap.inclusion (hU.inter_inter hV))))) x =
    ConcreteCategory.hom
    ((integralHomologyFunctor (n + 1)).map
        (TopCat.ofHom ((f.restrictPreimage ((U' : Set Y) ∪ V')).comp
        (ContinuousMap.inclusion (hU.union_union hV)))) ≫
      (opensUnionHomologyIso U' V' hcover' (n + 1)).hom ≫
      (openCoverHomologyComparisonOfCover hcover').boundary n ≫
      (opensIntersectionHomologyIso U' V' n).inv) x
  rw [hi]
  have hc := congrArg
    (fun q ↦ (opensUnionHomologyIso U V hcover (n + 1)).hom ≫ q ≫
      (opensIntersectionHomologyIso U' V' n).inv) hn
  simp only [Category.assoc] at hc
  rw [hc]
  rw [← Category.assoc, ← Category.assoc, hu]
  simp only [Category.assoc]

end SphereSixComplex.BinaryOpenCover
