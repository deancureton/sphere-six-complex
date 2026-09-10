module

public import SphereSixComplex.Prerequisites.Topology.RelativeSingularHomotopy
public import SphereSixComplex.Prerequisites.Topology.CylinderRelativeTriple

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SphereSixComplex

public def cylinderLowerSideInclusion {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of (cylinderLowerSide A) ⟶ TopCat.of (unitInterval × X) :=
  cylinderLowerSideToBoundary A ≫ cylinderBoundaryInclusion A

public instance cylinderLowerSideInclusion_mono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (cylinderLowerSideInclusion A) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

public def cylinderIdentityPair {X : Type} [TopologicalSpace X] (A : Set X) :
    CWTopologicalPairMap (cylinderLowerSideInclusion A) (cylinderLowerSideInclusion A) where
  left := 𝟙 _
  right := 𝟙 _
  comm := by simp

public def cylinderBottomPair {X : Type} [TopologicalSpace X] (A : Set X) :
    CWTopologicalPairMap (cylinderLowerSideInclusion A) (cylinderLowerSideInclusion A) where
  left := TopCat.ofHom (cylinderLowerSideBottomMap A)
  right := TopCat.ofHom (cylinderBottomMap X)
  comm := rfl

public theorem cylinderIdentityPair_chainMap {X : Type} [TopologicalSpace X] (A : Set X) :
    cwRelativeIntegralSingularChainMapOfPair (cylinderIdentityPair A) = 𝟙 _ :=
  cwRelativeIntegralSingularChainMapOfPair_id _

public def cylinderBottomToLowerSide {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of (unitInterval × X) ⟶ TopCat.of (cylinderLowerSide A) :=
  TopCat.ofHom ⟨fun p ↦ ⟨(0, p.2), Or.inl rfl⟩,
    (continuous_const.prodMk continuous_snd).subtype_mk _⟩

public theorem cylinderBottomPair_chainMap {X : Type} [TopologicalSpace X] (A : Set X) :
    cwRelativeIntegralSingularChainMapOfPair (cylinderBottomPair A) = 0 := by
  apply Cofork.IsColimit.hom_ext
    (cokernelIsCokernel (cwIntegralSingularChainMapObj (cylinderLowerSideInclusion A)))
  change cwRelativeIntegralSingularChainProjection _ ≫ _ =
    cwRelativeIntegralSingularChainProjection _ ≫ _
  rw [cwRelativeIntegralSingularChainProjection_natural, comp_zero]
  have hb : (cylinderBottomPair A).right =
    cylinderBottomToLowerSide A ≫ cylinderLowerSideInclusion A := rfl
  have hz : cwIntegralSingularChainMapObj (cylinderLowerSideInclusion A) ≫
      cwRelativeIntegralSingularChainProjection (cylinderLowerSideInclusion A) = 0 :=
    (cwRelativeIntegralSingularShortComplex (cylinderLowerSideInclusion A)).zero
  rw [hb, cwIntegralSingularChainMapObj_comp, Category.assoc, hz, comp_zero]

public def cylinderRelativeContraction {X : Type} [TopologicalSpace X] (A : Set X) :
    Homotopy (𝟙 (cylinderRelativeTriple A).X₂) 0 := by
  have H := cwRelativeSingularHomotopy
    (f := cylinderIdentityPair A) (g := cylinderBottomPair A)
    (cylinderLowerSideHomotopy A) (cylinderVerticalHomotopy X) (by ext p <;> rfl)
  exact (Homotopy.ofEq (cylinderIdentityPair_chainMap A).symm).trans
    (H.trans (Homotopy.ofEq (cylinderBottomPair_chainMap A)))

public theorem cylinderRelativeContraction_projection {X : Type} [TopologicalSpace X]
    (A : Set X) (p q : ℕ) :
    (cwRelativeIntegralSingularChainProjection (cylinderLowerSideInclusion A)).f p ≫
      (cylinderRelativeContraction A).hom p q =
    (TopCat.Homotopy.singularChainComplexFunctorObjMap
      (f := 𝟙 (TopCat.of (unitInterval × X)))
      (g := TopCat.ofHom (cylinderBottomMap X)) (cylinderVerticalHomotopy X)
        (AddCommGrpCat.of ℤ)).hom p q ≫
      (cwRelativeIntegralSingularChainProjection (cylinderLowerSideInclusion A)).f q := by
  let H := cwRelativeSingularHomotopy
    (f := cylinderIdentityPair A) (g := cylinderBottomPair A)
    (cylinderLowerSideHomotopy A) (cylinderVerticalHomotopy X) (by ext x <;> rfl)
  change (cwRelativeIntegralSingularChainProjection (cylinderLowerSideInclusion A)).f p ≫
    (0 + (H.hom p q + 0)) = _
  rw [zero_add, add_zero]
  exact cwRelativeSingularHomotopy_projection
    (f := cylinderIdentityPair A) (g := cylinderBottomPair A)
    (cylinderLowerSideHomotopy A) (cylinderVerticalHomotopy X) (by ext x <;> rfl) p q

public theorem cylinderRelativePrism_surjective {X : Type} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Function.Surjective (contractingPrismClass (cylinderRelativeTriple A)
      (cylinderRelativeContraction A) n) :=
  contractingPrismClass_surjective (cylinderRelativeTriple A)
    (cylinderRelativeTriple_shortExact A) (cylinderRelativeContraction A) n

end SphereSixComplex
