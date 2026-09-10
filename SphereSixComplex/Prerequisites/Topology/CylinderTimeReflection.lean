module

public import SphereSixComplex.Prerequisites.Topology.OrientedIntervalCylinderPrism

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SphereSixComplex

public def cylinderTimeReflectionPair {X : Type} [TopologicalSpace X] (A : Set X) :
    CWTopologicalPairMap (cylinderBoundaryInclusion A) (cylinderBoundaryInclusion A) where
  left := TopCat.ofHom ⟨fun p ↦ ⟨(unitInterval.symm p.1.1, p.1.2), by
    rcases p.2 with h | h | h
    · exact Or.inr (Or.inl (by rw [h]; simp))
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr (Or.inr h)⟩, by fun_prop⟩
  right := TopCat.ofHom ⟨fun p ↦ (unitInterval.symm p.1, p.2), by fun_prop⟩
  comm := rfl

public theorem cylinderTimeReflectionPair_chainMap_involutive
    {X : Type} [TopologicalSpace X] (A : Set X) :
    cwRelativeIntegralSingularChainMapOfPair (cylinderTimeReflectionPair A) ≫
      cwRelativeIntegralSingularChainMapOfPair (cylinderTimeReflectionPair A) = 𝟙 _ := by
  apply Cofork.IsColimit.hom_ext (cokernelIsCokernel
    (cwIntegralSingularChainMapObj (cylinderBoundaryInclusion A)))
  change cwRelativeIntegralSingularChainProjection _ ≫ (_ ≫ _) =
    cwRelativeIntegralSingularChainProjection _ ≫ 𝟙 _
  rw [← Category.assoc, cwRelativeIntegralSingularChainProjection_natural,
    Category.assoc, cwRelativeIntegralSingularChainProjection_natural, ← Category.assoc,
    ← cwIntegralSingularChainMapObj_comp]
  have h : (cylinderTimeReflectionPair A).right ≫
      (cylinderTimeReflectionPair A).right = 𝟙 _ := by
    ext p : 1
    exact Prod.ext (unitInterval.symm_symm p.1) rfl
  rw [h, cwIntegralSingularChainMapObj_id, Category.id_comp, Category.comp_id]

public def cylinderTimeReflectionRelativeIso {X : Type} [TopologicalSpace X] (A : Set X) :
    CWRelativeIntegralSingularChainComplex (cylinderBoundaryInclusion A) ≅
      CWRelativeIntegralSingularChainComplex (cylinderBoundaryInclusion A) where
  hom := cwRelativeIntegralSingularChainMapOfPair (cylinderTimeReflectionPair A)
  inv := cwRelativeIntegralSingularChainMapOfPair (cylinderTimeReflectionPair A)
  hom_inv_id := cylinderTimeReflectionPair_chainMap_involutive A
  inv_hom_id := cylinderTimeReflectionPair_chainMap_involutive A

public theorem cylinderTimeReflection_orientation_or_neg_orientation
    (T : IntegralCWCellularHomologyFoundation) :
    let g := homologyMap (cwCharacteristicCylinderRelativeIso 1).inv 2
      ((T.diskOrientation 2).symm 1)
    homologyMap (cwRelativeIntegralSingularChainMapOfPair
      (cylinderTimeReflectionPair (cwBallBoundarySet 1))) 2 g = g ∨
    homologyMap (cwRelativeIntegralSingularChainMapOfPair
      (cylinderTimeReflectionPair (cwBallBoundarySet 1))) 2 g = -g := by
  let e := ((homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) 2).mapIso
    (cwCharacteristicCylinderRelativeIso 1)).addCommGroupIsoToAddEquiv.trans (T.diskOrientation 2)
  let r := ((homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) 2).mapIso
    (cylinderTimeReflectionRelativeIso (cwBallBoundarySet 1))).addCommGroupIsoToAddEquiv
  have h := intAddEquiv_apply_one_eq_one_or_neg_one (e.symm.trans (r.trans e))
  change e (r (e.symm 1)) = 1 ∨ e (r (e.symm 1)) = -1 at h
  change r (e.symm 1) = e.symm 1 ∨ r (e.symm 1) = -(e.symm 1)
  rcases h with h | h
  · left
    apply e.injective
    simpa using h
  · right
    apply e.injective
    simpa using h

public theorem cylinderTimeReflection_orientedIntervalPrism
    (T : IntegralCWCellularHomologyFoundation) :
    homologyMap (cwRelativeIntegralSingularChainMapOfPair
      (cylinderTimeReflectionPair (cwBallBoundarySet 1))) 2 orientedIntervalCylinderPrism =
        orientedIntervalCylinderPrism ∨
    homologyMap (cwRelativeIntegralSingularChainMapOfPair
      (cylinderTimeReflectionPair (cwBallBoundarySet 1))) 2 orientedIntervalCylinderPrism =
        -orientedIntervalCylinderPrism := by
  rcases orientedIntervalCylinderPrism_eq_orientation_or_neg_orientation T with h | h
  · rw [h]
    exact cylinderTimeReflection_orientation_or_neg_orientation T
  · rw [h, map_neg, neg_neg]
    rcases cylinderTimeReflection_orientation_or_neg_orientation T with g | g
    · exact Or.inl (congrArg Neg.neg g)
    · exact Or.inr (by rw [g, neg_neg])

end SphereSixComplex
