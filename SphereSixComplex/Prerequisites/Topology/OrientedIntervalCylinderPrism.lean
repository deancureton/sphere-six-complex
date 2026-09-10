module

public import SphereSixComplex.Prerequisites.Topology.CharacteristicCylinderSuspensionOrientation
public import SphereSixComplex.Prerequisites.Topology.CylinderSweepPrismComparison

@[expose] public section
noncomputable section
open CategoryTheory HomologicalComplex
namespace SphereSixComplex

public def orientedIntervalCylinderPrism :
    (cwRelativeIntegralSingularChainComplex
      (cylinderBoundaryInclusion (cwBallBoundarySet 1))).homology 2 :=
  (cylinderTopPrismHomologyIso (cwBallBoundarySet 1) 0).hom
    (homologyMap (cwNestedBoundaryRelativeIso 1).hom 1 (cwOrientedIntervalClass.hom 1))

public theorem orientedIntervalCylinderPrism_eq_orientation_or_neg_orientation
    (T : CellularHomology.IntegralComparison) :
    orientedIntervalCylinderPrism =
        homologyMap (cwCharacteristicCylinderRelativeIso 1).inv 2 ((T.diskOrientation 2).symm 1) ∨
      orientedIntervalCylinderPrism =
        -homologyMap (cwCharacteristicCylinderRelativeIso 1).inv 2 ((T.diskOrientation 2).symm 1) := by
  let e : ℤ ≃+ ℤ := (normalizedIntervalDiskOrientation T).symm.trans
    ((cwCharacteristicSuspensionIso 0).addCommGroupIsoToAddEquiv.trans (T.diskOrientation 2))
  have h := intAddEquiv_apply_one_eq_one_or_neg_one e
  change (T.diskOrientation 2)
      ((cwCharacteristicSuspensionIso 0).hom ((normalizedIntervalDiskOrientation T).symm 1)) = 1 ∨
    (T.diskOrientation 2)
      ((cwCharacteristicSuspensionIso 0).hom ((normalizedIntervalDiskOrientation T).symm 1)) = -1 at h
  rw [normalizedIntervalDiskOrientation_symm_one] at h
  have he : (cwCharacteristicSuspensionIso 0).hom (cwOrientedIntervalClass.hom 1) =
      homologyMap (cwCharacteristicCylinderRelativeIso 1).hom 2 orientedIntervalCylinderPrism := rfl
  rw [he] at h
  have hi : Function.Injective (homologyMap (cwCharacteristicCylinderRelativeIso 1).hom 2) :=
    ((homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) 2).mapIso
      (cwCharacteristicCylinderRelativeIso 1)).addCommGroupIsoToAddEquiv.injective
  have hc : homologyMap (cwCharacteristicCylinderRelativeIso 1).hom 2
      (homologyMap (cwCharacteristicCylinderRelativeIso 1).inv 2 ((T.diskOrientation 2).symm 1)) =
      (T.diskOrientation 2).symm 1 := by
    change (homologyMap (cwCharacteristicCylinderRelativeIso 1).inv 2 ≫
      homologyMap (cwCharacteristicCylinderRelativeIso 1).hom 2) _ = _
    rw [← homologyMap_comp, Iso.inv_hom_id, homologyMap_id]
    rfl
  rcases h with h | h
  · left
    apply hi
    rw [hc]
    exact (T.diskOrientation 2).injective (by simpa using h)
  · right
    apply hi
    rw [map_neg, hc]
    exact (T.diskOrientation 2).injective (by simpa using h)

public theorem cylinderTopPrismHomologyIso_comp_eq_closedPrism
    {X : Type} [TopologicalSpace X] (A : Set X)
    (L : ChainComplex AddCommGrpCat ℕ)
    (g : (cylinderRelativeTriple A).X₃ ⟶ L)
    {r : cwRelativeIntegralSingularChainComplex (cylinderBaseInclusion A) ⟶ L}
    (R : Homotopy r r) (n : ℕ)
    (h : (cylinderTopFaceRelativeChains A).f (n + 1) ≫
      (cylinderRelativeTriple A).f.f (n + 1) ≫
      (cylinderRelativeContraction A).hom (n + 1) (n + 2) ≫
      (cylinderRelativeTriple A).g.f (n + 2) ≫ g.f (n + 2) =
        R.hom (n + 1) (n + 2)) :
    (cylinderTopPrismHomologyIso A n).hom ≫ homologyMap g (n + 2) =
      closedPrismHomology R n := by
  apply (cancel_epi ((cwRelativeIntegralSingularChainComplex
    (cylinderBaseInclusion A)).homologyπ (n + 1))).mp
  rw [← Category.assoc, cylinderTopPrismHomologyIso_projection]
  exact mappedContractingPrismClass_eq_closedPrism (cylinderRelativeTriple A)
    (cylinderRelativeContraction A) _ L (cylinderTopFaceRelativeChains A) g R n h

end SphereSixComplex
