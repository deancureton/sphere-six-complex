module

public import SphereSixComplex.Topology.OrientedIntervalCylinderPrism

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
namespace SphereSixComplex

variable {X B Y : TopCat} (A : Set X) {j : B ⟶ Y}
  (F : CWTopologicalPairMap (cylinderBoundaryInclusion A) j)

public def cylinderSlicePair (t : unitInterval) :
    CWTopologicalPairMap (cylinderBaseInclusion A) j where
  left := TopCat.ofHom ⟨fun a ↦ F.left ⟨(t, a.1), Or.inr (Or.inr a.2)⟩,
    F.left.hom.continuous.comp ((continuous_const.prodMk continuous_subtype_val).subtype_mk _)⟩
  right := TopCat.ofHom ⟨fun x ↦ F.right (t, x),
    F.right.hom.continuous.comp (continuous_const.prodMk continuous_id)⟩
  comm := by
    ext a
    exact ConcreteCategory.congr_hom F.comm ⟨(t, a.1), Or.inr (Or.inr a.2)⟩

public theorem cylinderSlicePair_chainMap_zero (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    cwRelativeIntegralSingularChainMapOfPair (cylinderSlicePair A F t) = 0 := by
  let u : X ⟶ B := TopCat.ofHom ⟨fun x ↦ F.left ⟨(t, x), by
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)⟩,
    by fun_prop⟩
  have hu : (cylinderSlicePair A F t).right = u ≫ j := by
    ext x
    exact ConcreteCategory.congr_hom F.comm ⟨(t, x), by
      rcases ht with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)⟩
  apply Cofork.IsColimit.hom_ext (cokernelIsCokernel (cwIntegralSingularChainMapObj
    (cylinderBaseInclusion A)))
  change cwRelativeIntegralSingularChainProjection _ ≫ _ =
    cwRelativeIntegralSingularChainProjection _ ≫ _
  have hz : cwIntegralSingularChainMapObj j ≫ cwRelativeIntegralSingularChainProjection j = 0 :=
    (cwRelativeIntegralSingularShortComplex j).zero
  rw [cwRelativeIntegralSingularChainProjection_natural, comp_zero, hu,
    cwIntegralSingularChainMapObj_comp, Category.assoc,
    hz, comp_zero]

public def cylinderBoundaryReverseSweep :
    TopCat.Homotopy (cylinderSlicePair A F 1).left (cylinderSlicePair A F 0).left where
  toFun p := F.left ⟨(unitInterval.symm p.1, p.2.1), Or.inr (Or.inr p.2.2)⟩
  continuous_toFun := by fun_prop
  map_zero_left a := by simp [cylinderSlicePair]
  map_one_left a := by simp [cylinderSlicePair]

public def cylinderPairReverseSweep :
    TopCat.Homotopy (cylinderSlicePair A F 1).right (cylinderSlicePair A F 0).right :=
  cylinderReversedSweep F.right

public theorem cylinderPairReverseSweep_comm :
    cylinderBaseInclusion A ▷ TopCat.I ≫ (cylinderPairReverseSweep A F).h =
      (cylinderBoundaryReverseSweep A F).h ≫ j := by
  ext p
  have h := ConcreteCategory.congr_hom F.comm
    ⟨(unitInterval.symm (TopCat.I.homeomorph p.2), p.1.1), Or.inr (Or.inr p.1.2)⟩
  change F.right (cylinderVerticalScale (TopCat.I.homeomorph p.2) 1, p.1.1) =
    j (F.left ⟨(unitInterval.symm (TopCat.I.homeomorph p.2), p.1.1), Or.inr (Or.inr p.1.2)⟩)
  have he : cylinderVerticalScale (TopCat.I.homeomorph p.2) 1 =
      unitInterval.symm (TopCat.I.homeomorph p.2) := by
    apply Subtype.ext
    simp [cylinderVerticalScale, unitInterval.symm]
  rw [he]
  exact h

public def closedCylinderRelativePrism
    [Mono (cylinderBaseInclusion A)] :
    Homotopy (0 : CWRelativeIntegralSingularChainComplex (cylinderBaseInclusion A) ⟶
      CWRelativeIntegralSingularChainComplex j) 0 :=
  (Homotopy.ofEq (cylinderSlicePair_chainMap_zero A F 1 (Or.inr rfl)).symm).trans
    ((cwRelativeSingularHomotopy (cylinderBoundaryReverseSweep A F)
      (cylinderPairReverseSweep A F) (cylinderPairReverseSweep_comm A F)).trans
      (Homotopy.ofEq (cylinderSlicePair_chainMap_zero A F 0 (Or.inl rfl))))

public theorem closedCylinderRelativePrism_projection
    [Mono (cylinderBaseInclusion A)] (p q : ℕ) :
    (cwRelativeIntegralSingularChainProjection (cylinderBaseInclusion A)).f p ≫
      (closedCylinderRelativePrism A F).hom p q =
    ((cylinderReversedSweep F.right).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)).hom p q ≫
      (cwRelativeIntegralSingularChainProjection j).f q := by
  change (cwRelativeIntegralSingularChainProjection (cylinderBaseInclusion A)).f p ≫
    (0 + ((cwRelativeSingularHomotopy (cylinderBoundaryReverseSweep A F)
      (cylinderPairReverseSweep A F) (cylinderPairReverseSweep_comm A F)).hom p q + 0)) = _
  rw [zero_add, add_zero]
  exact cwRelativeSingularHomotopy_projection (cylinderBoundaryReverseSweep A F)
    (cylinderPairReverseSweep A F) (cylinderPairReverseSweep_comm A F) p q

public def cylinderLowerRestrictionPair :
    CWTopologicalPairMap (cylinderLowerSideInclusion A) j where
  left := cylinderLowerSideToBoundary A ≫ F.left
  right := F.right
  comm := by
    dsimp only [cylinderLowerSideInclusion]
    rw [Category.assoc, F.comm, Category.assoc]

public theorem cylinderTopPrismHomologyIso_map_pair
    [Mono (cylinderBaseInclusion A)] (n : ℕ) :
    (cylinderTopPrismHomologyIso A n).hom ≫
      homologyMap (cwRelativeIntegralSingularChainMapOfPair F) (n + 2) =
        closedPrismHomology (closedCylinderRelativePrism A F) n := by
  let S := cylinderRelativeTriple A
  let f := cylinderTopFaceRelativeChains A
  let g := cwRelativeIntegralSingularChainMapOfPair F
  have ht : f ≫ S.f = cwRelativeIntegralSingularChainMapOfPair
      (cylinderTopLowerPair A) := by
    dsimp only [f, S, cylinderRelativeTriple]
    rw [cwRelativeTripleShortComplex_f]
    exact (cwRelativeIntegralSingularChainMapOfPair_comp (cylinderTopFacePairMap A) _).symm
  have hg : S.g ≫ g = cwRelativeIntegralSingularChainMapOfPair
      (cylinderLowerRestrictionPair A F) := by
    dsimp only [S, cylinderRelativeTriple, g]
    rw [cwRelativeTripleShortComplex_g]
    exact (cwRelativeIntegralSingularChainMapOfPair_comp _ F).symm
  apply cylinderTopPrismHomologyIso_comp_eq_closedPrism
  have ht' := congrArg (fun k ↦ k.f (n + 1)) ht
  have hg' := congrArg (fun k ↦ k.f (n + 2)) hg
  change f.f (n + 1) ≫ S.f.f (n + 1) = _ at ht'
  change S.g.f (n + 2) ≫ g.f (n + 2) = _ at hg'
  change f.f (n + 1) ≫ S.f.f (n + 1) ≫ _ ≫ S.g.f (n + 2) ≫ g.f (n + 2) = _
  erw [← Category.assoc, ← Category.assoc, ← Category.assoc, ht', Category.assoc,
    Category.assoc, hg']
  apply cylinderRelativeContraction_sweep_relative
  exact closedCylinderRelativePrism_projection A F (n + 1) (n + 2)

public theorem closedCylinderRelativePrism_naturality
    [Mono (cylinderBaseInclusion A)]
    {X' B' Y' : TopCat} (A' : Set X') {j' : B' ⟶ Y'}
    [Mono (cylinderBaseInclusion A')]
    (F' : CWTopologicalPairMap (cylinderBoundaryInclusion A') j')
    (u : CWTopologicalPairMap (cylinderBaseInclusion A) (cylinderBaseInclusion A'))
    (v : CWTopologicalPairMap j j')
    (h : ∀ (t : unitInterval) (x : X), F'.right (t, u.right x) = v.right (F.right (t, x)))
    (n : ℕ) :
    homologyMap (cwRelativeIntegralSingularChainMapOfPair u) (n + 1) ≫
        closedPrismHomology (closedCylinderRelativePrism A' F') n =
      closedPrismHomology (closedCylinderRelativePrism A F) n ≫
        homologyMap (cwRelativeIntegralSingularChainMapOfPair v) (n + 2) := by
  apply closedPrismHomology_naturality
  intro p q
  let : Epi (cwRelativeIntegralSingularChainProjection (cylinderBaseInclusion A)) := by
    change Epi (cokernel.π _)
    infer_instance
  apply (cancel_epi ((cwRelativeIntegralSingularChainProjection (cylinderBaseInclusion A)).f p)).mp
  have hu := congrArg (fun f ↦ f.f p) (cwRelativeIntegralSingularChainProjection_natural u)
  have hv := congrArg (fun f ↦ f.f q) (cwRelativeIntegralSingularChainProjection_natural v)
  change (cwRelativeIntegralSingularChainProjection (cylinderBaseInclusion A)).f p ≫
    (cwRelativeIntegralSingularChainMapOfPair u).f p =
      (cwIntegralSingularChainMapObj u.right).f p ≫
      (cwRelativeIntegralSingularChainProjection (cylinderBaseInclusion A')).f p at hu
  change (cwRelativeIntegralSingularChainProjection j).f q ≫
    (cwRelativeIntegralSingularChainMapOfPair v).f q =
      (cwIntegralSingularChainMapObj v.right).f q ≫
      (cwRelativeIntegralSingularChainProjection j').f q at hv
  have ht := topologicalPrism_naturality (cylinderReversedSweep F.right)
    (cylinderReversedSweep F'.right) u.right v.right (by
      ext z
      exact h (cylinderVerticalScale (TopCat.I.homeomorph z.2) 1) z.1)
    (AddCommGrpCat.of ℤ) p q
  change (cwIntegralSingularChainMapObj u.right).f p ≫ _ =
    _ ≫ (cwIntegralSingularChainMapObj v.right).f q at ht
  rw [← Category.assoc, hu, Category.assoc, closedCylinderRelativePrism_projection,
    ← Category.assoc, ht, Category.assoc, ← hv]
  rw [← Category.assoc, ← closedCylinderRelativePrism_projection, Category.assoc]

end SphereSixComplex
