module

public import SphereSixComplex.Topology.CylinderTopPrismGenerators
public import SphereSixComplex.Topology.CellularIntervalOrientation
public import SphereSixComplex.Topology.CellularSquareOrientation

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SphereSixComplex

public def contractingPrismHomologyIso
    (S : ShortComplex (ChainComplex AddCommGrpCat ℕ)) (hS : S.ShortExact)
    (H : Homotopy (𝟙 S.X₂) 0) (n : ℕ) :
    S.X₁.homology (n + 1) ≅ S.X₃.homology (n + 2) := by
  let := contractingPrism_boundary_isIso S hS H n
  exact (asIso (hS.δ (n + 2) (n + 1) rfl)).symm

public theorem contractingPrismHomologyIso_projection
    (S : ShortComplex (ChainComplex AddCommGrpCat ℕ)) (hS : S.ShortExact)
    (H : Homotopy (𝟙 S.X₂) 0) (n : ℕ) :
    S.X₁.homologyπ (n + 1) ≫ (contractingPrismHomologyIso S hS H n).hom =
      contractingPrismClass S H n :=
  (contractingPrismClass_eq_inverse_boundary S hS H n).symm

public def cylinderTopPrismHomologyIso {X : Type} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    (CWRelativeIntegralSingularChainComplex (cylinderBaseInclusion A)).homology (n + 1) ≅
      (cylinderRelativeTriple A).X₃.homology (n + 2) := by
  let f : CWRelativeIntegralSingularChainComplex (cylinderBaseInclusion A) ⟶
      (cylinderRelativeTriple A).X₁ := cylinderTopFaceRelativeChains A
  let : QuasiIso f := cylinderTopFaceRelativeChains_quasiIso A
  exact (asIso (homologyMap f (n + 1))) ≪≫
    contractingPrismHomologyIso (cylinderRelativeTriple A)
      (cylinderRelativeTriple_shortExact A) (cylinderRelativeContraction A) n

public theorem cylinderTopPrismHomologyIso_projection {X : Type} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    (CWRelativeIntegralSingularChainComplex (cylinderBaseInclusion A)).homologyπ (n + 1) ≫
      (cylinderTopPrismHomologyIso A n).hom = cylinderTopPrismClass A n := by
  dsimp only [cylinderTopPrismHomologyIso, Iso.trans_hom, asIso_hom, cylinderTopPrismClass]
  erw [← Category.assoc, homologyπ_naturality, Category.assoc,
    contractingPrismHomologyIso_projection]
  rfl

public def cwBoundaryNestedHomeomorph (n : ℕ) :
    CWCharacteristicBoundarySphere n ≃ₜ cwBallBoundarySet n where
  toFun b := ⟨⟨b.1, le_of_eq b.2⟩, b.2⟩
  invFun b := ⟨b.1.1, b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

public def cwNestedBoundaryRelativeIso (n : ℕ) :
    CWRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion n) ≅
      CWRelativeIntegralSingularChainComplex (cylinderBaseInclusion (cwBallBoundarySet n)) := by
  let F := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  exact cokernel.mapIso _ _ (F.mapIso (TopCat.isoOfHomeo (cwBoundaryNestedHomeomorph n)))
    (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id]
      change F.map _ = F.map _ ≫ F.map _
      rw [← Functor.map_comp]
      rfl)

public def cwCharacteristicSuspensionIso (n : ℕ) :
    (CWRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion (n + 1))).homology (n + 1) ≅
      (CWRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion (n + 2))).homology (n + 2) :=
  (homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) (n + 1)).mapIso
    (cwNestedBoundaryRelativeIso (n + 1)) ≪≫
      cylinderTopPrismHomologyIso (cwBallBoundarySet (n + 1)) n ≪≫
        (homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) (n + 2)).mapIso
          (cwCharacteristicCylinderRelativeIso (n + 1))

public theorem cwCharacteristicSuspensionIso_projection (n : ℕ) :
    (CWRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion (n + 1))).homologyπ
        (n + 1) ≫ (cwCharacteristicSuspensionIso n).hom =
      cyclesMap (cwNestedBoundaryRelativeIso (n + 1)).hom (n + 1) ≫
        cwCharacteristicBallPrismClass n := by
  dsimp only [cwCharacteristicSuspensionIso, Iso.trans_hom, Functor.mapIso_hom,
    cwCharacteristicBallPrismClass]
  change _ ≫ homologyMap _ _ ≫ (cylinderTopPrismHomologyIso _ _).hom ≫ homologyMap _ _ = _
  erw [← Category.assoc, ← Category.assoc,
    homologyπ_naturality (cwNestedBoundaryRelativeIso (n + 1)).hom (n + 1),
    Category.assoc, Category.assoc]
  have h := cylinderTopPrismHomologyIso_projection (cwBallBoundarySet (n + 1)) n
  have hh := congrArg
    (fun f => cyclesMap (cwNestedBoundaryRelativeIso (n + 1)).hom (n + 1) ≫ f ≫
      homologyMap (cwCharacteristicCylinderRelativeIso (n + 1)).hom (n + 2)) h
  change _ = _ at hh
  erw [Category.assoc] at hh
  exact hh

public theorem intAddEquiv_apply_one_eq_one_or_neg_one (e : ℤ ≃+ ℤ) :
    e 1 = 1 ∨ e 1 = -1 := by
  have he (z : ℤ) : e z = z * e 1 := by
    simpa only [smul_eq_mul, mul_one] using map_zsmul e z 1
  have h : e 1 * e.symm 1 = 1 := by
    rw [mul_comm, ← he, e.apply_symm_apply]
  exact Int.eq_one_or_neg_one_of_mul_eq_one h

public theorem cwIntervalSuspension_eq_square_or_neg_square
    (T : IntegralCWCellularHomologyFoundation) :
    (cwCharacteristicSuspensionIso 0).hom (cwOrientedIntervalClass.hom 1) =
        normalizedSquareDiskOrientation.symm 1 ∨
      (cwCharacteristicSuspensionIso 0).hom (cwOrientedIntervalClass.hom 1) =
        -(normalizedSquareDiskOrientation.symm 1) := by
  let e : ℤ ≃+ ℤ := (normalizedIntervalDiskOrientation T).symm.trans
    ((cwCharacteristicSuspensionIso 0).addCommGroupIsoToAddEquiv.trans normalizedSquareDiskOrientation)
  have h := intAddEquiv_apply_one_eq_one_or_neg_one e
  change normalizedSquareDiskOrientation
      ((cwCharacteristicSuspensionIso 0).hom ((normalizedIntervalDiskOrientation T).symm 1)) = 1 ∨
    normalizedSquareDiskOrientation
      ((cwCharacteristicSuspensionIso 0).hom ((normalizedIntervalDiskOrientation T).symm 1)) = -1 at h
  rw [normalizedIntervalDiskOrientation_symm_one] at h
  rcases h with h | h
  · exact Or.inl (normalizedSquareDiskOrientation.injective (by simpa using h))
  · exact Or.inr (normalizedSquareDiskOrientation.injective (by simpa using h))

end SphereSixComplex
