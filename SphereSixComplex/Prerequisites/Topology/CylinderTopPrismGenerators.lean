module

public import SphereSixComplex.Prerequisites.Topology.CylinderTopFaceExcision
public import SphereSixComplex.Prerequisites.Topology.CharacteristicCylinderHomeomorph

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SphereSixComplex

public def cylinderTopPrismClass {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :=
  cyclesMap (cylinderTopFaceRelativeChains A) (n + 1) ≫
    contractingPrismClass (cylinderRelativeTriple A) (cylinderRelativeContraction A) n

public theorem contractingPrismClass_comp_cyclesMap_surjective
    (S : ShortComplex (ChainComplex AddCommGrpCat ℕ)) (hS : S.ShortExact)
    (H : Homotopy (𝟙 S.X₂) 0) (K : ChainComplex AddCommGrpCat ℕ)
    (f : K ⟶ S.X₁) [QuasiIso f] (n : ℕ) :
    Function.Surjective (cyclesMap f (n + 1) ≫ contractingPrismClass S H n) := by
  let := contractingPrism_boundary_isIso S hS H n
  have h : cyclesMap f (n + 1) ≫ contractingPrismClass S H n =
      K.homologyπ (n + 1) ≫ homologyMap f (n + 1) ≫
        inv (hS.δ (n + 2) (n + 1) rfl) := by
    erw [contractingPrismClass_eq_inverse_boundary S hS H n,
      ← Category.assoc, ← homologyπ_naturality, Category.assoc]
  rw [h]
  exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance

public theorem cylinderTopPrismClass_surjective {X : Type} [TopologicalSpace X]
    (A : Set X) (n : ℕ) : Function.Surjective (cylinderTopPrismClass A n) := by
  let f : cwRelativeIntegralSingularChainComplex (cylinderBaseInclusion A) ⟶
      (cylinderRelativeTriple A).X₁ := cylinderTopFaceRelativeChains A
  let : QuasiIso f := cylinderTopFaceRelativeChains_quasiIso A
  exact contractingPrismClass_comp_cyclesMap_surjective (cylinderRelativeTriple A)
    (cylinderRelativeTriple_shortExact A) (cylinderRelativeContraction A) _
      f n

public def cwBallBoundarySet (n : ℕ) : Set (CWCharacteristicClosedBall n) :=
  {b | b.1 ∈ Metric.sphere 0 1}

public def cwCharacteristicCylinderPair (n : ℕ) :
    CWTopologicalPairMap (cylinderBoundaryInclusion (cwBallBoundarySet n))
      (cwCharacteristicBoundaryInclusion (n + 1)) where
  left := TopCat.ofHom ⟨fun p ↦ ⟨(cwCharacteristicCylinderHomeomorph n p.1).1,
    (cwCharacteristicCylinderHomeomorph_boundary n p.1.1 p.1.2).mpr p.2⟩,
    (continuous_subtype_val.comp
      ((cwCharacteristicCylinderHomeomorph n).continuous.comp continuous_subtype_val)).subtype_mk _⟩
  right := TopCat.ofHom ⟨cwCharacteristicCylinderHomeomorph n, (cwCharacteristicCylinderHomeomorph n).continuous⟩
  comm := rfl

public def cwCharacteristicCylinderInversePair (n : ℕ) :
    CWTopologicalPairMap (cwCharacteristicBoundaryInclusion (n + 1))
      (cylinderBoundaryInclusion (cwBallBoundarySet n)) where
  left := TopCat.ofHom ⟨fun p ↦
    ⟨(cwCharacteristicCylinderHomeomorph n).symm (cwCharacteristicBoundaryInclusion (n + 1) p), by
      apply (cwCharacteristicCylinderHomeomorph_boundary n _ _).mp
      change ((cwCharacteristicCylinderHomeomorph n)
        ((cwCharacteristicCylinderHomeomorph n).symm _)).1 ∈ Metric.sphere 0 1
      rw [Homeomorph.apply_symm_apply]
      exact p.2⟩,
    ((cwCharacteristicCylinderHomeomorph n).symm.continuous.comp
      (cwCharacteristicBoundaryInclusion (n + 1)).hom.continuous).subtype_mk _⟩
  right := TopCat.ofHom ⟨(cwCharacteristicCylinderHomeomorph n).symm, (cwCharacteristicCylinderHomeomorph n).symm.continuous⟩
  comm := rfl

public def cwCharacteristicCylinderRelativeIso (n : ℕ) :
    cwRelativeIntegralSingularChainComplex (cylinderBoundaryInclusion (cwBallBoundarySet n)) ≅
      cwRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion (n + 1)) where
  hom := cwRelativeIntegralSingularChainMapOfPair (cwCharacteristicCylinderPair n)
  inv := cwRelativeIntegralSingularChainMapOfPair (cwCharacteristicCylinderInversePair n)
  hom_inv_id := by
    apply Cofork.IsColimit.hom_ext (cokernelIsCokernel
      (cwIntegralSingularChainMapObj (cylinderBoundaryInclusion (cwBallBoundarySet n))))
    change cwRelativeIntegralSingularChainProjection _ ≫ (_ ≫ _) =
      cwRelativeIntegralSingularChainProjection _ ≫ 𝟙 _
    rw [← Category.assoc, cwRelativeIntegralSingularChainProjection_natural,
      Category.assoc, cwRelativeIntegralSingularChainProjection_natural, ← Category.assoc,
      ← cwIntegralSingularChainMapObj_comp]
    have h : (cwCharacteristicCylinderPair n).right ≫
        (cwCharacteristicCylinderInversePair n).right = 𝟙 _ := by
      ext p : 1
      exact (cwCharacteristicCylinderHomeomorph n).symm_apply_apply p
    rw [h, cwIntegralSingularChainMapObj_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply Cofork.IsColimit.hom_ext (cokernelIsCokernel
      (cwIntegralSingularChainMapObj (cwCharacteristicBoundaryInclusion (n + 1))))
    change cwRelativeIntegralSingularChainProjection _ ≫ (_ ≫ _) =
      cwRelativeIntegralSingularChainProjection _ ≫ 𝟙 _
    rw [← Category.assoc, cwRelativeIntegralSingularChainProjection_natural,
      Category.assoc, cwRelativeIntegralSingularChainProjection_natural, ← Category.assoc,
      ← cwIntegralSingularChainMapObj_comp]
    have h : (cwCharacteristicCylinderInversePair n).right ≫
        (cwCharacteristicCylinderPair n).right = 𝟙 _ := by
      ext p : 1
      exact (cwCharacteristicCylinderHomeomorph n).apply_symm_apply p
    rw [h, cwIntegralSingularChainMapObj_id, Category.id_comp, Category.comp_id]

public def cwCharacteristicBallPrismClass (n : ℕ) :=
  cylinderTopPrismClass (cwBallBoundarySet (n + 1)) n ≫
    homologyMap (cwCharacteristicCylinderRelativeIso (n + 1)).hom (n + 2)

public theorem cwCharacteristicBallPrismClass_surjective (n : ℕ) :
    Function.Surjective (cwCharacteristicBallPrismClass n) := by
  let e := cwCharacteristicCylinderRelativeIso (n + 1)
  have h : Function.Surjective (homologyMap e.hom (n + 2)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  exact h.comp (cylinderTopPrismClass_surjective (cwBallBoundarySet (n + 1)) n)

end SphereSixComplex
