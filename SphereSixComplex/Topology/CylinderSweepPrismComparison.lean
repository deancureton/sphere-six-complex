module

public import SphereSixComplex.Topology.CylinderTopPrismGenerators
public import SphereSixComplex.Topology.ClosedPrismBoundaryVanishing

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
namespace SphereSixComplex

public def cylinderTopInclusion (X : TopCat) : X ⟶ TopCat.of (unitInterval × X) :=
  TopCat.ofHom ⟨fun x ↦ (1, x), continuous_const.prodMk continuous_id⟩

public def cylinderBottomInclusion (X : TopCat) : X ⟶ TopCat.of (unitInterval × X) :=
  TopCat.ofHom ⟨fun x ↦ (0, x), continuous_const.prodMk continuous_id⟩

public def cylinderTopVerticalHomotopy (X : TopCat) :
    TopCat.Homotopy (cylinderTopInclusion X) (cylinderBottomInclusion X) where
  toFun p := cylinderVerticalHomotopy X (p.1, (1, p.2))
  continuous_toFun := (cylinderVerticalHomotopy X).continuous.comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  map_zero_left _ := (cylinderVerticalHomotopy X).map_zero_left _
  map_one_left _ := (cylinderVerticalHomotopy X).map_one_left _

public def cylinderReversedSweep {X Y : TopCat} (F : TopCat.of (unitInterval × X) ⟶ Y) :
    TopCat.Homotopy (cylinderTopInclusion X ≫ F) (cylinderBottomInclusion X ≫ F) where
  toFun p := F (cylinderTopVerticalHomotopy X p)
  continuous_toFun := F.hom.continuous.comp (cylinderTopVerticalHomotopy X).continuous
  map_zero_left x := congrArg F ((cylinderTopVerticalHomotopy X).map_zero_left x)
  map_one_left x := congrArg F ((cylinderTopVerticalHomotopy X).map_one_left x)

public theorem cylinderTopVerticalPrism_naturality (X : TopCat) (p q : ℕ) :
    (cwIntegralSingularChainMapObj (cylinderTopInclusion X)).f p ≫
      (TopCat.Homotopy.singularChainComplexFunctorObjMap
        (f := 𝟙 (TopCat.of (unitInterval × X)))
        (g := TopCat.ofHom (cylinderBottomMap X)) (cylinderVerticalHomotopy X)
        (AddCommGrpCat.of ℤ)).hom p q =
    ((cylinderTopVerticalHomotopy X).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)).hom p q := by
  have h := topologicalPrism_naturality (cylinderTopVerticalHomotopy X)
    (cylinderVerticalHomotopy X) (cylinderTopInclusion X) (𝟙 _) (by ext z <;> rfl)
    (AddCommGrpCat.of ℤ) p q
  change _ = _ ≫ (cwIntegralSingularChainMapObj (𝟙 _)).f q at h
  erw [cwIntegralSingularChainMapObj_id, HomologicalComplex.id_f, Category.comp_id] at h
  exact h

public theorem cylinderReversedSweepPrism_naturality {X Y : TopCat}
    (F : TopCat.of (unitInterval × X) ⟶ Y) (p q : ℕ) :
    ((cylinderTopVerticalHomotopy X).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)).hom p q ≫ (cwIntegralSingularChainMapObj F).f q =
    ((cylinderReversedSweep F).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)).hom p q := by
  have h := topologicalPrism_naturality (cylinderTopVerticalHomotopy X)
    (cylinderReversedSweep F) (𝟙 _) F (by ext z; rfl)
    (AddCommGrpCat.of ℤ) p q
  change (cwIntegralSingularChainMapObj (𝟙 _)).f p ≫ _ = _ at h
  erw [cwIntegralSingularChainMapObj_id, HomologicalComplex.id_f, Category.id_comp] at h
  exact h.symm

public theorem cylinderRelativeContraction_sweep_projection
    {X Y B : TopCat} (A : Set X) (j : B ⟶ Y)
    (F : CWTopologicalPairMap (cylinderLowerSideInclusion A) j) (p q : ℕ) :
    (cwIntegralSingularChainMapObj (cylinderTopInclusion X)).f p ≫
      (cwRelativeIntegralSingularChainProjection (cylinderLowerSideInclusion A)).f p ≫
        (cylinderRelativeContraction A).hom p q ≫
          (cwRelativeIntegralSingularChainMapOfPair F).f q =
    ((cylinderReversedSweep F.right).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)).hom p q ≫
        (cwRelativeIntegralSingularChainProjection j).f q := by
  have hp := cylinderRelativeContraction_projection A p q
  have hn := congrArg (fun f ↦ f.f q) (cwRelativeIntegralSingularChainProjection_natural F)
  change (cwRelativeIntegralSingularChainProjection (cylinderLowerSideInclusion A)).f q ≫
    (cwRelativeIntegralSingularChainMapOfPair F).f q =
      (cwIntegralSingularChainMapObj F.right).f q ≫
        (cwRelativeIntegralSingularChainProjection j).f q at hn
  have ht := cylinderTopVerticalPrism_naturality X p q
  have hs := cylinderReversedSweepPrism_naturality F.right p q
  calc
    _ = (cwIntegralSingularChainMapObj (cylinderTopInclusion X)).f p ≫
        ((cwRelativeIntegralSingularChainProjection (cylinderLowerSideInclusion A)).f p ≫
          (cylinderRelativeContraction A).hom p q) ≫
            (cwRelativeIntegralSingularChainMapOfPair F).f q := by
      exact (Category.assoc _ _ _).symm
    _ = _ := by
      rw [hp]
      erw [Category.assoc, hn, ← Category.assoc, ← Category.assoc, ht,
        Category.assoc, ← Category.assoc _ _ ((cwRelativeIntegralSingularChainProjection j).f q), hs]

public def cylinderTopLowerPair {X : TopCat} (A : Set X) :
    CWTopologicalPairMap (cylinderBaseInclusion A) (cylinderLowerSideInclusion A) where
  left := cylinderTopEdgeMap A
  right := cylinderTopInclusion X
  comm := rfl

public theorem cylinderRelativeContraction_sweep_relative
    {X Y B : TopCat} (A : Set X) (j : B ⟶ Y)
    (F : CWTopologicalPairMap (cylinderLowerSideInclusion A) j) (p q : ℕ)
    (R : (CWRelativeIntegralSingularChainComplex (cylinderBaseInclusion A)).X p ⟶
      (CWRelativeIntegralSingularChainComplex j).X q)
    (hR : (cwRelativeIntegralSingularChainProjection (cylinderBaseInclusion A)).f p ≫ R =
      ((cylinderReversedSweep F.right).singularChainComplexFunctorObjMap
        (AddCommGrpCat.of ℤ)).hom p q ≫
          (cwRelativeIntegralSingularChainProjection j).f q) :
    (cwRelativeIntegralSingularChainMapOfPair (cylinderTopLowerPair A)).f p ≫
      (cylinderRelativeContraction A).hom p q ≫
        (cwRelativeIntegralSingularChainMapOfPair F).f q = R := by
  let : Epi (cwRelativeIntegralSingularChainProjection (cylinderBaseInclusion A)) := by
    change Epi (cokernel.π _)
    infer_instance
  apply (cancel_epi ((cwRelativeIntegralSingularChainProjection
    (cylinderBaseInclusion A)).f p)).mp
  have ht := congrArg (fun f ↦ f.f p)
    (cwRelativeIntegralSingularChainProjection_natural (cylinderTopLowerPair A))
  change (cwRelativeIntegralSingularChainProjection (cylinderBaseInclusion A)).f p ≫
      (cwRelativeIntegralSingularChainMapOfPair (cylinderTopLowerPair A)).f p =
    (cwIntegralSingularChainMapObj (cylinderTopInclusion X)).f p ≫
      (cwRelativeIntegralSingularChainProjection (cylinderLowerSideInclusion A)).f p at ht
  calc
    _ = ((cwRelativeIntegralSingularChainProjection (cylinderBaseInclusion A)).f p ≫
        (cwRelativeIntegralSingularChainMapOfPair (cylinderTopLowerPair A)).f p) ≫
          (cylinderRelativeContraction A).hom p q ≫
            (cwRelativeIntegralSingularChainMapOfPair F).f q := (Category.assoc _ _ _).symm
    _ = _ := by
      rw [ht]
      exact (cylinderRelativeContraction_sweep_projection A j F p q).trans hR.symm

public theorem mappedContractingPrismClass_eq_closedPrism
    (S : ShortComplex (ChainComplex AddCommGrpCat ℕ)) (H : Homotopy (𝟙 S.X₂) 0)
    (K L : ChainComplex AddCommGrpCat ℕ) (f : K ⟶ S.X₁) (g : S.X₃ ⟶ L)
    {r : K ⟶ L} (R : Homotopy r r) (n : ℕ)
    (h : f.f (n + 1) ≫ S.f.f (n + 1) ≫ H.hom (n + 1) (n + 2) ≫
        S.g.f (n + 2) ≫ g.f (n + 2) = R.hom (n + 1) (n + 2)) :
    cyclesMap f (n + 1) ≫ contractingPrismClass S H n ≫ homologyMap g (n + 2) =
      K.homologyπ (n + 1) ≫ closedPrismHomology R n := by
  rw [closedPrismHomology_projection]
  dsimp only [contractingPrismClass]
  erw [Category.assoc, homologyπ_naturality]
  have hc : cyclesMap f (n + 1) ≫
      S.X₃.liftCycles (contractingPrismLift S H n ≫ S.g.f (n + 2)) (n + 1) (by simp)
        (contractingPrismLift_quotient_cycle S H n) ≫ cyclesMap g (n + 2) =
      closedPrismCycles R n := by
    apply (cancel_mono (L.iCycles (n + 2))).mp
    simp only [Category.assoc, cyclesMap_i, liftCycles_i_assoc, closedPrismCycles_i]
    dsimp only [contractingPrismLift]
    simp only [Category.assoc]
    rw [cyclesMap_i_assoc]
    rw [h]
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ L.homologyπ (n + 2)) hc

public theorem mappedContractingPrism_boundary_eq_zero
    (S : ShortComplex (ChainComplex AddCommGrpCat ℕ)) (H : Homotopy (𝟙 S.X₂) 0)
    (K L : ChainComplex AddCommGrpCat ℕ) (f : K ⟶ S.X₁) (g : S.X₃ ⟶ L)
    {r : K ⟶ L} (R : Homotopy r r) (n : ℕ)
    (h : f.f (n + 1) ≫ S.f.f (n + 1) ≫ H.hom (n + 1) (n + 2) ≫
        S.g.f (n + 2) ≫ g.f (n + 2) = R.hom (n + 1) (n + 2))
    (hsurj : Function.Surjective (cyclesMap f (n + 1) ≫ contractingPrismClass S H n))
    {M : AddCommGrpCat} (d : L.homology (n + 2) ⟶ M)
    (hzero : closedPrismHomology R n ≫ d = 0) : homologyMap g (n + 2) ≫ d = 0 := by
  let : Epi (cyclesMap f (n + 1) ≫ contractingPrismClass S H n) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr hsurj
  apply (cancel_epi (cyclesMap f (n + 1) ≫ contractingPrismClass S H n)).mp
  calc
    _ = (K.homologyπ (n + 1) ≫ closedPrismHomology R n) ≫ d := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ d)
        (mappedContractingPrismClass_eq_closedPrism S H K L f g R n h)
    _ = _ := by rw [Category.assoc, hzero, comp_zero, comp_zero]

end SphereSixComplex
