module

public import SphereSixComplex.Topology.FirstQuadrantSingleColumnTotal
public import SphereSixComplex.Topology.BoundarySevenFaceNeighborhoodIntersections
public import SphereSixComplex.Topology.BoundarySevenFaceNeighborhoodLocalComparison
public import SphereSixComplex.Topology.SixSphereLowIntegralHomology

/-!
# Global Cech comparison for the boundary of the seven-simplex

This file assembles the two canonical augmented Cech nerves which occur in the comparison
between the simplicial boundary and the singular complex small for the eight affine face
neighbourhoods.  In particular, it constructs the actual totalized Cech augmentation (rather
than leaving it as structure data), the map between the two Cech bicomplexes, and proves the
strict compatibility of all three canonical augmentations.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

universe u v

set_option linter.style.haveILetI false in
/-- A finite coproduct of quasi-isomorphisms of chain complexes is a quasi-isomorphism. -/
public theorem quasiIso_finite_coproduct
    {I : Type} [Finite I]
    (K L : I → FirstQuadrantChainComplex)
    (f : ∀ i, K i ⟶ L i) (hf : ∀ i, QuasiIso (f i)) :
    QuasiIso (CategoryTheory.Limits.Sigma.map f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat
    (ComplexShape.down ℕ) n
  let σK := sigmaComparison H K
  let σL := sigmaComparison H L
  haveI hfi (i : I) : IsIso (H.map (f i)) := by
    exact (quasiIsoAt_iff_isIso_homologyMap (f i) n).mp
      ((hf i).quasiIsoAt n)
  haveI : IsIso (CategoryTheory.Limits.Sigma.map fun i ↦ H.map (f i)) := inferInstance
  haveI : IsIso σK := by dsimp [σK]; infer_instance
  haveI : IsIso σL := by dsimp [σL]; infer_instance
  have hnat : σK ≫ H.map (CategoryTheory.Limits.Sigma.map f) =
      CategoryTheory.Limits.Sigma.map (fun i ↦ H.map (f i)) ≫ σL := by
    apply Sigma.hom_ext
    intro i
    simp only [← Category.assoc, σK, σL,
      CategoryTheory.Limits.ι_comp_sigmaComparison,
      ← H.map_comp, CategoryTheory.Limits.Sigma.ι_map]
    rw [Category.assoc,
      CategoryTheory.Limits.ι_comp_sigmaComparison, ← H.map_comp]
  haveI : IsIso (σK ≫ H.map (CategoryTheory.Limits.Sigma.map f)) := by
    rw [hnat]
    infer_instance
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ σK
    (H.map (CategoryTheory.Limits.Sigma.map f)) inferInstance inferInstance

set_option linter.style.haveILetI false in
/-- A functor to chain complexes which preserves a finite coproduct carries a coproduct of
maps sent to quasi-isomorphisms to a quasi-isomorphism. -/
public theorem quasiIso_map_finite_coproduct
    {C : Type u} [Category.{v} C] {I : Type} [Finite I]
    (F : C ⥤ FirstQuadrantChainComplex.{0})
    [HasColimitsOfShape (Discrete I) C]
    [PreservesColimitsOfShape (Discrete I) F]
    (K L : I → C) (f : ∀ i, K i ⟶ L i)
    (hf : ∀ i, QuasiIso (F.map (f i))) :
    QuasiIso (F.map (CategoryTheory.Limits.Sigma.map f)) := by
  let σK := sigmaComparison F K
  let σL := sigmaComparison F L
  let sf := CategoryTheory.Limits.Sigma.map (fun i ↦ F.map (f i))
  haveI : IsIso σK := by dsimp [σK]; infer_instance
  haveI : IsIso σL := by dsimp [σL]; infer_instance
  haveI : QuasiIso sf := quasiIso_finite_coproduct
    (fun i ↦ F.obj (K i)) (fun i ↦ F.obj (L i))
    (fun i ↦ F.map (f i)) hf
  have hnat : σK ≫ F.map (CategoryTheory.Limits.Sigma.map f) = sf ≫ σL := by
    apply Sigma.hom_ext
    intro i
    simp only [← Category.assoc, σK, σL, sf,
      CategoryTheory.Limits.ι_comp_sigmaComparison,
      ← F.map_comp, CategoryTheory.Limits.Sigma.ι_map]
    rw [Category.assoc,
      CategoryTheory.Limits.ι_comp_sigmaComparison, ← F.map_comp]
  haveI : QuasiIso σK := inferInstance
  haveI : QuasiIso σL := inferInstance
  haveI : QuasiIso (σK ≫ F.map (CategoryTheory.Limits.Sigma.map f)) := by
    rw [hnat]
    infer_instance
  exact quasiIso_of_comp_left σK
    (F.map (CategoryTheory.Limits.Sigma.map f))

/-- The simplicial face presentation, regarded as an arrow. -/
public noncomputable def boundarySevenSimplicialFacePresentationArrow : Arrow SSet :=
  Arrow.mk boundarySevenSimplicialFacePresentation

/-- The simplicial face presentation evaluated in one inner simplicial degree. -/
public noncomputable def boundarySevenSimplicialFacePresentationEvaluationArrow
    (n : SimplexCategoryᵒᵖ) : Arrow (Type 0) :=
  Arrow.mk (boundarySevenSimplicialFacePresentation.app n)

/-- A chosen splitting of the evaluated simplicial face presentation. -/
public noncomputable def boundarySevenSimplicialFacePresentationEvaluationSplitEpi
    (n : SimplexCategoryᵒᵖ) :
    SplitEpi (boundarySevenSimplicialFacePresentationEvaluationArrow n).hom := by
  let h := boundarySevenSimplicialFacePresentation_app_surjective n
  exact
    { section_ := ↾ fun z ↦ Function.surjInv h z
      id := by
        ext z
        exact Function.rightInverse_surjInv h z }

/-- The evaluated simplicial face-presentation Cech nerve has an extra degeneracy. -/
public noncomputable def boundarySevenSimplicialFaceEvaluationExtraDegeneracy
    (n : SimplexCategoryᵒᵖ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (boundarySevenSimplicialFacePresentationEvaluationArrow n).augmentedCechNerve :=
  Arrow.AugmentedCechNerve.extraDegeneracy
    (boundarySevenSimplicialFacePresentationEvaluationArrow n)
    (boundarySevenSimplicialFacePresentationEvaluationSplitEpi n)

/-- Integral coefficients on the evaluated augmented Cech nerve of the simplicial face
presentation. -/
public noncomputable abbrev boundarySevenSimplicialFaceIntegralEvaluationCech
    (k : ℕ) : SimplicialObject.Augmented AddCommGrpCat :=
  ((SimplicialObject.Augmented.whiskering (Type 0) AddCommGrpCat).obj
    (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
      (boundarySevenSimplicialFacePresentationEvaluationArrow
        (Opposite.op (SimplexCategory.mk k))).augmentedCechNerve

/-- The integral evaluated face-presentation Cech nerve retains its extra degeneracy. -/
public noncomputable def boundarySevenSimplicialFaceIntegralEvaluationExtraDegeneracy
    (k : ℕ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (boundarySevenSimplicialFaceIntegralEvaluationCech k) :=
  (boundarySevenSimplicialFaceEvaluationExtraDegeneracy
    (Opposite.op (SimplexCategory.mk k))).map
      (sigmaConst.obj (AddCommGrpCat.of ℤ))

/-- Each horizontal row of the augmented face-presentation Cech complex contracts onto the
corresponding chain group of the simplicial boundary. -/
public noncomputable def boundarySevenSimplicialFaceIntegralCechRowHomotopyEquiv
    (k : ℕ) :
    HomotopyEquiv
      (AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj
          (boundarySevenSimplicialFaceIntegralEvaluationCech k)))
      ((ChainComplex.single₀ AddCommGrpCat).obj
        (SimplicialObject.Augmented.point.obj
          (boundarySevenSimplicialFaceIntegralEvaluationCech k))) :=
  (boundarySevenSimplicialFaceIntegralEvaluationExtraDegeneracy k).homotopyEquiv

/-- Thus every horizontal row augmentation of the simplicial face resolution is a
quasi-isomorphism. -/
public theorem boundarySevenSimplicialFaceIntegralCechRowAugmentation_quasiIso
    (k : ℕ) :
    QuasiIso (AlternatingFaceMapComplex.ε.app
      (boundarySevenSimplicialFaceIntegralEvaluationCech k)) :=
  (boundarySevenSimplicialFaceIntegralCechRowHomotopyEquiv k).quasiIso_hom

/-- The map of the two degree-zero Cech presentation objects is literally the finite coproduct
of the eight canonical local face comparisons. -/
public theorem boundarySevenFacePresentationSourceMap_eq_sigmaMap :
    boundarySevenFacePresentationSourceMap =
      CategoryTheory.Limits.Sigma.map
        (fun i : Fin 8 ↦ boundarySevenFaceNeighborhoodLocalComparisonSSetMap i) := by
  apply Sigma.hom_ext
  intro i
  rw [boundarySevenFacePresentationSourceMap_iota,
    CategoryTheory.Limits.Sigma.ι_map]
  rfl

set_option linter.style.haveILetI false in
/-- Consequently the canonical map on the degree-zero Cech presentation objects induces a
quasi-isomorphism on integral chains.  This is the first graded piece of the vertical-column
filtration of the Cech total map. -/
public theorem boundarySevenFacePresentationSourceIntegralChainMap_quasiIso :
    QuasiIso (SSet.chainComplexMap boundarySevenFacePresentationSourceMap
      (AddCommGrpCat.of ℤ)) := by
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  let K : Fin 8 → SSet.{0} := fun _ ↦ (Δ[6] : SSet.{0})
  let L : Fin 8 → SSet.{0} := fun i ↦
    TopCat.toSSet.obj (TopCat.of (boundarySevenComparisonFaceNeighborhood i))
  let f : ∀ i, K i ⟶ L i :=
    fun i ↦ boundarySevenFaceNeighborhoodLocalComparisonSSetMap i
  letI : PreservesColimitsOfShape (Discrete (Fin 8)) F := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    change PreservesColimitsOfShape (Discrete (Fin 8))
      ((evaluation SimplexCategoryᵒᵖ Type).obj
        (Opposite.op (SimplexCategory.mk n)) ⋙
          sigmaConst.obj (AddCommGrpCat.of ℤ))
    infer_instance
  have hf : ∀ i, QuasiIso (F.map (f i)) := by
    intro i
    exact boundarySevenFaceNeighborhoodLocalIntegralComparison_quasiIso i
  have h := quasiIso_map_finite_coproduct F K L f hf
  rw [boundarySevenFacePresentationSourceMap_eq_sigmaMap]
  exact h

/-- The augmented Cech nerve of the simplicial face presentation. -/
public noncomputable def boundarySevenSimplicialFaceAugmentedCechNerve :
    SimplicialObject.Augmented SSet :=
  boundarySevenSimplicialFacePresentationArrow.augmentedCechNerve

/-- Integral chains in the inner simplicial direction of the face-presentation Cech nerve. -/
public noncomputable def boundarySevenSimplicialFaceAugmentedCechChains :
    SimplicialObject.Augmented (ChainComplex AddCommGrpCat ℕ) :=
  ((SimplicialObject.Augmented.whiskering SSet
    (ChainComplex AddCommGrpCat ℕ)).obj
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ))).obj
        boundarySevenSimplicialFaceAugmentedCechNerve

/-- The Cech--simplicial bicomplex of the eight standard faces. -/
public noncomputable def boundarySevenSimplicialFaceCechBicomplex :
    FirstQuadrantBicomplex :=
  AlternatingFaceMapComplex.obj
    (SimplicialObject.Augmented.drop.obj
      boundarySevenSimplicialFaceAugmentedCechChains)

/-- The direct-sum total of the Cech--simplicial bicomplex. -/
public noncomputable def boundarySevenSimplicialFaceCechTotal :
    FirstQuadrantChainComplex :=
  boundarySevenSimplicialFaceCechBicomplex.total (ComplexShape.down ℕ)

/-- The outer augmentation of the Cech--simplicial bicomplex. -/
public noncomputable def boundarySevenSimplicialFaceCechOuterAugmentation :
    boundarySevenSimplicialFaceCechBicomplex ⟶
      firstQuadrantSingleZeroBicomplex
        ((∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)) :=
  AlternatingFaceMapComplex.ε.app boundarySevenSimplicialFaceAugmentedCechChains

/-- The map of augmented Cech nerves induced by the facewise local comparison square. -/
public noncomputable def boundarySevenFaceAugmentedCechNerveMap :
    boundarySevenSimplicialFaceAugmentedCechNerve ⟶
      boundarySevenFaceNeighborhoodAugmentedCechNerve :=
  Arrow.mapAugmentedCechNerve boundarySevenFacePresentationArrowMap

/-- Apply integral chains to the map of augmented Cech nerves. -/
public noncomputable def boundarySevenFaceAugmentedCechChainMap :
    boundarySevenSimplicialFaceAugmentedCechChains ⟶
      boundarySevenFaceNeighborhoodAugmentedCechChains :=
  ((SimplicialObject.Augmented.whiskering SSet
    (ChainComplex AddCommGrpCat ℕ)).obj
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ))).map
        boundarySevenFaceAugmentedCechNerveMap

/-- The induced morphism of the two first-quadrant Cech bicomplexes. -/
public noncomputable def boundarySevenFaceCechBicomplexMap :
    boundarySevenSimplicialFaceCechBicomplex ⟶
      boundarySevenFaceNeighborhoodCechBicomplex :=
  AlternatingFaceMapComplex.map
    (SimplicialObject.Augmented.drop.map boundarySevenFaceAugmentedCechChainMap)

/-- The induced map of direct-sum total complexes. -/
public noncomputable def boundarySevenFaceCechTotalMap :
    boundarySevenSimplicialFaceCechTotal ⟶
      boundarySevenFaceNeighborhoodCechTotal :=
  HomologicalComplex₂.total.map boundarySevenFaceCechBicomplexMap
    (ComplexShape.down ℕ)

/-- Totalize the Cech--simplicial augmentation and identify the total of its unique target
column with the ordinary simplicial chain complex. -/
public noncomputable def boundarySevenSimplicialFaceCechTotalAugmentation :
    boundarySevenSimplicialFaceCechTotal ⟶
      (∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ) :=
  HomologicalComplex₂.total.map boundarySevenSimplicialFaceCechOuterAugmentation
      (ComplexShape.down ℕ) ≫
    firstQuadrantTotalToSingleZero
      ((∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ))

/-- The canonical totalized augmentation from the face-neighbourhood Cech total to cover-small
integral singular chains. -/
public noncomputable def boundarySevenFaceNeighborhoodCechTotalAugmentation :
    boundarySevenFaceNeighborhoodCechTotal ⟶
      CoverSmallIntegralSingularChainComplex
        (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
        boundarySevenComparisonFaceNeighborhood :=
  HomologicalComplex₂.total.map boundarySevenFaceNeighborhoodCechOuterAugmentation
      (ComplexShape.down ℕ) ≫
    firstQuadrantTotalToSingleZero
      (CoverSmallIntegralSingularChainComplex
        (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
        boundarySevenComparisonFaceNeighborhood)

/-- The evaluated horizontal row of the outer neighbourhood-Cech augmentation, in the precise
coefficient presentation furnished by the evaluated augmented Cech nerve. -/
public noncomputable def boundarySevenFaceNeighborhoodCechOuterAugmentationRow (k : ℕ) :
    AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj
          (boundarySevenFaceNeighborhoodIntegralEvaluationCech k)) ⟶
      (ChainComplex.single₀ AddCommGrpCat).obj
        (SimplicialObject.Augmented.point.obj
          (boundarySevenFaceNeighborhoodIntegralEvaluationCech k)) :=
  AlternatingFaceMapComplex.ε.app
    (boundarySevenFaceNeighborhoodIntegralEvaluationCech k)

/-- The previously constructed extra degeneracy proves that every actual horizontal row of the
outer augmentation is a quasi-isomorphism. -/
public theorem boundarySevenFaceNeighborhoodCechOuterAugmentationRow_quasiIso (k : ℕ) :
    QuasiIso (boundarySevenFaceNeighborhoodCechOuterAugmentationRow k) := by
  exact boundarySevenFaceNeighborhoodIntegralCechRowAugmentation_quasiIso k

/-- Naturality of the alternating-complex augmentation, before totalization. -/
public theorem boundarySevenFaceCechBicomplexMap_comp_outerAugmentation :
    boundarySevenFaceCechBicomplexMap ≫
        boundarySevenFaceNeighborhoodCechOuterAugmentation =
      boundarySevenSimplicialFaceCechOuterAugmentation ≫
        (ChainComplex.single₀ (ChainComplex AddCommGrpCat ℕ)).map
          (SSet.chainComplexMap
            (simplicialToCoverSmallSingularSet
              (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
              boundarySevenComparisonUnitLandsInFaceNeighborhoods)
            (AddCommGrpCat.of ℤ)) := by
  exact AlternatingFaceMapComplex.ε.naturality
    boundarySevenFaceAugmentedCechChainMap

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion into the total of a zero-column bicomplex is natural in the column. -/
public theorem firstQuadrantSingleZeroToTotal_naturality
    {K L : FirstQuadrantChainComplex} (f : K ⟶ L) :
    f ≫ firstQuadrantSingleZeroToTotal L =
      firstQuadrantSingleZeroToTotal K ≫
        HomologicalComplex₂.total.map
          ((ChainComplex.single₀ (ChainComplex AddCommGrpCat ℕ)).map f)
          (ComplexShape.down ℕ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f]
  dsimp only [firstQuadrantSingleZeroToTotal,
    firstQuadrantZeroColumnToTotal]
  simp only [HomologicalComplex.comp_f]
  simp only [show firstQuadrantSingleZeroColumnIso K = Iso.refl K by
      exact ChainComplex.single₀ObjXSelf K,
    show firstQuadrantSingleZeroColumnIso L = Iso.refl L by
      exact ChainComplex.single₀ObjXSelf L,
    Iso.refl_inv, HomologicalComplex.id_f, Category.id_comp]
  rw [HomologicalComplex₂.ιTotal_map]
  simp

set_option linter.style.haveILetI false in
/-- The projection from the total of a zero-column bicomplex is natural in the column. -/
public theorem firstQuadrantTotalToSingleZero_naturality
    {K L : FirstQuadrantChainComplex} (f : K ⟶ L) :
    HomologicalComplex₂.total.map
          ((ChainComplex.single₀ (ChainComplex AddCommGrpCat ℕ)).map f)
          (ComplexShape.down ℕ) ≫
        firstQuadrantTotalToSingleZero L =
      firstQuadrantTotalToSingleZero K ≫ f := by
  letI : IsIso (firstQuadrantSingleZeroToTotal K) :=
    (firstQuadrantSingleZeroTotalIso K).isIso_inv
  apply (cancel_epi (firstQuadrantSingleZeroToTotal K)).1
  rw [← Category.assoc, ← firstQuadrantSingleZeroToTotal_naturality]
  rw [Category.assoc, firstQuadrantSingleZeroToTotal_comp_projection]
  rw [Category.comp_id, ← Category.assoc,
    firstQuadrantSingleZeroToTotal_comp_projection, Category.id_comp]

/-- The total Cech map commutes strictly with the canonical totalized augmentations. -/
public theorem boundarySevenFaceCechTotalMap_comp_augmentation :
    boundarySevenFaceCechTotalMap ≫
        boundarySevenFaceNeighborhoodCechTotalAugmentation =
      boundarySevenSimplicialFaceCechTotalAugmentation ≫
        simplicialToCoverSmallSingularChainMap
          (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
          boundarySevenComparisonUnitLandsInFaceNeighborhoods := by
  let φ := simplicialToCoverSmallSingularChainMap
    (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
    boundarySevenComparisonUnitLandsInFaceNeighborhoods
  let S := boundarySevenSimplicialFaceCechOuterAugmentation
  let T := boundarySevenFaceNeighborhoodCechOuterAugmentation
  let F := boundarySevenFaceCechBicomplexMap
  change HomologicalComplex₂.total.map F (ComplexShape.down ℕ) ≫
      (HomologicalComplex₂.total.map T (ComplexShape.down ℕ) ≫
        firstQuadrantTotalToSingleZero _) =
    (HomologicalComplex₂.total.map S (ComplexShape.down ℕ) ≫
      firstQuadrantTotalToSingleZero _) ≫ φ
  calc
    _ = (HomologicalComplex₂.total.map F (ComplexShape.down ℕ) ≫
          HomologicalComplex₂.total.map T (ComplexShape.down ℕ)) ≫
          firstQuadrantTotalToSingleZero _ :=
      (Category.assoc _ _ _).symm
    _ = HomologicalComplex₂.total.map (F ≫ T) (ComplexShape.down ℕ) ≫
          firstQuadrantTotalToSingleZero _ := by
      rw [HomologicalComplex₂.total.map_comp]
    _ = HomologicalComplex₂.total.map
          (S ≫ (ChainComplex.single₀ (ChainComplex AddCommGrpCat ℕ)).map φ)
          (ComplexShape.down ℕ) ≫ firstQuadrantTotalToSingleZero _ := by
      rw [show F ≫ T =
          S ≫ (ChainComplex.single₀ (ChainComplex AddCommGrpCat ℕ)).map φ by
        exact boundarySevenFaceCechBicomplexMap_comp_outerAugmentation]
    _ = (HomologicalComplex₂.total.map S (ComplexShape.down ℕ) ≫
          HomologicalComplex₂.total.map
            ((ChainComplex.single₀ (ChainComplex AddCommGrpCat ℕ)).map φ)
            (ComplexShape.down ℕ)) ≫ firstQuadrantTotalToSingleZero _ := by
      rw [HomologicalComplex₂.total.map_comp]
    _ = HomologicalComplex₂.total.map S (ComplexShape.down ℕ) ≫
          (firstQuadrantTotalToSingleZero _ ≫ φ) := by
      rw [Category.assoc, firstQuadrantTotalToSingleZero_naturality]
    _ = _ := by rw [Category.assoc]

/-! ## Exact low-degree assembly endpoint -/

/-- The remaining input for the low-degree global comparison, after the canonical Cech maps
and their strict augmentation square have been constructed above.  The lift is the output of
totalizing a contraction of the simplicial face-presentation resolution; the other four fields
are precisely the degree-two and degree-three conclusions of the rowwise-to-total argument. -/
public structure BoundarySevenCechLowAssemblyInput where
  sourceLift :
    (∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ) ⟶
      boundarySevenSimplicialFaceCechTotal
  sourceLift_fac :
    sourceLift ≫ boundarySevenSimplicialFaceCechTotalAugmentation = 𝟙 _
  sourceLift_quasiIsoAt_two : QuasiIsoAt sourceLift 2
  sourceLift_quasiIsoAt_three : QuasiIsoAt sourceLift 3
  cechMap_quasiIsoAt_two : QuasiIsoAt boundarySevenFaceCechTotalMap 2
  cechMap_quasiIsoAt_three : QuasiIsoAt boundarySevenFaceCechTotalMap 3
  augmentation_quasiIsoAt_two :
    QuasiIsoAt boundarySevenFaceNeighborhoodCechTotalAugmentation 2
  augmentation_quasiIsoAt_three :
    QuasiIsoAt boundarySevenFaceNeighborhoodCechTotalAugmentation 3

/-- The canonical map from boundary chains to the neighbourhood Cech total obtained from a
contracting lift of the simplicial face resolution. -/
public noncomputable def boundarySevenBoundaryToFaceNeighborhoodCechTotal
    (h : BoundarySevenCechLowAssemblyInput) :
    (∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ) ⟶
      boundarySevenFaceNeighborhoodCechTotal :=
  h.sourceLift ≫ boundarySevenFaceCechTotalMap

/-- The constructed boundary-to-Cech map has exactly the required canonical composite. -/
public theorem boundarySevenBoundaryToFaceNeighborhoodCechTotal_fac
    (h : BoundarySevenCechLowAssemblyInput) :
    boundarySevenBoundaryToFaceNeighborhoodCechTotal h ≫
        boundarySevenFaceNeighborhoodCechTotalAugmentation =
      simplicialToCoverSmallSingularChainMap
        (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
        boundarySevenComparisonUnitLandsInFaceNeighborhoods := by
  unfold boundarySevenBoundaryToFaceNeighborhoodCechTotal
  rw [Category.assoc, boundarySevenFaceCechTotalMap_comp_augmentation]
  rw [← Category.assoc, h.sourceLift_fac, Category.id_comp]

/-- The exact low-degree Cech package consumed by the six-sphere homology reduction. -/
public noncomputable def boundarySevenFaceNeighborhoodCechLowComparison_of_assembly
    (h : BoundarySevenCechLowAssemblyInput) :
    BoundarySevenFaceNeighborhoodCechLowComparison where
  boundaryToCech := boundarySevenBoundaryToFaceNeighborhoodCechTotal h
  augmentation := boundarySevenFaceNeighborhoodCechTotalAugmentation
  fac := boundarySevenBoundaryToFaceNeighborhoodCechTotal_fac h
  boundaryToCech_quasiIsoAt_two :=
    quasiIsoAt_comp h.sourceLift boundarySevenFaceCechTotalMap 2
      (hφ := h.sourceLift_quasiIsoAt_two)
      (hφ' := h.cechMap_quasiIsoAt_two)
  boundaryToCech_quasiIsoAt_three :=
    quasiIsoAt_comp h.sourceLift boundarySevenFaceCechTotalMap 3
      (hφ := h.sourceLift_quasiIsoAt_three)
      (hφ' := h.cechMap_quasiIsoAt_three)
  augmentation_quasiIsoAt_two := h.augmentation_quasiIsoAt_two
  augmentation_quasiIsoAt_three := h.augmentation_quasiIsoAt_three

/-- Consequently the remaining low-degree Cech assembly input is sufficient for both desired
six-sphere homology vanishings and the disk-cover local acyclicity package. -/
public theorem sixSphere_lowHomology_and_diskLocalAcyclic_of_cechAssembly
    (h : BoundarySevenCechLowAssemblyInput) :
    (IsZero ((IntegralSingularChainComplexObj (TopCat.sphere.{0} 6)).homology 2) ∧
      IsZero ((IntegralSingularChainComplexObj (TopCat.sphere.{0} 6)).homology 3)) ∧
      DiskSevenCoverLocalRelativeLowAcyclic :=
  sixSphere_lowHomology_and_diskLocalAcyclic_of_cechLow
    (boundarySevenFaceNeighborhoodCechLowComparison_of_assembly h)

end SphereSixComplex
