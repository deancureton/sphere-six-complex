/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Topology.BinaryOpenCoverMayerVietoris
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Assembly of the ordinary open-cover Mayer--Vietoris comparison

The subdivision certificate makes the generated-cover inclusion a homology isomorphism. This
file supplies the remaining formal comparison with the ordinary homology groups of the two open
sets and their intersection. Singular simplices in an open subset identify with the range of
their inclusion into the ambient singular set. Homology preserves the resulting binary
biproduct, and the two canonical chain-level squares give the required naturality equations.

This file is ported from Paul Lezeau's independent formalisation. It reuses the separated
corestriction and generated-cover developments already present in this repository.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits TopologicalSpace

namespace SphereSixComplex.BinaryOpenCover

/-! ## Chains of an open subset and their image subcomplex -/

/-- Integral singular chains of an open subset. -/
noncomputable abbrev openSingularChains {X : TopCat} (U : Opens X) :
    ChainComplex AddCommGrpCat ℕ :=
  integralSimplicialChains.obj
    (TopCat.toSSet.obj ((Opens.toTopCat X).obj U))

/-- Integral chains on the image subcomplex associated to an open subset. -/
noncomputable abbrev openRangeChains {X : TopCat} (U : Opens X) :
    ChainComplex AddCommGrpCat ℕ :=
  integralSimplicialChains.obj (singularOpenSubcomplex U)

/-- Corestriction commutes with an inclusion of open subsets. -/
theorem singularOpenCorestriction_naturality {X : TopCat} {U V : Opens X}
    (h : U ≤ V) :
    singularOpenCorestriction U ≫
        SSet.Subcomplex.homOfLE (singularOpenSubcomplex_mono h) =
      TopCat.toSSet.map ((Opens.toTopCat X).map (homOfLE h)) ≫
        singularOpenCorestriction V := by
  rw [← cancel_mono (singularOpenSubcomplex V).ι]
  simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι,
    singularOpenCorestriction_comp_inclusion]
  rw [← Functor.map_comp]
  congr 1

/-- Chain-level form of naturality of open corestriction. -/
theorem singularOpenCorestrictionChainMap_naturality
    {X : TopCat} {U V : Opens X} (h : U ≤ V) :
    singularOpenCorestrictionChainMap U ≫
        integralSimplicialChains.map
          (SSet.Subcomplex.homOfLE (singularOpenSubcomplex_mono h)) =
      integralSimplicialChains.map
          (TopCat.toSSet.map ((Opens.toTopCat X).map (homOfLE h))) ≫
        singularOpenCorestrictionChainMap V := by
  simpa only [singularOpenCorestrictionChainMap, Functor.map_comp] using
    congrArg integralSimplicialChains.map
      (singularOpenCorestriction_naturality h)

/-! ## The three chain comparisons -/

/-- The forward chain comparison from the actual open intersection to the generated one. -/
noncomputable def intersectionForwardChain {X : TopCat} (U V : Opens X) :
    openSingularChains (U ⊓ V) ⟶ (coverChainShortComplex U V).X₁ := by
  change openSingularChains (U ⊓ V) ⟶
    integralSimplicialChains.obj (coverIntersection U V)
  exact singularOpenCorestrictionChainMap (U ⊓ V) ≫
    openIntersectionChainComparison U V

/-- The forward comparison from the actual open sets to the generated biproduct. -/
noncomputable def biprodForwardChain {X : TopCat} (U V : Opens X) :
    openSingularChains U ⊞ openSingularChains V ⟶
      (coverChainShortComplex U V).X₂ := by
  change openSingularChains U ⊞ openSingularChains V ⟶
    openRangeChains U ⊞ openRangeChains V
  exact biprod.map (singularOpenCorestrictionChainMap U)
    (singularOpenCorestrictionChainMap V)

noncomputable instance intersectionForwardChain_isIso {X : TopCat}
    (U V : Opens X) : IsIso (intersectionForwardChain U V) := by
  change IsIso (singularOpenCorestrictionChainMap (U ⊓ V) ≫
    openIntersectionChainComparison U V)
  infer_instance

noncomputable instance biprodForwardChain_isIso {X : TopCat}
    (U V : Opens X) : IsIso (biprodForwardChain U V) := by
  change IsIso (biprod.map (singularOpenCorestrictionChainMap U)
    (singularOpenCorestrictionChainMap V))
  change IsIso ((biprod.mapIso
    (asIso (singularOpenCorestrictionChainMap U))
    (asIso (singularOpenCorestrictionChainMap V))).hom)
  infer_instance

/-- Alternating inclusions between the actual open-set chain complexes. -/
noncomputable def openMVToBiprodChain {X : TopCat} (U V : Opens X) :
    openSingularChains (U ⊓ V) ⟶ openSingularChains U ⊞ openSingularChains V :=
  biprod.lift
    (integralSimplicialChains.map
      (TopCat.toSSet.map ((Opens.toTopCat X).map (Opens.infLELeft U V))))
    (-(integralSimplicialChains.map
      (TopCat.toSSet.map ((Opens.toTopCat X).map (Opens.infLERight U V)))))

/-- The sum of the two actual open-set inclusions at chain level. -/
noncomputable def openMVFromBiprodChain {X : TopCat} (U V : Opens X) :
    openSingularChains U ⊞ openSingularChains V ⟶
      integralSimplicialChains.obj (TopCat.toSSet.obj X) :=
  biprod.desc
    (integralSimplicialChains.map (TopCat.toSSet.map (Opens.inclusion' U)))
    (integralSimplicialChains.map (TopCat.toSSet.map (Opens.inclusion' V)))

private theorem intersectionComparison_comp_left {X : TopCat} (U V : Opens X) :
    openIntersectionComparison U V ≫
        SSet.Subcomplex.homOfLE (coverSubcomplexBicartSq U V).le₁₂ =
      SSet.Subcomplex.homOfLE
        (singularOpenSubcomplex_mono (inf_le_left : U ⊓ V ≤ U)) := by
  ext n x
  rfl

private theorem intersectionComparison_comp_right {X : TopCat} (U V : Opens X) :
    openIntersectionComparison U V ≫
        SSet.Subcomplex.homOfLE (coverSubcomplexBicartSq U V).le₁₃ =
      SSet.Subcomplex.homOfLE
        (singularOpenSubcomplex_mono (inf_le_right : U ⊓ V ≤ V)) := by
  ext n x
  rfl

private theorem intersectionForwardChain_comp_left {X : TopCat}
    (U V : Opens X) :
    (singularOpenCorestrictionChainMap (U ⊓ V) ≫
        openIntersectionChainComparison U V) ≫
        integralSimplicialChains.map
          (SSet.Subcomplex.homOfLE (coverSubcomplexBicartSq U V).le₁₂) =
      integralSimplicialChains.map
          (TopCat.toSSet.map ((Opens.toTopCat X).map (Opens.infLELeft U V))) ≫
        singularOpenCorestrictionChainMap U := by
  rw [Category.assoc, openIntersectionChainComparison, ← Functor.map_comp,
    intersectionComparison_comp_left,
    singularOpenCorestrictionChainMap_naturality
      (inf_le_left : U ⊓ V ≤ U)]
  congr 1

private theorem intersectionForwardChain_comp_right {X : TopCat}
    (U V : Opens X) :
    (singularOpenCorestrictionChainMap (U ⊓ V) ≫
        openIntersectionChainComparison U V) ≫
        integralSimplicialChains.map
          (SSet.Subcomplex.homOfLE (coverSubcomplexBicartSq U V).le₁₃) =
      integralSimplicialChains.map
          (TopCat.toSSet.map ((Opens.toTopCat X).map (Opens.infLERight U V))) ≫
        singularOpenCorestrictionChainMap V := by
  rw [Category.assoc, openIntersectionChainComparison, ← Functor.map_comp,
    intersectionComparison_comp_right,
    singularOpenCorestrictionChainMap_naturality
      (inf_le_right : U ⊓ V ≤ V)]
  congr 1

/-- The alternating chain comparison square commutes. -/
theorem openMVToBiprodChain_naturality {X : TopCat} (U V : Opens X) :
    openMVToBiprodChain U V ≫ biprodForwardChain U V =
      intersectionForwardChain U V ≫ (coverChainShortComplex U V).f := by
  change openMVToBiprodChain U V ≫
      biprod.map (singularOpenCorestrictionChainMap U)
        (singularOpenCorestrictionChainMap V) =
    (singularOpenCorestrictionChainMap (U ⊓ V) ≫
        openIntersectionChainComparison U V) ≫
      biprod.lift
        (integralSimplicialChains.map
          (SSet.Subcomplex.homOfLE (coverSubcomplexBicartSq U V).le₁₂))
        (-integralSimplicialChains.map
          (SSet.Subcomplex.homOfLE (coverSubcomplexBicartSq U V).le₁₃))
  apply biprod.hom_ext
  · simpa only [openMVToBiprodChain, Category.assoc, biprod.map_fst,
      biprod.lift_fst_assoc, biprod.lift_fst] using
      (intersectionForwardChain_comp_left U V).symm
  · simpa only [openMVToBiprodChain, Category.assoc, biprod.map_snd,
      biprod.lift_snd_assoc, biprod.lift_snd, Preadditive.neg_comp,
      Preadditive.comp_neg] using
      congrArg (fun f ↦ -f) (intersectionForwardChain_comp_right U V).symm

private theorem leftCorestriction_comp_union {X : TopCat} (U V : Opens X) :
    singularOpenCorestrictionChainMap U ≫
        integralSimplicialChains.map
          (SSet.Subcomplex.homOfLE (coverSubcomplexBicartSq U V).le₂₄) ≫
        coverChainInclusion U V =
      integralSimplicialChains.map (TopCat.toSSet.map (Opens.inclusion' U)) := by
  rw [singularOpenCorestrictionChainMap, coverChainInclusion,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1

private theorem rightCorestriction_comp_union {X : TopCat} (U V : Opens X) :
    singularOpenCorestrictionChainMap V ≫
        integralSimplicialChains.map
          (SSet.Subcomplex.homOfLE (coverSubcomplexBicartSq U V).le₃₄) ≫
        coverChainInclusion U V =
      integralSimplicialChains.map (TopCat.toSSet.map (Opens.inclusion' V)) := by
  rw [singularOpenCorestrictionChainMap, coverChainInclusion,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- The sum-to-union chain comparison square commutes. -/
theorem openMVFromBiprodChain_naturality {X : TopCat}
    (U V : Opens X) :
    biprodForwardChain U V ≫ (coverChainShortComplex U V).g ≫
        coverChainInclusion U V =
      openMVFromBiprodChain U V := by
  change biprod.map (singularOpenCorestrictionChainMap U)
      (singularOpenCorestrictionChainMap V) ≫
        biprod.desc
          (integralSimplicialChains.map
            (SSet.Subcomplex.homOfLE (coverSubcomplexBicartSq U V).le₂₄))
          (integralSimplicialChains.map
            (SSet.Subcomplex.homOfLE (coverSubcomplexBicartSq U V).le₃₄)) ≫
        coverChainInclusion U V = openMVFromBiprodChain U V
  apply biprod.hom_ext'
  · simpa only [openMVFromBiprodChain, Category.assoc,
      biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc] using
      leftCorestriction_comp_union U V
  · simpa only [openMVFromBiprodChain, Category.assoc,
      biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc] using
      rightCorestriction_comp_union U V

private theorem coverUnion_ι_app_zero_surjective {X : TopCat}
    (U V : Opens X) (hcover : U ⊔ V = ⊤) :
    Function.Surjective
      ((coverUnion U V).ι.app (Opposite.op (SimplexCategory.mk 0))) := by
  intro σ
  let x := TopCat.toSSetObj₀Equiv σ
  refine ⟨⟨σ, ?_⟩, rfl⟩
  have hx : x ∈ U ⊔ V := by
    rw [hcover]
    trivial
  change
    (∃ a, (TopCat.toSSet.map (Opens.inclusion' U)).app _ a = σ) ∨
      ∃ b, (TopCat.toSSet.map (Opens.inclusion' V)).app _ b = σ
  rcases Opens.mem_sup.mp hx with hx | hx
  · left
    refine ⟨TopCat.toSSetObj₀Equiv.symm ⟨x, hx⟩, ?_⟩
    apply TopCat.toSSetObj₀Equiv.injective
    rfl
  · right
    refine ⟨TopCat.toSSetObj₀Equiv.symm ⟨x, hx⟩, ?_⟩
    apply TopCat.toSSetObj₀Equiv.injective
    rfl

/-! ## Homology isomorphisms and the two naturality squares -/

noncomputable abbrev homologyFunctor (n : ℕ) :
    ChainComplex AddCommGrpCat ℕ ⥤ AddCommGrpCat :=
  HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n

local instance homologyFunctor_additive (n : ℕ) :
    (homologyFunctor n).Additive := by
  dsimp only [homologyFunctor]
  infer_instance

local instance homologyFunctor_preservesBinaryBiproducts (n : ℕ) :
    PreservesBinaryBiproducts (homologyFunctor n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- The generated intersection has the homology of the actual open intersection. -/
noncomputable def intersectionHomologyIso {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    generatedIntersectionHomology U V n ≅
      (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj (U ⊓ V)) :=
  (homologyFunctor n).mapIso (asIso (intersectionForwardChain U V)).symm

/-- The generated middle term has the biproduct of the actual open-set homologies. -/
noncomputable def biprodHomologyIso {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    generatedBiprodHomology U V n ≅
      (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj U) ⊞
        (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj V) :=
  (homologyFunctor n).mapIso (asIso (biprodForwardChain U V)).symm ≪≫
    (homologyFunctor n).mapBiprod (openSingularChains U) (openSingularChains V)

/-- Subdivision supplies the generated-union homology isomorphism. -/
noncomputable def unionHomologyIso {X : TopCat} {U V : Opens X}
    (D : CoverSubdivisionData U V) (n : ℕ) :
    generatedUnionHomology U V n ≅ (integralHomologyFunctor n).obj X := by
  change (homologyFunctor n).obj
      (integralSimplicialChains.obj (coverUnion U V)) ≅
    (homologyFunctor n).obj
      (integralSimplicialChains.obj (TopCat.toSSet.obj X))
  letI : IsIso (HomologicalComplex.homologyMap (coverChainInclusion U V) n) :=
    D.isIso_homologyMap n
  let e := asIso (HomologicalComplex.homologyMap (coverChainInclusion U V) n)
  exact e

private theorem homology_openMVToBiprodChain {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    (homologyFunctor n).map (openMVToBiprodChain U V) ≫
        ((homologyFunctor n).mapBiprod
          (openSingularChains U) (openSingularChains V)).hom =
      integralMVToBiprod U V n := by
  change (homologyFunctor n).map (openMVToBiprodChain U V) ≫
      ((homologyFunctor n).mapBiprod
        (openSingularChains U) (openSingularChains V)).hom =
    biprod.lift
      ((homologyFunctor n).map
        (integralSimplicialChains.map
          (TopCat.toSSet.map
            ((Opens.toTopCat X).map (Opens.infLELeft U V)))))
      (-((homologyFunctor n).map
        (integralSimplicialChains.map
          (TopCat.toSSet.map
            ((Opens.toTopCat X).map (Opens.infLERight U V))))))
  simpa only [openMVToBiprodChain, Functor.map_neg] using
    (biprod.map_lift_mapBiprod (F := homologyFunctor n)
      (openSingularChains U) (openSingularChains V)
      (integralSimplicialChains.map
        (TopCat.toSSet.map ((Opens.toTopCat X).map (Opens.infLELeft U V))))
      (-(integralSimplicialChains.map
        (TopCat.toSSet.map ((Opens.toTopCat X).map (Opens.infLERight U V))))))

private theorem homology_openMVFromBiprodChain {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    ((homologyFunctor n).mapBiprod
          (openSingularChains U) (openSingularChains V)).hom ≫
        integralMVFromBiprod U V n =
      (homologyFunctor n).map (openMVFromBiprodChain U V) := by
  change ((homologyFunctor n).mapBiprod
        (openSingularChains U) (openSingularChains V)).hom ≫
      biprod.desc
        ((homologyFunctor n).map
          (integralSimplicialChains.map
            (TopCat.toSSet.map (Opens.inclusion' U))))
        ((homologyFunctor n).map
          (integralSimplicialChains.map
            (TopCat.toSSet.map (Opens.inclusion' V)))) =
    (homologyFunctor n).map (openMVFromBiprodChain U V)
  simpa only [openMVFromBiprodChain] using
    (biprod.mapBiprod_hom_desc (F := homologyFunctor n)
      (openSingularChains U) (openSingularChains V)
      (integralSimplicialChains.map (TopCat.toSSet.map (Opens.inclusion' U)))
      (integralSimplicialChains.map (TopCat.toSSet.map (Opens.inclusion' V))))

/-- The degree-zero map from the homology of the two open sets covers ambient homology. -/
public theorem integralMVFromBiprod_zero_surjective
    {X : TopCat} (U V : Opens X) (hcover : U ⊔ V = ⊤) :
    Function.Surjective (integralMVFromBiprod U V 0) := by
  let _ : IsIso
      ((coverUnion U V).ι.app (Opposite.op (SimplexCategory.mk 0))) :=
    (isIso_iff_bijective _).mpr
      ⟨Subtype.coe_injective, coverUnion_ι_app_zero_surjective U V hcover⟩
  let _ : IsIso ((coverChainInclusion U V).f 0) := by
    change IsIso ((sigmaConst.obj (AddCommGrpCat.of ℤ)).map
      ((coverUnion U V).ι.app (Opposite.op (SimplexCategory.mk 0))))
    infer_instance
  let _ : Epi ((coverChainInclusion U V).f 0) := inferInstance
  let _ : Epi (coverChainShortComplex U V).g :=
    (coverChainShortComplex_shortExact U V).epi_g
  let _ : Epi ((coverChainShortComplex U V).g.f 0) := inferInstance
  let _ : Epi ((biprodForwardChain U V).f 0) := inferInstance
  let _ : Epi ((openMVFromBiprodChain U V).f 0) := by
    have h := HomologicalComplex.congr_hom
      (openMVFromBiprodChain_naturality U V) 0
    simp only [HomologicalComplex.comp_f] at h
    rw [← h]
    change Epi ((biprodForwardChain U V).f 0 ≫
      ((coverChainShortComplex U V).g.f 0 ≫ (coverChainInclusion U V).f 0))
    exact epi_comp'
      (inferInstance : Epi ((biprodForwardChain U V).f 0))
      (epi_comp'
        (inferInstance : Epi ((coverChainShortComplex U V).g.f 0))
        (inferInstance : Epi ((coverChainInclusion U V).f 0)))
  let hHomologyEpi : Epi
      ((homologyFunctor 0).map (openMVFromBiprodChain U V)) := by
    change Epi (HomologicalComplex.homologyMap
      (openMVFromBiprodChain U V) 0)
    apply HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
    simp [ComplexShape.down_Rel]
  exact (AddCommGrpCat.epi_iff_surjective _).mp
    (@epi_of_epi_fac _ _ _ _ _ _ _ _ hHomologyEpi
      (homology_openMVFromBiprodChain U V 0))

private theorem homologyFunctor_map_comp_mapIso_symm_hom_assoc
    {K L : ChainComplex AddCommGrpCat ℕ} (f : K ⟶ L) [IsIso f]
    (n : ℕ) {A : AddCommGrpCat} (g : (homologyFunctor n).obj K ⟶ A) :
    (homologyFunctor n).map f ≫
        ((homologyFunctor n).mapIso (asIso f).symm).hom ≫ g = g := by
  simpa only [Functor.mapIso_hom, Iso.symm_hom, Functor.mapIso_inv,
    asIso_hom] using
    ((homologyFunctor n).mapIso (asIso f)).hom_inv_id_assoc g

private theorem homology_openMVToBiprodChain_raw_naturality
    {X : TopCat} (U V : Opens X) (n : ℕ) :
    (homologyFunctor n).map (openMVToBiprodChain U V) ≫
        ((homologyFunctor n).mapBiprod
          (openSingularChains U) (openSingularChains V)).hom =
      (homologyFunctor n).map (intersectionForwardChain U V) ≫
        ((homologyFunctor n).map (coverChainShortComplex U V).f ≫
          (((homologyFunctor n).mapIso
              (asIso (biprodForwardChain U V)).symm).hom ≫
            ((homologyFunctor n).mapBiprod
              (openSingularChains U) (openSingularChains V)).hom)) := by
  calc
    _ = (homologyFunctor n).map
          (openMVToBiprodChain U V ≫ biprodForwardChain U V) ≫
        (((homologyFunctor n).mapIso
            (asIso (biprodForwardChain U V)).symm).hom ≫
          ((homologyFunctor n).mapBiprod
            (openSingularChains U) (openSingularChains V)).hom) := by
      rw [Functor.map_comp, Category.assoc,
        homologyFunctor_map_comp_mapIso_symm_hom_assoc]
    _ = (homologyFunctor n).map
          (intersectionForwardChain U V ≫
            (coverChainShortComplex U V).f) ≫
        (((homologyFunctor n).mapIso
            (asIso (biprodForwardChain U V)).symm).hom ≫
          ((homologyFunctor n).mapBiprod
            (openSingularChains U) (openSingularChains V)).hom) := by
      rw [openMVToBiprodChain_naturality]
    _ = _ := by rw [Functor.map_comp, Category.assoc]

private theorem homology_openMVFromBiprodChain_raw_naturality
    {X : TopCat} (U V : Opens X) (n : ℕ) :
    (homologyFunctor n).map (openMVFromBiprodChain U V) =
      (homologyFunctor n).map (biprodForwardChain U V) ≫
        ((homologyFunctor n).map (coverChainShortComplex U V).g ≫
          (homologyFunctor n).map (coverChainInclusion U V)) := by
  calc
    _ = (homologyFunctor n).map
          (biprodForwardChain U V ≫
            ((coverChainShortComplex U V).g ≫ coverChainInclusion U V)) :=
      congrArg (homologyFunctor n).map
        (openMVFromBiprodChain_naturality U V).symm
    _ = (homologyFunctor n).map (biprodForwardChain U V) ≫
        (homologyFunctor n).map
          ((coverChainShortComplex U V).g ≫ coverChainInclusion U V) :=
      (homologyFunctor n).map_comp _ _
    _ = _ := congrArg
      (fun q ↦ (homologyFunctor n).map (biprodForwardChain U V) ≫ q)
      ((homologyFunctor n).map_comp
        (coverChainShortComplex U V).g (coverChainInclusion U V))

/-- The three canonical comparison isomorphisms supplied by a subdivision certificate. -/
noncomputable def openCoverHomologyComparisonOfSubdivision
    {X : TopCat} {U V : Opens X} (D : CoverSubdivisionData U V) :
    OpenCoverHomologyComparison U V where
  intersectionIso := intersectionHomologyIso U V
  biprodIso := biprodHomologyIso U V
  unionIso := unionHomologyIso D
  toBiprod_comm n := by
    apply (cancel_epi (intersectionHomologyIso U V n).inv).mp
    rw [(intersectionHomologyIso U V n).inv_hom_id_assoc]
    change integralMVToBiprod U V n =
      (homologyFunctor n).map (intersectionForwardChain U V) ≫
        ((homologyFunctor n).map (coverChainShortComplex U V).f ≫
          (((homologyFunctor n).mapIso
              (asIso (biprodForwardChain U V)).symm).hom ≫
            ((homologyFunctor n).mapBiprod
              (openSingularChains U) (openSingularChains V)).hom))
    rw [← homology_openMVToBiprodChain]
    exact homology_openMVToBiprodChain_raw_naturality U V n
  fromBiprod_comm n := by
    apply (cancel_epi ((homologyFunctor n).map (biprodForwardChain U V))).mp
    change (homologyFunctor n).map (biprodForwardChain U V) ≫
        (((homologyFunctor n).mapIso
            (asIso (biprodForwardChain U V)).symm).hom ≫
          (((homologyFunctor n).mapBiprod
              (openSingularChains U) (openSingularChains V)).hom ≫
            integralMVFromBiprod U V n)) =
      (homologyFunctor n).map (biprodForwardChain U V) ≫
        ((homologyFunctor n).map (coverChainShortComplex U V).g ≫
          (homologyFunctor n).map (coverChainInclusion U V))
    rw [homologyFunctor_map_comp_mapIso_symm_hom_assoc,
      homology_openMVFromBiprodChain]
    exact homology_openMVFromBiprodChain_raw_naturality U V n

/-- Binary-cover subdivision implies the complete ordinary open-cover comparison. -/
public theorem integralOpenCoverComparisonStatement_of_binaryOpenCoverSubdivision
    (h : BinaryOpenCoverSubdivisionStatement) :
    IntegralOpenCoverComparisonStatement := by
  intro X U V hcover
  obtain ⟨D⟩ := h X U V hcover
  exact ⟨openCoverHomologyComparisonOfSubdivision D⟩

end SphereSixComplex.BinaryOpenCover
