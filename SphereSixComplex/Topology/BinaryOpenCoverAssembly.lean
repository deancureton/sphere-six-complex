/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Topology.BinaryOpenCoverMayerVietoris
public import SphereSixComplex.Topology.BinaryOpenCoverMapNaturality
public import SphereSixComplex.Topology.SingularExcisionOpenCover
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

/-! ## Identification with the general small-chain construction -/

/-- The set-valued binary cover associated to two open subsets. -/
public def binaryCoverFamily {X : TopCat} (U V : Opens X) : Bool → Set X :=
  fun b ↦ if b then (V : Set X) else (U : Set X)

/-- Every member of the set-valued binary cover is open. -/
public theorem binaryCoverFamily_isOpen {X : TopCat} (U V : Opens X) :
    ∀ b, IsOpen (binaryCoverFamily U V b) := by
  intro b
  cases b
  · exact U.2
  · exact V.2

/-- A lattice cover by `U` and `V` is a set-theoretic cover by the associated Bool family. -/
public theorem binaryCoverFamily_iUnion {X : TopCat} (U V : Opens X)
    (hcover : U ⊔ V = ⊤) :
    ⋃ b, binaryCoverFamily U V b = Set.univ := by
  ext x
  simp [binaryCoverFamily]
  have hx : x ∈ (U ⊔ V : Opens X) := by rw [hcover]; trivial
  simpa using hx

/-- For a binary cover, the general cover-small singular subcomplex is exactly the join of the
two singular open-image subcomplexes. -/
public theorem coverSmallSingularSubcomplex_binaryCoverFamily {X : TopCat}
    (U V : Opens X) :
    coverSmallSingularSubcomplex X (binaryCoverFamily U V) = coverUnion U V := by
  unfold coverSmallSingularSubcomplex binaryCoverFamily coverUnion singularOpenSubcomplex
  rw [iSup_bool_eq]
  change
    SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X (V : Set X))) ⊔
      SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X (U : Set X))) =
    SSet.Subcomplex.range (TopCat.toSSet.map U.inclusion') ⊔
      SSet.Subcomplex.range (TopCat.toSSet.map V.inclusion')
  rw [sup_comm]
  congr 1

/-- The generated binary-cover inclusion is a quasi-isomorphism whenever the opens cover the
ambient space. -/
public theorem coverChainInclusion_quasiIso_of_sup_eq_top {X : TopCat}
    (U V : Opens X) (hcover : U ⊔ V = ⊤) :
    QuasiIso (coverChainInclusion U V) := by
  have h := coverSmallChainQuasiIsomorphism_of_openCover X
    (binaryCoverFamily U V) (binaryCoverFamily_isOpen U V)
      (binaryCoverFamily_iUnion U V hcover)
  change QuasiIso
    (SSet.chainComplexMap (coverSmallSingularSubcomplex X (binaryCoverFamily U V)).ι
      (AddCommGrpCat.of ℤ)) at h
  rw [coverSmallSingularSubcomplex_binaryCoverFamily U V] at h
  exact h

/-- In every degree, the generated binary-cover inclusion induces a homology isomorphism. -/
public theorem coverChainInclusion_isIso_homologyMap_of_sup_eq_top {X : TopCat}
    (U V : Opens X) (hcover : U ⊔ V = ⊤) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (coverChainInclusion U V) n) := by
  let _ : QuasiIso (coverChainInclusion U V) :=
    coverChainInclusion_quasiIso_of_sup_eq_top U V hcover
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  infer_instance

/-! ## Chains of an open subset and their image subcomplex -/

/-- Integral singular chains of an open subset. -/
public noncomputable abbrev openSingularChains {X : TopCat} (U : Opens X) :
    ChainComplex AddCommGrpCat ℕ :=
  integralSimplicialChains.obj
    (TopCat.toSSet.obj ((Opens.toTopCat X).obj U))

/-- Integral chains on the image subcomplex associated to an open subset. -/
public noncomputable abbrev openRangeChains {X : TopCat} (U : Opens X) :
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
@[expose] public noncomputable def intersectionForwardChain {X : TopCat} (U V : Opens X) :
    openSingularChains (U ⊓ V) ⟶ (coverChainShortComplex U V).X₁ := by
  change openSingularChains (U ⊓ V) ⟶
    integralSimplicialChains.obj (coverIntersection U V)
  exact singularOpenCorestrictionChainMap (U ⊓ V) ≫
    openIntersectionChainComparison U V

/-- Explicit form of the forward intersection comparison. -/
public theorem intersectionForwardChain_eq {X : TopCat} (U V : Opens X) :
    intersectionForwardChain U V =
      singularOpenCorestrictionChainMap (U ⊓ V) ≫
        openIntersectionChainComparison U V := rfl

private noncomputable def openIntersectionPullbackChainMap {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    openSingularChains ((Opens.map f).obj U ⊓ (Opens.map f).obj V) ⟶
      openSingularChains (U ⊓ V) :=
  integralSimplicialChains.map
    (TopCat.toSSet.map (openIntersectionPreimageMap f U V))

private theorem intersectionForwardSSet_pullback_naturality {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    TopCat.toSSet.map (openIntersectionPreimageMap f U V) ≫
        singularOpenCorestriction (U ⊓ V) ≫ openIntersectionComparison U V =
      singularOpenCorestriction ((Opens.map f).obj U ⊓ (Opens.map f).obj V) ≫
        openIntersectionComparison ((Opens.map f).obj U) ((Opens.map f).obj V) ≫
          coverIntersectionPullbackMap f U V := by
  rw [← cancel_mono (coverIntersection U V).ι]
  simp [← Functor.map_comp, openIntersectionPreimageMap_comp_inclusion]

private theorem intersectionForwardChain_pullback_naturality {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    openIntersectionPullbackChainMap f U V ≫ intersectionForwardChain U V =
      intersectionForwardChain ((Opens.map f).obj U) ((Opens.map f).obj V) ≫
        coverIntersectionPullbackChainMap f U V := by
  change
    integralSimplicialChains.map
          (TopCat.toSSet.map (openIntersectionPreimageMap f U V)) ≫
        (singularOpenCorestrictionChainMap (U ⊓ V) ≫
          openIntersectionChainComparison U V) =
      (singularOpenCorestrictionChainMap
          ((Opens.map f).obj U ⊓ (Opens.map f).obj V) ≫
        openIntersectionChainComparison
          ((Opens.map f).obj U) ((Opens.map f).obj V)) ≫
        integralSimplicialChains.map (coverIntersectionPullbackMap f U V)
  simpa only [singularOpenCorestrictionChainMap, openIntersectionChainComparison,
    Functor.map_comp, Category.assoc] using
    congrArg integralSimplicialChains.map
      (intersectionForwardSSet_pullback_naturality f U V)

private theorem coverChainInclusion_pullback_naturality {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    coverUnionPullbackChainMap f U V ≫ coverChainInclusion U V =
      coverChainInclusion ((Opens.map f).obj U) ((Opens.map f).obj V) ≫
        integralSimplicialChains.map (TopCat.toSSet.map f) := by
  simpa only [coverUnionPullbackChainMap, coverChainInclusion,
    Functor.map_comp] using
    congrArg integralSimplicialChains.map
      (coverUnionPullbackMap_comp_inclusion f U V)

/-- The forward comparison from the actual open sets to the generated biproduct. -/
@[expose] public noncomputable def biprodForwardChain {X : TopCat} (U V : Opens X) :
    openSingularChains U ⊞ openSingularChains V ⟶
      (coverChainShortComplex U V).X₂ := by
  change openSingularChains U ⊞ openSingularChains V ⟶
    openRangeChains U ⊞ openRangeChains V
  exact biprod.map (singularOpenCorestrictionChainMap U)
    (singularOpenCorestrictionChainMap V)

public noncomputable instance intersectionForwardChain_isIso {X : TopCat}
    (U V : Opens X) : IsIso (intersectionForwardChain U V) := by
  change IsIso (singularOpenCorestrictionChainMap (U ⊓ V) ≫
    openIntersectionChainComparison U V)
  infer_instance

public noncomputable instance biprodForwardChain_isIso {X : TopCat}
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

public noncomputable abbrev homologyFunctor (n : ℕ) :
    ChainComplex AddCommGrpCat ℕ ⥤ AddCommGrpCat :=
  HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n

public instance homologyFunctor_additive (n : ℕ) :
    (homologyFunctor n).Additive := by
  dsimp only [homologyFunctor]
  infer_instance

public instance homologyFunctor_preservesBinaryBiproducts (n : ℕ) :
    PreservesBinaryBiproducts (homologyFunctor n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- The generated intersection has the homology of the actual open intersection. -/
@[expose] public noncomputable def intersectionHomologyIso {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    generatedIntersectionHomology U V n ≅
      (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj (U ⊓ V)) :=
  (homologyFunctor n).mapIso (asIso (intersectionForwardChain U V)).symm

/-- The inverse of the intersection comparison is induced by its forward chain map. -/
public theorem intersectionHomologyIso_inv {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    (intersectionHomologyIso U V n).inv =
      HomologicalComplex.homologyMap (intersectionForwardChain U V) n := rfl

/-- Naturality of the generated-to-ordinary intersection comparison with respect to a
commuting chain-level square. -/
public theorem intersectionHomologyIso_naturality {X : TopCat}
    {U V U' V' : Opens X}
    (f : (Opens.toTopCat X).obj (U ⊓ V) ⟶
      (Opens.toTopCat X).obj (U' ⊓ V'))
    (b : (coverChainShortComplex U V).X₁ ⟶ (coverChainShortComplex U' V').X₁)
    (h : intersectionForwardChain U V ≫ b =
      integralSimplicialChains.map (TopCat.toSSet.map f) ≫
        intersectionForwardChain U' V') (n : ℕ) :
    HomologicalComplex.homologyMap b n ≫ (intersectionHomologyIso U' V' n).hom =
      (intersectionHomologyIso U V n).hom ≫
        (integralHomologyFunctor n).map f := by
  have hn :
      (intersectionHomologyIso U V n).inv ≫
          HomologicalComplex.homologyMap b n =
        (integralHomologyFunctor n).map f ≫
          (intersectionHomologyIso U' V' n).inv := by
    change
      HomologicalComplex.homologyMap (intersectionForwardChain U V) n ≫
          HomologicalComplex.homologyMap b n =
        HomologicalComplex.homologyMap
            (integralSimplicialChains.map (TopCat.toSSet.map f)) n ≫
          HomologicalComplex.homologyMap (intersectionForwardChain U' V') n
    rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp, h]
  apply (cancel_epi (intersectionHomologyIso U V n).inv).mp
  rw [← Category.assoc, hn]
  simp

/-- The generated middle term has the biproduct of the actual open-set homologies. -/
@[expose] public noncomputable def biprodHomologyIso {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    generatedBiprodHomology U V n ≅
      (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj U) ⊞
        (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj V) :=
  (homologyFunctor n).mapIso (asIso (biprodForwardChain U V)).symm ≪≫
    (homologyFunctor n).mapBiprod (openSingularChains U) (openSingularChains V)

/-- A quasi-isomorphism from cover-generated chains supplies the generated-union homology
isomorphism. -/
@[expose] public noncomputable def unionHomologyIsoOfQuasiIso {X : TopCat} {U V : Opens X}
    (h : QuasiIso (coverChainInclusion U V)) (n : ℕ) :
    generatedUnionHomology U V n ≅ (integralHomologyFunctor n).obj X := by
  change (homologyFunctor n).obj
      (integralSimplicialChains.obj (coverUnion U V)) ≅
    (homologyFunctor n).obj
      (integralSimplicialChains.obj (TopCat.toSSet.obj X))
  let _ : QuasiIso (coverChainInclusion U V) := h
  let e := asIso (HomologicalComplex.homologyMap (coverChainInclusion U V) n)
  exact e

/-- A subdivision certificate is one way to obtain the generated-union homology isomorphism. -/
noncomputable def unionHomologyIso {X : TopCat} {U V : Opens X}
    (D : CoverSubdivisionData U V) (n : ℕ) :
    generatedUnionHomology U V n ≅ (integralHomologyFunctor n).obj X :=
  unionHomologyIsoOfQuasiIso D.coverChainInclusion_quasiIso n

/-- An actual open cover supplies the generated-union homology isomorphism without a separate
subdivision certificate. -/
@[expose] public noncomputable def unionHomologyIsoOfCover {X : TopCat} {U V : Opens X}
    (hcover : U ⊔ V = ⊤) (n : ℕ) :
    generatedUnionHomology U V n ≅ (integralHomologyFunctor n).obj X :=
  unionHomologyIsoOfQuasiIso
    (coverChainInclusion_quasiIso_of_sup_eq_top U V hcover) n

private theorem intersectionHomologyIso_inv_pullback_naturality {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) (n : ℕ) :
    (intersectionHomologyIso ((Opens.map f).obj U) ((Opens.map f).obj V) n).inv ≫
        generatedIntersectionPullbackHomologyMap f U V n =
      openIntersectionPullbackHomologyMap f U V n ≫
        (intersectionHomologyIso U V n).inv := by
  change
    HomologicalComplex.homologyMap
          (intersectionForwardChain ((Opens.map f).obj U) ((Opens.map f).obj V)) n ≫
        HomologicalComplex.homologyMap (coverIntersectionPullbackChainMap f U V) n =
      HomologicalComplex.homologyMap (openIntersectionPullbackChainMap f U V) n ≫
        HomologicalComplex.homologyMap (intersectionForwardChain U V) n
  rw [← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp,
    intersectionForwardChain_pullback_naturality]

private theorem unionHomologyIsoOfCover_hom_pullback_naturality {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y)
    (hsource : (Opens.map f).obj U ⊔ (Opens.map f).obj V = ⊤)
    (htarget : U ⊔ V = ⊤) (n : ℕ) :
    generatedUnionPullbackHomologyMap f U V n ≫
        (unionHomologyIsoOfCover htarget n).hom =
      (unionHomologyIsoOfCover hsource n).hom ≫
        (integralHomologyFunctor n).map f := by
  change
    (homologyFunctor n).map (coverUnionPullbackChainMap f U V) ≫
        (homologyFunctor n).map (coverChainInclusion U V) =
      (homologyFunctor n).map
          (coverChainInclusion ((Opens.map f).obj U) ((Opens.map f).obj V)) ≫
        (homologyFunctor n).map
          (integralSimplicialChains.map (TopCat.toSSet.map f))
  simpa only [Functor.map_comp] using congrArg (homologyFunctor n).map
    (coverChainInclusion_pullback_naturality f U V)

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

/-- The three canonical comparison isomorphisms supplied by a quasi-isomorphism from
cover-generated chains. -/
@[expose] public noncomputable def openCoverHomologyComparisonOfQuasiIso
    {X : TopCat} {U V : Opens X} (h : QuasiIso (coverChainInclusion U V)) :
    OpenCoverHomologyComparison U V where
  intersectionIso := intersectionHomologyIso U V
  biprodIso := biprodHomologyIso U V
  unionIso := unionHomologyIsoOfQuasiIso h
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

/-- A subdivision certificate is one way to obtain the canonical open-cover comparison. -/
noncomputable def openCoverHomologyComparisonOfSubdivision
    {X : TopCat} {U V : Opens X} (D : CoverSubdivisionData U V) :
    OpenCoverHomologyComparison U V :=
  openCoverHomologyComparisonOfQuasiIso D.coverChainInclusion_quasiIso

/-- The canonical homology comparison for two open subsets which cover their ambient space. -/
@[expose] public noncomputable def openCoverHomologyComparisonOfCover
    {X : TopCat} {U V : Opens X} (hcover : U ⊔ V = ⊤) :
    OpenCoverHomologyComparison U V :=
  openCoverHomologyComparisonOfQuasiIso
    (coverChainInclusion_quasiIso_of_sup_eq_top U V hcover)

/-! ## Canonical comparison under oriented refinement -/

/-- The map between intersections induced by an oriented refinement of two binary covers. -/
@[expose] public def openIntersectionRefinementMap {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') :
    (Opens.toTopCat X).obj (U ⊓ V) ⟶ (Opens.toTopCat X).obj (U' ⊓ V') :=
  (Opens.toTopCat X).map (homOfLE (inf_le_inf hU hV))

/-- The homology map between intersections induced by an oriented refinement. -/
@[expose] public noncomputable def openIntersectionRefinementHomologyMap {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') (n : ℕ) :
    (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj (U ⊓ V)) ⟶
      (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj (U' ⊓ V')) :=
  (integralHomologyFunctor n).map (openIntersectionRefinementMap hU hV)

/-- The induced map between generated intersection homology groups. -/
@[expose] public noncomputable def generatedIntersectionRefinementHomologyMap {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') (n : ℕ) :
    generatedIntersectionHomology U V n ⟶ generatedIntersectionHomology U' V' n :=
  HomologicalComplex.homologyMap (coverIntersectionRefinementMap hU hV) n

/-- The induced map between generated union homology groups. -/
@[expose] public noncomputable def generatedUnionRefinementHomologyMap {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') (n : ℕ) :
    generatedUnionHomology U V n ⟶ generatedUnionHomology U' V' n :=
  HomologicalComplex.homologyMap (coverUnionRefinementMap hU hV) n

private theorem intersectionRefinementSSetNaturality {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') :
    singularOpenCorestriction (U ⊓ V) ≫ openIntersectionComparison U V ≫
        SSet.Subcomplex.homOfLE (inf_le_inf
          (singularOpenSubcomplex_mono hU) (singularOpenSubcomplex_mono hV)) =
      TopCat.toSSet.map (openIntersectionRefinementMap hU hV) ≫
        singularOpenCorestriction (U' ⊓ V') ≫
          openIntersectionComparison U' V' := by
  rw [← cancel_mono (coverIntersection U' V').ι]
  simp [← Functor.map_comp, openIntersectionRefinementMap]
  congr 1

private theorem intersectionRefinementChainNaturality {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') :
    (singularOpenCorestrictionChainMap (U ⊓ V) ≫ openIntersectionChainComparison U V) ≫
        coverIntersectionRefinementMap hU hV =
      integralSimplicialChains.map
          (TopCat.toSSet.map (openIntersectionRefinementMap hU hV)) ≫
        (singularOpenCorestrictionChainMap (U' ⊓ V') ≫
          openIntersectionChainComparison U' V') := by
  simpa only [singularOpenCorestrictionChainMap, openIntersectionChainComparison,
    coverIntersectionRefinementMap, Functor.map_comp, Category.assoc] using
    congrArg integralSimplicialChains.map
      (intersectionRefinementSSetNaturality hU hV)

private theorem unionRefinementChainNaturality {X : TopCat}
    {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') :
    coverUnionRefinementMap hU hV ≫ coverChainInclusion U' V' =
      coverChainInclusion U V := by
  dsimp [coverUnionRefinementMap, coverChainInclusion]
  rw [← Functor.map_comp]
  rfl

/-- The intersection comparison square for canonical ordinary-homology comparisons. -/
public theorem openCoverHomologyComparisonOfCover_intersection_refinement_naturality
    {X : TopCat} {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V')
    (hcover : U ⊔ V = ⊤) (hcover' : U' ⊔ V' = ⊤) (n : ℕ) :
    generatedIntersectionRefinementHomologyMap hU hV n ≫
        ((openCoverHomologyComparisonOfCover hcover').intersectionIso n).hom =
      ((openCoverHomologyComparisonOfCover hcover).intersectionIso n).hom ≫
        openIntersectionRefinementHomologyMap hU hV n := by
  apply (cancel_epi
    ((openCoverHomologyComparisonOfCover hcover).intersectionIso n).inv).mp
  apply (cancel_mono
    ((openCoverHomologyComparisonOfCover hcover').intersectionIso n).inv).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id]
  change
    HomologicalComplex.homologyMap
        (singularOpenCorestrictionChainMap (U ⊓ V) ≫
          openIntersectionChainComparison U V) n ≫
      HomologicalComplex.homologyMap (coverIntersectionRefinementMap hU hV) n =
    HomologicalComplex.homologyMap
        (integralSimplicialChains.map
          (TopCat.toSSet.map (openIntersectionRefinementMap hU hV))) n ≫
      HomologicalComplex.homologyMap
        (singularOpenCorestrictionChainMap (U' ⊓ V') ≫
          openIntersectionChainComparison U' V') n
  rw [← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp,
    intersectionRefinementChainNaturality hU hV]

/-- The union comparison square for canonical ordinary-homology comparisons. -/
public theorem openCoverHomologyComparisonOfCover_union_refinement_naturality
    {X : TopCat} {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V')
    (hcover : U ⊔ V = ⊤) (hcover' : U' ⊔ V' = ⊤) (n : ℕ) :
    generatedUnionRefinementHomologyMap hU hV n ≫
        ((openCoverHomologyComparisonOfCover hcover').unionIso n).hom =
      ((openCoverHomologyComparisonOfCover hcover).unionIso n).hom := by
  change HomologicalComplex.homologyMap (coverUnionRefinementMap hU hV) n ≫
      HomologicalComplex.homologyMap (coverChainInclusion U' V') n =
    HomologicalComplex.homologyMap (coverChainInclusion U V) n
  rw [← HomologicalComplex.homologyMap_comp,
    unionRefinementChainNaturality hU hV]

/-- The canonical ordinary homology comparisons commute with pullback along a continuous map. -/
public theorem openCoverHomologyComparisonOfCover_pullbackNaturality
    {X Y : TopCat} (f : X ⟶ Y) (U V : Opens Y)
    (hsource : (Opens.map f).obj U ⊔ (Opens.map f).obj V = ⊤)
    (htarget : U ⊔ V = ⊤) :
    (openCoverHomologyComparisonOfCover hsource).PullbackNaturality f U V
      (openCoverHomologyComparisonOfCover htarget) where
  intersection n := by
    change generatedIntersectionPullbackHomologyMap f U V n ≫
        (intersectionHomologyIso U V n).hom =
      (intersectionHomologyIso
          ((Opens.map f).obj U) ((Opens.map f).obj V) n).hom ≫
        openIntersectionPullbackHomologyMap f U V n
    apply (cancel_epi
      (intersectionHomologyIso ((Opens.map f).obj U) ((Opens.map f).obj V) n).inv).mp
    rw [← Category.assoc,
      intersectionHomologyIso_inv_pullback_naturality,
      Category.assoc,
      (intersectionHomologyIso U V n).inv_hom_id,
      Category.comp_id,
      (intersectionHomologyIso
        ((Opens.map f).obj U) ((Opens.map f).obj V) n).inv_hom_id_assoc]
  union n := unionHomologyIsoOfCover_hom_pullback_naturality
    f U V hsource htarget n

/-- Every binary open cover admits the complete ordinary singular-homology comparison. -/
public theorem integralOpenCoverComparisonStatement :
    IntegralOpenCoverComparisonStatement := by
  intro X U V hcover
  exact ⟨openCoverHomologyComparisonOfCover hcover⟩

/-- Binary-cover subdivision implies the complete ordinary open-cover comparison. -/
public theorem integralOpenCoverComparisonStatement_of_binaryOpenCoverSubdivision
    (h : BinaryOpenCoverSubdivisionStatement) :
    IntegralOpenCoverComparisonStatement := by
  intro X U V hcover
  obtain ⟨D⟩ := h X U V hcover
  exact ⟨openCoverHomologyComparisonOfSubdivision D⟩

end SphereSixComplex.BinaryOpenCover
