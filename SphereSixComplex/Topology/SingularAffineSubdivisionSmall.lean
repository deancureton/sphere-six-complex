module

public import SphereSixComplex.Topology.SingularAffineSubdivision
public import SphereSixComplex.Topology.SingularExcision

/-!
# Affine subdivision on cover-small singular chains

Affine barycentric subdivision of a simplex only precomposes that simplex.  Consequently a
simplex which factors through one member of a cover subdivides entirely inside the same member.
This file packages that range-preservation statement as an endomorphism of the cover-small chain
complex and proves compatibility with its inclusion into all singular chains.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace SphereSixComplex

variable {iota : Type} (X : TopCat) (U : iota → Set X)

/-- A selected cover member through which a cover-small simplex factors. -/
public noncomputable def coverSmallSimplexPreimageIndex
    {n : SimplexCategoryᵒᵖ}
    (x : (coverSmallSingularSubcomplex X U : SSet).obj n) : iota :=
  ((mem_coverSmallSingularSubcomplex_iff_exists_preimage X U x.1).mp x.2).choose

/-- A selected lift of a cover-small simplex to its selected cover member. -/
public noncomputable def coverSmallSimplexPreimage
    {n : SimplexCategoryᵒᵖ}
    (x : (coverSmallSingularSubcomplex X U : SSet).obj n) :
    (TopCat.toSSet.obj
      (TopCat.of (U (coverSmallSimplexPreimageIndex X U x)))).obj n :=
  ((mem_coverSmallSingularSubcomplex_iff_exists_preimage X U x.1).mp
    x.2).choose_spec.choose

/-- The selected lift maps back to the underlying ambient singular simplex. -/
public theorem coverSmallSimplexPreimage_spec
    {n : SimplexCategoryᵒᵖ}
    (x : (coverSmallSingularSubcomplex X U : SSet).obj n) :
    (TopCat.toSSet.map
      (topologicalSubsetInclusion X
        (U (coverSmallSimplexPreimageIndex X U x)))).app n
        (coverSmallSimplexPreimage X U x) = x.1 :=
  ((mem_coverSmallSingularSubcomplex_iff_exists_preimage X U x.1).mp
    x.2).choose_spec.choose_spec

/-- Affine subdivision of a cover-small generator, performed in a cover member and then mapped
back into the cover-small complex. -/
public noncomputable def coverSmallAffineSubdivisionSimplexChain
    (n : ℕ)
    (x : (coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    AddCommGrpCat.of ℤ ⟶
      (CoverSmallIntegralSingularChainComplex X U).X n :=
  affineSubdivisionSingularSimplexChain
      (TopCat.of (U (coverSmallSimplexPreimageIndex X U x))) n
      (coverSmallSimplexPreimage X U x) ≫
    (coverMemberToSmallIntegralSingularChains X U
      (coverSmallSimplexPreimageIndex X U x)).f n

/-- The degreewise affine subdivision endomorphism of cover-small chains. -/
public noncomputable def coverSmallAffineSubdivisionComponent (n : ℕ) :
    (CoverSmallIntegralSingularChainComplex X U).X n ⟶
      (CoverSmallIntegralSingularChainComplex X U).X n :=
  Sigma.desc (coverSmallAffineSubdivisionSimplexChain X U n)

@[reassoc (attr := simp)]
public theorem iota_coverSmallAffineSubdivisionComponent
    (n : ℕ)
    (x : (coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (coverSmallSingularSubcomplex X U : SSet).ιChainComplex x ≫
        coverSmallAffineSubdivisionComponent X U n =
      coverSmallAffineSubdivisionSimplexChain X U n x := by
  apply Sigma.ι_desc

/-- Subdivision of a selected cover-small generator agrees with full subdivision after
inclusion. -/
public theorem coverSmallAffineSubdivisionSimplexChain_comp_inclusion
    (n : ℕ)
    (x : (coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    coverSmallAffineSubdivisionSimplexChain X U n x ≫
        (coverSmallIntegralSingularChainInclusion X U).f n =
      affineSubdivisionSingularSimplexChain X n x.1 := by
  let j := coverSmallSimplexPreimageIndex X U x
  let y := coverSmallSimplexPreimage X U x
  change (affineSubdivisionSingularSimplexChain
      (TopCat.of (U j)) n y ≫
        (SSet.chainComplexMap (coverMemberToSmallSingularSet X U j)
          (AddCommGrpCat.of ℤ)).f n) ≫
      (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f n =
    affineSubdivisionSingularSimplexChain X n x.1
  have hcover := congrArg (fun F ↦ F.f n)
    (coverMemberToSmallIntegralSingularChains_comp_inclusion X U j)
  change (SSet.chainComplexMap (coverMemberToSmallSingularSet X U j)
        (AddCommGrpCat.of ℤ)).f n ≫
      (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f n =
    (SSet.chainComplexMap
      (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))
      (AddCommGrpCat.of ℤ)).f n at hcover
  rw [Category.assoc, hcover]
  rw [← affineSubdivisionSingularSimplexChain_naturality]
  change affineSubdivisionSingularSimplexChain X n
      ((TopCat.toSSet.map (topologicalSubsetInclusion X (U j))).app _ y) =
    affineSubdivisionSingularSimplexChain X n x.1
  rw [show (TopCat.toSSet.map
      (topologicalSubsetInclusion X (U j))).app _ y = x.1 from
    coverSmallSimplexPreimage_spec X U x]

/-- Cover-small affine subdivision agrees with full affine subdivision after inclusion. -/
public theorem coverSmallAffineSubdivisionComponent_comp_inclusion
    (n : ℕ) :
    coverSmallAffineSubdivisionComponent X U n ≫
        (coverSmallIntegralSingularChainInclusion X U).f n =
      (coverSmallIntegralSingularChainInclusion X U).f n ≫
        affineSingularSubdivisionComponent X n := by
  change coverSmallAffineSubdivisionComponent X U n ≫
      (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f n =
    (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
      (AddCommGrpCat.of ℤ)).f n ≫
      affineSingularSubdivisionComponent X n
  apply (coverSmallSingularSubcomplex X U : SSet).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, iota_coverSmallAffineSubdivisionComponent]
  simp only [SSet.ι_chainComplexMap_f_assoc,
    iota_affineSingularSubdivisionComponent]
  exact coverSmallAffineSubdivisionSimplexChain_comp_inclusion X U n x

set_option linter.style.haveILetI false in
/-- The cover-small affine subdivision components commute with the small-chain boundary. -/
public theorem coverSmallAffineSubdivisionComponents_commute
    (n : ℕ) :
    coverSmallAffineSubdivisionComponent X U (n + 1) ≫
        (CoverSmallIntegralSingularChainComplex X U).d (n + 1) n =
      (CoverSmallIntegralSingularChainComplex X U).d (n + 1) n ≫
        coverSmallAffineSubdivisionComponent X U n := by
  let I := SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
    (AddCommGrpCat.of ℤ)
  let A := coverSmallAffineSubdivisionComponent X U
  let B := affineSingularSubdivisionComponent X
  haveI : Mono I := by
    dsimp [I]
    exact coverSmallIntegralSingularChainInclusion_mono X U
  haveI : Mono (I.f n) := by
    change Mono ((HomologicalComplex.eval AddCommGrpCat
      (ComplexShape.down ℕ) n).map I)
    infer_instance
  have hAI (k : ℕ) : A k ≫ I.f k = I.f k ≫ B k := by
    change coverSmallAffineSubdivisionComponent X U k ≫
        (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
          (AddCommGrpCat.of ℤ)).f k =
      (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f k ≫
        affineSingularSubdivisionComponent X k
    exact coverSmallAffineSubdivisionComponent_comp_inclusion X U k
  apply (cancel_mono (I.f n)).mp
  calc
    (A (n + 1) ≫
        (CoverSmallIntegralSingularChainComplex X U).d (n + 1) n) ≫ I.f n =
      A (n + 1) ≫
        ((CoverSmallIntegralSingularChainComplex X U).d (n + 1) n ≫
          I.f n) := Category.assoc _ _ _
    _ = A (n + 1) ≫
        (I.f (n + 1) ≫
          ((TopCat.toSSet.obj X).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n) := by
      rw [I.comm]
    _ = (A (n + 1) ≫ I.f (n + 1)) ≫
        ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n :=
      (Category.assoc _ _ _).symm
    _ = (I.f (n + 1) ≫ B (n + 1)) ≫
        ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n := by
      rw [hAI]
    _ = I.f (n + 1) ≫
        (B (n + 1) ≫
          ((TopCat.toSSet.obj X).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n) :=
      Category.assoc _ _ _
    _ = I.f (n + 1) ≫
        (((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n ≫ B n) := by
      rw [affineSingularSubdivisionComponents_commute]
    _ = (I.f (n + 1) ≫
        ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n) ≫ B n :=
      (Category.assoc _ _ _).symm
    _ = ((CoverSmallIntegralSingularChainComplex X U).d (n + 1) n ≫
        I.f n) ≫ B n := by rw [I.comm]
    _ = (CoverSmallIntegralSingularChainComplex X U).d (n + 1) n ≫
        (I.f n ≫ B n) := Category.assoc _ _ _
    _ = (CoverSmallIntegralSingularChainComplex X U).d (n + 1) n ≫
        (A n ≫ I.f n) := by
      rw [hAI]
    _ = ((CoverSmallIntegralSingularChainComplex X U).d (n + 1) n ≫ A n) ≫
        I.f n := (Category.assoc _ _ _).symm

/-- Affine barycentric subdivision as an endomorphism of the cover-small chain complex. -/
public noncomputable def coverSmallAffineSubdivisionChainMap :
    CoverSmallIntegralSingularChainComplex X U ⟶
      CoverSmallIntegralSingularChainComplex X U :=
  ChainComplex.ofHom (coverSmallAffineSubdivisionComponent X U)
    (coverSmallAffineSubdivisionComponents_commute X U)

@[simp]
public theorem coverSmallAffineSubdivisionChainMap_f (n : ℕ) :
    (coverSmallAffineSubdivisionChainMap X U).f n =
      coverSmallAffineSubdivisionComponent X U n :=
  rfl

/-- Cover-small subdivision is the restriction of full affine singular subdivision. -/
public theorem coverSmallAffineSubdivisionChainMap_comp_inclusion :
    coverSmallAffineSubdivisionChainMap X U ≫
        coverSmallIntegralSingularChainInclusion X U =
      coverSmallIntegralSingularChainInclusion X U ≫
        affineSingularSubdivisionChainMap X := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact coverSmallAffineSubdivisionComponent_comp_inclusion X U n

end SphereSixComplex
