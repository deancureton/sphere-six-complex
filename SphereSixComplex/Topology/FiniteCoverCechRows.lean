module

public import SphereSixComplex.Topology.FiniteCoverCechDefs
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# Row contractions for the finite-cover Cech resolution

The presentation of cover-small singular simplices by the coproduct of the singular sets of the
cover members is surjective in every simplicial degree.  After choosing a section degree by
degree, Mathlib's augmented-Cech-nerve extra degeneracy contracts the corresponding horizontal
Cech row after applying integral simplicial chains.

The section chosen here depends on the singular degree.  Consequently these row contractions do
not by themselves give a contraction, or a quasi-isomorphism theorem, for the total
Cech--singular bicomplex.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set

namespace SphereSixComplex

section FiniteCoverCechRows

variable {iota X : Type} [TopologicalSpace X]

/-- The cover presentation evaluated at one singular simplicial degree. -/
public noncomputable abbrev finiteCoverPresentationAt
    (U : iota → Set X) (q : SimplexCategoryᵒᵖ) :
    (finiteCoverPresentationSource U).obj q ⟶
      (coverSmallSingularSubcomplex (TopCat.of X) U).obj q :=
  (SSet.evaluation.obj q).map (finiteCoverPresentation U)

/-- Every cover-small simplex has a lift to the coproduct of the cover members. -/
public theorem finiteCoverPresentationAt_surjective
    (U : iota → Set X) (q : SimplexCategoryᵒᵖ) :
    Function.Surjective (finiteCoverPresentationAt U q) := by
  intro x
  obtain ⟨j, y, hy⟩ :=
    (mem_coverSmallSingularSubcomplex_iff_exists_preimage (TopCat.of X) U x.val).mp x.property
  refine ⟨(Sigma.ι (fun i : iota ↦ TopCat.toSSet.obj (TopCat.of (U i))) j).app q y, ?_⟩
  have hι :
      Sigma.ι (fun i : iota ↦ TopCat.toSSet.obj (TopCat.of (U i))) j ≫
          finiteCoverPresentation U =
        coverMemberToSmallSingularSet (TopCat.of X) U j := by
    simp [finiteCoverPresentation]
  have hq := ConcreteCategory.congr_hom (congr_app hι q) y
  apply Subtype.ext
  exact (congrArg (fun z ↦ z.val) hq).trans hy

/-- The evaluated cover presentation, bundled as an arrow in `Type`. -/
public noncomputable abbrev finiteCoverPresentationArrowAt
    (U : iota → Set X) (q : SimplexCategoryᵒᵖ) : Arrow (Type _) :=
  (SSet.evaluation.obj q).mapArrow.obj (finiteCoverPresentationArrow U)

/-- A chosen split-epimorphism structure on the cover presentation in degree `q`. -/
public noncomputable def finiteCoverPresentationSplitEpiAt
    (U : iota → Set X) (q : SimplexCategoryᵒᵖ) :
    SplitEpi (finiteCoverPresentationArrowAt U q).hom :=
  ((isSplitEpi_iff_surjective _).2
    (finiteCoverPresentationAt_surjective U q)).exists_splitEpi.some

/-- The degreewise split cover presentation gives an extra degeneracy on its augmented Cech
nerve. -/
public noncomputable def finiteCoverCechExtraDegeneracyAt
    (U : iota → Set X) (q : SimplexCategoryᵒᵖ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (finiteCoverPresentationArrowAt U q).augmentedCechNerve :=
  Arrow.AugmentedCechNerve.extraDegeneracy _
    (finiteCoverPresentationSplitEpiAt U q)

/-- The augmented horizontal Cech row with the free integral abelian group on each set of
simplices. -/
public noncomputable abbrev finiteCoverIntegralAugmentedCechRow
    (U : iota → Set X) (q : SimplexCategoryᵒᵖ) :
    SimplicialObject.Augmented AddCommGrpCat :=
  ((SimplicialObject.Augmented.whiskering (Type _) AddCommGrpCat).obj
    (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
      (finiteCoverPresentationArrowAt U q).augmentedCechNerve

/-- The extra degeneracy on the degree-`q` Cech nerve after applying free integral abelian
groups. -/
public noncomputable def finiteCoverIntegralCechExtraDegeneracyAt
    (U : iota → Set X) (q : SimplexCategoryᵒᵖ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (finiteCoverIntegralAugmentedCechRow U q) :=
  (finiteCoverCechExtraDegeneracyAt U q).map
    (sigmaConst.obj (AddCommGrpCat.of ℤ))

/-- The horizontal Cech row in each fixed singular degree is chain-homotopy equivalent to its
augmentation.  This is a rowwise statement; it does not assert compatibility of the chosen
homotopies with the vertical singular differential. -/
public noncomputable def finiteCoverCechRowHomotopyEquiv
    (U : iota → Set X) (q : SimplexCategoryᵒᵖ) :
    HomotopyEquiv
      (AlgebraicTopology.AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj (finiteCoverIntegralAugmentedCechRow U q)))
      ((ChainComplex.single₀ AddCommGrpCat).obj
        (SimplicialObject.Augmented.point.obj (finiteCoverIntegralAugmentedCechRow U q))) :=
  (finiteCoverIntegralCechExtraDegeneracyAt U q).homotopyEquiv

end FiniteCoverCechRows

end SphereSixComplex
