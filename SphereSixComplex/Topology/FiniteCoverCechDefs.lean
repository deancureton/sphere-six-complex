module

public import SphereSixComplex.Topology.SectionSevenCoherentRealizationReduction
public import SphereSixComplex.Topology.FirstQuadrantSingleColumnTotal
public import Mathlib.AlgebraicTopology.CechNerve

/-!
# The finite-cover Cech--singular bicomplex

This file contains the objects and augmentation used by the finite-cover Leray--Cech
comparison.  Its proof is separated from these definitions so that the degreewise row
contractions can use them without creating an import cycle.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set

namespace SphereSixComplex

section FiniteCoverCech

variable {iota X : Type} [TopologicalSpace X]

/-- The intersection selected by a finite set of cover indices.  The empty intersection is the
whole space, as usual. -/
public def finiteCoverIntersection (U : iota → Set X) (s : Finset iota) : Set X :=
  ⋂ i ∈ s, U i

omit [TopologicalSpace X] in
@[simp]
public theorem mem_finiteCoverIntersection_iff (U : iota → Set X) (s : Finset iota)
    (x : X) :
    x ∈ finiteCoverIntersection U s ↔ ∀ i ∈ s, x ∈ U i := by
  simp [finiteCoverIntersection]

/-- Finite intersections stay open; no assertion about their homology is made. -/
public theorem isOpen_finiteCoverIntersection (U : iota → Set X)
    (hOpen : ∀ i, IsOpen (U i)) (s : Finset iota) :
    IsOpen (finiteCoverIntersection U s) := by
  apply isOpen_biInter_finset
  intro i _
  exact hOpen i

/-- The coproduct of the singular simplicial sets of all cover members. -/
public noncomputable abbrev finiteCoverPresentationSource (U : iota → Set X) : SSet :=
  ∐ fun i : iota ↦ TopCat.toSSet.obj (TopCat.of (U i))

/-- The canonical cover presentation onto the simplicial set of cover-small simplices. -/
public noncomputable def finiteCoverPresentation (U : iota → Set X) :
    finiteCoverPresentationSource U ⟶ coverSmallSingularSubcomplex (TopCat.of X) U :=
  Sigma.desc fun i ↦ coverMemberToSmallSingularSet (TopCat.of X) U i

/-- The cover presentation, bundled as an arrow so that Mathlib's canonical Cech nerve applies. -/
public noncomputable def finiteCoverPresentationArrow (U : iota → Set X) : Arrow SSet :=
  Arrow.mk (finiteCoverPresentation U)

/-- The augmented Cech nerve of the cover presentation. -/
public noncomputable def finiteCoverAugmentedCechNerve (U : iota → Set X) :
    SimplicialObject.Augmented SSet :=
  (finiteCoverPresentationArrow U).augmentedCechNerve

/-- The Cech nerve of the cover presentation.  Its degree-`p` object records `(p+1)` compatible
lifts of a small singular simplex, hence all ordered `(p+1)`-fold cover intersections, including
repetitions. -/
public noncomputable def finiteCoverCechNerve (U : iota → Set X) : SimplicialObject SSet :=
  SimplicialObject.Augmented.drop.obj (finiteCoverAugmentedCechNerve U)

/-- Apply integral simplicial chains to the augmented cover Cech nerve. -/
public noncomputable def finiteCoverAugmentedCechChains (U : iota → Set X) :
    SimplicialObject.Augmented (ChainComplex AddCommGrpCat ℕ) :=
  ((SimplicialObject.Augmented.whiskering SSet
    (ChainComplex AddCommGrpCat ℕ)).obj
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ))).obj
        (finiteCoverAugmentedCechNerve U)

/-- Apply integral simplicial chains in the singular direction to the cover Cech nerve. -/
public noncomputable def finiteCoverCechChainSimplicialObject (U : iota → Set X) :
    SimplicialObject (ChainComplex AddCommGrpCat ℕ) :=
  SimplicialObject.Augmented.drop.obj (finiteCoverAugmentedCechChains U)

/-- The Cech--singular bicomplex: the outer differential is the alternating Cech boundary,
while the inner differential is the ordinary singular boundary on each iterated intersection. -/
public noncomputable def finiteCoverLerayCechBicomplex (U : iota → Set X) :
    HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (alternatingFaceMapComplex (ChainComplex AddCommGrpCat ℕ)).obj
    (finiteCoverCechChainSimplicialObject U)

/-- The direct-sum total complex of the Cech--singular bicomplex. -/
public noncomputable def finiteCoverLerayCechTotal (U : iota → Set X) :
    ChainComplex AddCommGrpCat ℕ :=
  (finiteCoverLerayCechBicomplex U).total (ComplexShape.down ℕ)

/-- The outer Cech augmentation, before totalization. -/
public noncomputable def finiteCoverLerayCechOuterAugmentation (U : iota → Set X) :
    finiteCoverLerayCechBicomplex U ⟶
      firstQuadrantSingleZeroBicomplex
        (CoverSmallIntegralSingularChainComplex (TopCat.of X) U) :=
  AlternatingFaceMapComplex.ε.app (finiteCoverAugmentedCechChains U)

/-- Totalize the outer Cech augmentation and identify the total of its zero column with
cover-small singular chains. -/
public noncomputable def finiteCoverLerayCechTotalAugmentation (U : iota → Set X) :
    finiteCoverLerayCechTotal U ⟶
      CoverSmallIntegralSingularChainComplex (TopCat.of X) U :=
  HomologicalComplex₂.total.map (finiteCoverLerayCechOuterAugmentation U)
      (ComplexShape.down ℕ) ≫
    firstQuadrantTotalToSingleZero
      (CoverSmallIntegralSingularChainComplex (TopCat.of X) U)

/-- The output of the augmentation theorem for the cover Cech resolution. -/
public structure FiniteOpenCoverLerayCechComparison (U : iota → Set X) where
  /-- Augmentation from the canonical total Cech--singular complex to cover-small chains. -/
  augmentation : finiteCoverLerayCechTotal U ⟶
    CoverSmallIntegralSingularChainComplex (TopCat.of X) U
  /-- The augmentation is a quasi-isomorphism. -/
  quasiIso : QuasiIso augmentation

end FiniteCoverCech

end SphereSixComplex
