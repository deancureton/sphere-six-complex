module

public import SphereSixComplex.Topology.SectionSevenCoherentRealizationReduction
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.AlgebraicTopology.CechNerve

/-!
# Leray--Čech comparison for a finite open cover

The cover Čech nerve below retains the singular chains of every iterated intersection.  No
acyclicity or contractibility hypothesis is imposed on an intersection.  The only external input
is the standard augmentation theorem comparing the total Čech--singular bicomplex with chains
small for the cover.
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

/-- The cover presentation, bundled as an arrow so that Mathlib's canonical Čech nerve applies. -/
public noncomputable def finiteCoverPresentationArrow (U : iota → Set X) : Arrow SSet :=
  Arrow.mk (finiteCoverPresentation U)

/-- The Čech nerve of the cover presentation.  Its degree-`p` object records `(p+1)` compatible
lifts of a small singular simplex, hence all ordered `(p+1)`-fold cover intersections, including
repetitions. -/
public noncomputable def finiteCoverCechNerve (U : iota → Set X) : SimplicialObject SSet :=
  (finiteCoverPresentationArrow U).cechNerve

/-- Apply integral simplicial chains in the singular direction to the cover Čech nerve. -/
public noncomputable def finiteCoverCechChainSimplicialObject (U : iota → Set X) :
    SimplicialObject (ChainComplex AddCommGrpCat ℕ) :=
  ((SimplicialObject.whiskering SSet (ChainComplex AddCommGrpCat ℕ)).obj
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ))).obj
      (finiteCoverCechNerve U)

/-- The Čech--singular bicomplex: the outer differential is the alternating Čech boundary,
while the inner differential is the ordinary singular boundary on each iterated intersection. -/
public noncomputable def finiteCoverLerayCechBicomplex (U : iota → Set X) :
    HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (alternatingFaceMapComplex (ChainComplex AddCommGrpCat ℕ)).obj
    (finiteCoverCechChainSimplicialObject U)

/-- The direct-sum total complex of the Čech--singular bicomplex. -/
public noncomputable def finiteCoverLerayCechTotal (U : iota → Set X) :
    ChainComplex AddCommGrpCat ℕ :=
  (finiteCoverLerayCechBicomplex U).total (ComplexShape.down ℕ)

/-- The output of the classical augmentation theorem for the cover Čech resolution. -/
public structure FiniteOpenCoverLerayCechComparison (U : iota → Set X) where
  /-- Augmentation from the canonical total Čech--singular complex to cover-small chains. -/
  augmentation : finiteCoverLerayCechTotal U ⟶
    CoverSmallIntegralSingularChainComplex (TopCat.of X) U
  /-- The augmentation is a quasi-isomorphism. -/
  quasiIso : QuasiIso augmentation

/-- Standard Leray--Čech augmentation for a finite open cover.  This theorem does not assume
that any nonempty intersection is acyclic: the full singular chain complex of every iterated
intersection occurs in `finiteCoverLerayCechTotal`. -/
public axiom establishedFiniteOpenCoverLerayCechComparison
    [Fintype iota] (U : iota → Set X)
    (hOpen : ∀ i, IsOpen (U i)) (hCover : ⋃ i, U i = Set.univ) :
    FiniteOpenCoverLerayCechComparison U

end FiniteCoverCech

section SectionSevenReduction

variable {X : Type} [TopologicalSpace X] {C : FourPieceOpenCover X}

/-- The remaining Section 7 input after applying the general cover theorem.  Its homotopy
equivalence is precisely where the explicit chain models for the four pieces and their
intersections, together with the displayed alternating and transferred-differential matrices,
must be checked. -/
public structure SectionSevenLerayCechIdentification
    (X : Type) [TopologicalSpace X] (C : FourPieceOpenCover X) where
  identification : HomotopyEquiv (sectionSevenLerayChainModel (-1))
    (finiteCoverLerayCechTotal C.piece)

namespace SectionSevenLerayCechIdentification

/-- Explicit intersection-chain equivalences and matrix compatibility, packaged as the
identification above, imply the paper-specific small-chain comparison. -/
public noncomputable def toFourPieceSmallChainComparison
    (h : SectionSevenLerayCechIdentification X C) :
    SectionSevenFourPieceSmallChainComparison X C := by
  let e := establishedFiniteOpenCoverLerayCechComparison
    C.piece C.isOpen_piece C.covers
  refine
    { comparison := h.identification.hom ≫ e.augmentation
      quasiIso := ?_ }
  let _ : QuasiIso h.identification.hom := by
    rw [quasiIso_iff]
    intro k
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso ((h.identification.toHomologyIso k).hom)
    infer_instance
  let _ : QuasiIso e.augmentation := e.quasiIso
  infer_instance

end SectionSevenLerayCechIdentification

end SectionSevenReduction

end SphereSixComplex
