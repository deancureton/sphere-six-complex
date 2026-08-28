module

public import SphereSixComplex.Topology.FiniteCoverCechRows
public import SphereSixComplex.Topology.FirstQuadrantRowwiseTotalizationProof
public import SphereSixComplex.Topology.BoundarySevenCechRowIdentificationsProof

/-!
# Leray--Cech comparison for a finite open cover

The cover Cech nerve retains the singular chains of every iterated intersection.  Its
augmentation is a quasi-isomorphism because every horizontal row is the Cech resolution of a
surjection of sets and hence has an extra degeneracy.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set Simplicial

namespace SphereSixComplex

section FiniteCoverCech

variable {iota X : Type} [TopologicalSpace X]

/-- Integral chains carry the canonical comparison between evaluation of the simplicial-set
Cech nerve and the Cech nerve of the evaluated presentation. -/
public noncomputable def finiteCoverIntegralCechAugmentedRowIso
    (U : iota → Set X) (q : ℕ) :
    ((SimplicialObject.Augmented.whiskering (Type 0) AddCommGrpCat).obj
      (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
        (((SimplicialObject.Augmented.whiskering SSet (Type 0)).obj
          ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
            (Opposite.op (SimplexCategory.mk q)))).obj
              (finiteCoverAugmentedCechNerve U)) ≅
      finiteCoverIntegralAugmentedCechRow U
        (Opposite.op (SimplexCategory.mk q)) :=
  Functor.mapIso _
    (cechPresentationAugmentedEvaluationIso (finiteCoverPresentationArrow U) q)

/-- The actual horizontal row of the Cech bicomplex augmentation is canonically the evaluated
row contracted by `finiteCoverCechRowHomotopyEquiv`. -/
public noncomputable def finiteCoverCechRowArrowIso
    (U : iota → Set X) (q : ℕ) :
    Arrow.mk (firstQuadrantHorizontalRowMap
        (finiteCoverLerayCechOuterAugmentation U) q) ≅
      Arrow.mk (AlternatingFaceMapComplex.ε.app
        (finiteCoverIntegralAugmentedCechRow U
          (Opposite.op (SimplexCategory.mk q)))) := by
  let e := finiteCoverIntegralCechAugmentedRowIso U q
  let R := ((SimplicialObject.Augmented.whiskering (Type 0) AddCommGrpCat).obj
    (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
      (((SimplicialObject.Augmented.whiskering SSet (Type 0)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
          (Opposite.op (SimplexCategory.mk q)))).obj
            (finiteCoverAugmentedCechNerve U))
  let F := HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) q
  let Y := SimplicialObject.Augmented.drop.obj (finiteCoverAugmentedCechChains U)
  let l₀ : firstQuadrantHorizontalRow
      (finiteCoverLerayCechBicomplex U) q ≅
      AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj R) :=
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).app Y
  let r₀ : firstQuadrantHorizontalRow
      (firstQuadrantSingleZeroBicomplex
        (CoverSmallIntegralSingularChainComplex (TopCat.of X) U)) q ≅
      (ChainComplex.single₀ AddCommGrpCat).obj
        (SimplicialObject.Augmented.point.obj R) :=
    (HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.down ℕ) 0).app
        (CoverSmallIntegralSingularChainComplex (TopCat.of X) U)
  let e₀ : Arrow.mk (firstQuadrantHorizontalRowMap
      (finiteCoverLerayCechOuterAugmentation U) q) ≅
      Arrow.mk (AlternatingFaceMapComplex.ε.app R) :=
    Arrow.isoMk' _ _ l₀ r₀ (by
      ext n x
      rcases n with _ | n
      · simp [l₀, r₀, R, F, firstQuadrantHorizontalRowMap,
          firstQuadrantHorizontalRow, finiteCoverLerayCechOuterAugmentation,
          finiteCoverLerayCechBicomplex, finiteCoverCechChainSimplicialObject,
          finiteCoverAugmentedCechChains, SSet.chainComplexFunctor]
        erw [HomologicalComplex.comp_f]
      · rw [HomologicalComplex.comp_f,
          AlternatingFaceMapComplex.ε_app_f_succ, comp_zero]
        rfl)
  let e₁ := Arrow.isoMk'
    (AlternatingFaceMapComplex.ε.app R)
    (AlternatingFaceMapComplex.ε.app
      (finiteCoverIntegralAugmentedCechRow U
        (Opposite.op (SimplexCategory.mk q))))
    ((alternatingFaceMapComplex AddCommGrpCat).mapIso
      (SimplicialObject.Augmented.drop.mapIso e))
    ((ChainComplex.single₀ AddCommGrpCat).mapIso
      (SimplicialObject.Augmented.point.mapIso e))
    (by
      exact AlternatingFaceMapComplex.ε.naturality e.hom)
  exact e₀ ≪≫ e₁

/-- Every evaluated horizontal Cech augmentation is a quasi-isomorphism. -/
public theorem finiteCoverIntegralCechRowAugmentation_quasiIso
    (U : iota → Set X) (q : SimplexCategoryᵒᵖ) :
    QuasiIso (AlternatingFaceMapComplex.ε.app
      (finiteCoverIntegralAugmentedCechRow U q)) :=
  (finiteCoverCechRowHomotopyEquiv U q).quasiIso_hom

/-- The Leray--Cech augmentation for a finite open cover.  In fact the proof only uses that the
target consists of cover-small simplices: its presentation by cover members is degreewise
surjective for every family of subsets. -/
public noncomputable def establishedFiniteOpenCoverLerayCechComparison
    [Fintype iota] (U : iota → Set X)
    (_hOpen : ∀ i, IsOpen (U i)) (_hCover : ⋃ i, U i = Set.univ) :
    FiniteOpenCoverLerayCechComparison U := by
  let T := HomologicalComplex₂.total.map
    (finiteCoverLerayCechOuterAugmentation U) (ComplexShape.down ℕ)
  have hT : QuasiIso T := by
    apply firstQuadrantTotal_quasiIso_of_rows
      (finiteCoverLerayCechOuterAugmentation U)
    intro q
    let _ : QuasiIso (AlternatingFaceMapComplex.ε.app
        (finiteCoverIntegralAugmentedCechRow U
          (Opposite.op (SimplexCategory.mk q)))) :=
      finiteCoverIntegralCechRowAugmentation_quasiIso U _
    exact quasiIso_of_arrow_mk_iso
      (AlternatingFaceMapComplex.ε.app
        (finiteCoverIntegralAugmentedCechRow U
          (Opposite.op (SimplexCategory.mk q))))
      (firstQuadrantHorizontalRowMap
        (finiteCoverLerayCechOuterAugmentation U) q)
      (finiteCoverCechRowArrowIso U q).symm
  let P := firstQuadrantTotalToSingleZero
    (CoverSmallIntegralSingularChainComplex (TopCat.of X) U)
  have hP : QuasiIso P := by
    let _ : IsIso P :=
      (firstQuadrantSingleZeroTotalIso
        (CoverSmallIntegralSingularChainComplex (TopCat.of X) U)).isIso_hom
    infer_instance
  refine ⟨finiteCoverLerayCechTotalAugmentation U, ?_⟩
  change QuasiIso (T ≫ P)
  exact quasiIso_comp T P

end FiniteCoverCech

section SectionSevenReduction

variable {X : Type} [TopologicalSpace X] {C : FourPieceOpenCover X}

/-- A strong chain-level comparison with the finite algebraic model.  This is sufficient for the
general cover theorem, but it is not asserted by Section 7 of the paper: the paper computes a
Leray spectral sequence rather than a contraction of the four-piece Cech total. -/
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
