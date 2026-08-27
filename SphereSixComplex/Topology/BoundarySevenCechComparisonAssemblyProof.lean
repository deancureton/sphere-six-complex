module

public import SphereSixComplex.Topology.BoundarySevenCechRowwiseGlobalizationProof

/-!
# Direct assembly of the boundary-seven Cech comparison

The strict source split used by the earlier low-degree package is not needed for the canonical
simplicial-to-singular comparison.  The canonical map of Cech totals commutes strictly with the
two augmentations.  Since both augmentations are already quasi-isomorphisms, two-out-of-three
reduces the whole comparison theorem to the single assertion that the map of Cech totals is a
quasi-isomorphism.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- A map of simplicial sets which, after conjugating by coproduct isomorphisms, is a finite
coproduct of integral chain quasi-isomorphisms is itself an integral chain quasi-isomorphism. -/
public theorem quasiIso_sSetIntegralChains_of_finiteCoproduct_conjugation
    {I : Type} [Finite I]
    (K L : I → SSet.{0}) (f : ∀ i, K i ⟶ L i)
    {X Y : SSet.{0}} (sourceIso : sigmaObj K ≅ X) (targetIso : sigmaObj L ≅ Y)
    (g : X ⟶ Y)
    (h : sourceIso.hom ≫ g = CategoryTheory.Limits.Sigma.map f ≫ targetIso.hom)
    (hf : ∀ i, QuasiIso (SSet.chainComplexMap (f i) (AddCommGrpCat.of ℤ))) :
    QuasiIso (SSet.chainComplexMap g (AddCommGrpCat.of ℤ)) := by
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  letI : PreservesColimitsOfShape (Discrete I) F := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    change PreservesColimitsOfShape (Discrete I)
      ((evaluation SimplexCategoryᵒᵖ Type).obj
        (Opposite.op (SimplexCategory.mk n)) ⋙
          sigmaConst.obj (AddCommGrpCat.of ℤ))
    infer_instance
  haveI hsigma : QuasiIso (F.map (CategoryTheory.Limits.Sigma.map f)) :=
    quasiIso_map_finite_coproduct F K L f hf
  haveI hsource : QuasiIso (F.map sourceIso.hom) := by infer_instance
  haveI htarget : QuasiIso (F.map targetIso.hom) := by infer_instance
  have hmap : F.map sourceIso.hom ≫ F.map g =
      F.map (CategoryTheory.Limits.Sigma.map f) ≫ F.map targetIso.hom := by
    rw [← F.map_comp, h, F.map_comp]
  haveI : QuasiIso (F.map sourceIso.hom ≫ F.map g) := by
    rw [hmap]
    infer_instance
  exact quasiIso_of_comp_left (F.map sourceIso.hom) (F.map g)

/-- Columnwise quasi-isomorphisms of the actual boundary-seven Cech bicomplex map imply the
quasi-isomorphism of its direct-sum total. -/
public theorem boundarySevenFaceCechTotalMap_quasiIso_of_columns
    (hcolumn : ∀ p : ℕ, QuasiIso (boundarySevenFaceCechBicomplexMap.f p)) :
    QuasiIso boundarySevenFaceCechTotalMap := by
  apply firstQuadrantTotal_quasiIso_of_singleColumns
    boundarySevenFaceCechBicomplexMap
  intro p
  exact firstQuadrantSingleColumnTotal_quasiIso
    boundarySevenFaceCechBicomplexMap p (hcolumn p)

/-- The canonical integral comparison follows directly from the quasi-isomorphism of the two
Cech totals.  No chain-level section of the source augmentation is required. -/
public theorem boundarySeven_integralComparison_of_faceCechTotalMap_quasiIso
    (hcech : QuasiIso boundarySevenFaceCechTotalMap) :
    SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ) := by
  let P := boundarySevenSimplicialFaceCechTotalAugmentation
  let F := boundarySevenFaceCechTotalMap
  let A := boundarySevenFaceNeighborhoodCechTotalAugmentation
  let φ := simplicialToCoverSmallSingularChainMap
    (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
    boundarySevenComparisonUnitLandsInFaceNeighborhoods
  letI : QuasiIso P :=
    boundarySevenSimplicialFaceCechTotalAugmentation_quasiIso
      boundarySevenCechRowwiseGlobalization.totalization
      boundarySevenCechRowwiseGlobalization.rowIdentifications
  letI : QuasiIso F := hcech
  letI : QuasiIso A :=
    boundarySevenFaceNeighborhoodCechTotalAugmentation_quasiIso
      boundarySevenCechRowwiseGlobalization.totalization
      boundarySevenCechRowwiseGlobalization.rowIdentifications
  haveI : QuasiIso (P ≫ φ) := by
    rw [← boundarySevenFaceCechTotalMap_comp_augmentation]
    infer_instance
  have hφ : QuasiIso φ := quasiIso_of_comp_left P φ
  exact boundarySeven_integralComparison_of_faceNeighborhoodLift
    boundarySevenComparisonMapLandsInAffineBoundary hφ

end SphereSixComplex
