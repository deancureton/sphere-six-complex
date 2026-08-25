module

public import SphereSixComplex.Topology.BoundarySevenCechOrderedSource
public import SphereSixComplex.Topology.BoundarySevenCechOrderedTarget
public import SphereSixComplex.Topology.BoundarySevenCechOrderedLocalComparison
public import SphereSixComplex.Topology.BoundarySevenCechComparisonAssemblyProof
public import SphereSixComplex.Topology.BoundarySevenDegreeTransportProof
public import SphereSixComplex.Topology.DiskSevenRelativeHomologyLowAcyclic
public import SphereSixComplex.Topology.DiskSevenRelativeHomologyModTwo

/-!
# The boundary-seven Cech total comparison

The object in every outer Cech degree is a coproduct over proper ordered tuples.  On each
summand, the canonical map is the comparison from the common simplicial face to singular
simplices in the corresponding face-neighbourhood intersection.  Those local maps are
quasi-isomorphisms, so finite-coproduct assembly and first-quadrant column totalization prove
that the actual map of Cech totals is a quasi-isomorphism.  The strict augmentation square then
gives the canonical integral simplicial-to-singular comparison for `∂Δ[7]`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

set_option backward.isDefEq.respectTransparency false in
/-- The map of augmented Cech nerves commutes with every projection to a selected presentation
leg. -/
@[reassoc]
public theorem boundarySevenFaceAugmentedCechNerveMap_comp_projection
    (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    boundarySevenFaceAugmentedCechNerveMap.left.app n ≫
        boundarySevenTargetCechProjection n i =
      boundarySevenSourceCechProjection n i ≫
        boundarySevenFacePresentationSourceMap := by
  change WidePullback.lift _ _ _ ≫ WidePullback.π _ i = _
  rw [WidePullback.lift_π]
  rfl

/-- The two independently constructed common-face inclusions into the simplicial boundary are
equal. -/
public theorem boundarySevenProperCechTupleFaceToBoundarySSetMap_eq_source
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    boundarySevenProperCechTupleFaceToBoundarySSetMap a =
      boundarySevenOrderedSourceCommonFaceToBoundary a := by
  apply (cancel_mono (SSet.boundary 7).ι).1
  rw [boundarySevenOrderedSourceCommonFaceToBoundary_comp_inclusion]
  simp [boundarySevenProperCechTupleFaceToBoundarySSetMap]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- On realized spaces, passing from a common face through a selected facet is the same as
passing through its full ordered intersection. -/
public theorem boundarySevenOrderedCommonFace_local_topologicalCompatibility
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    SSet.toTop.map (boundarySevenOrderedSourceCommonFaceToFacet a i) ≫
        boundarySevenFaceToComparisonFaceNeighborhood (a.1 i) =
      TopCat.ofHom (boundarySevenProperCechTupleFaceToIntersection a) ≫
        boundarySevenTargetIntersectionToMember a i := by
  letI : Mono
      (topologicalSubsetInclusion
        (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
        (boundarySevenComparisonFaceNeighborhood (a.1 i))) :=
    (TopCat.mono_iff_injective _).mpr (fun _ _ h ↦ Subtype.ext h)
  apply (cancel_mono
    (topologicalSubsetInclusion
      (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
      (boundarySevenComparisonFaceNeighborhood (a.1 i)))).1
  rw [Category.assoc,
    boundarySevenFaceToComparisonFaceNeighborhood_comp_inclusion]
  rw [Category.assoc,
    boundarySevenTargetIntersectionToMember_comp_inclusion]
  rw [boundarySevenProperCechTupleFaceToIntersection_comp_subsetInclusion]
  rw [← SSet.toTop.map_comp,
    boundarySevenOrderedSourceCommonFaceToFacet_comp_boundary]
  rw [boundarySevenProperCechTupleFaceToBoundarySSetMap_eq_source]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Simplicially, the local tuple comparison commutes with every selected facet leg. -/
public theorem boundarySevenProperCechTupleLocalComparison_comp_member
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    boundarySevenOrderedSourceCommonFaceToFacet a i ≫
        boundarySevenFaceNeighborhoodLocalComparisonSSetMap (a.1 i) =
      boundarySevenProperCechTupleLocalComparisonSSetMap a ≫
        TopCat.toSSet.map (boundarySevenTargetIntersectionToMember a i) := by
  rw [boundarySevenFaceNeighborhoodLocalComparisonSSetMap,
    boundarySevenProperCechTupleLocalComparisonSSetMap]
  change (((𝟭 SSet).map
      (boundarySevenOrderedSourceCommonFaceToFacet a i) ≫
        sSetTopAdj.unit.app (Δ[6] : SSet.{0})) ≫
      TopCat.toSSet.map
        (boundarySevenFaceToComparisonFaceNeighborhood (a.1 i))) = _
  rw [sSetTopAdj.unit.naturality]
  change (sSetTopAdj.unit.app
      (SSet.stdSimplex.face a.1.supportᶜ : SSet.{0}) ≫
    TopCat.toSSet.map
      (SSet.toTop.map (boundarySevenOrderedSourceCommonFaceToFacet a i)) ≫
    TopCat.toSSet.map
      (boundarySevenFaceToComparisonFaceNeighborhood (a.1 i))) =
    sSetTopAdj.unit.app
      (SSet.stdSimplex.face a.1.supportᶜ : SSet.{0}) ≫
    TopCat.toSSet.map
      (TopCat.ofHom (boundarySevenProperCechTupleFaceToIntersection a)) ≫
    TopCat.toSSet.map (boundarySevenTargetIntersectionToMember a i)
  simp only [← Functor.map_comp]
  congr 1
  exact TopCat.toSSet.congr_map
    (boundarySevenOrderedCommonFace_local_topologicalCompatibility a i)

set_option backward.isDefEq.respectTransparency false in
/-- The compatibility square on one ordered-tuple summand of a fixed outer Cech degree. -/
public theorem boundarySevenOrderedCechComparison_summand
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    boundarySevenOrderedSourceCechSummand a ≫
        boundarySevenFaceAugmentedCechNerveMap.left.app n =
      boundarySevenProperCechTupleLocalComparisonSSetMap a ≫
        boundarySevenTargetIntersectionToCechSummand a := by
  have htargetProj (i : Fin (n.unop.len + 1)) :
      boundarySevenTargetIntersectionToCechSummand a ≫
          boundarySevenTargetCechProjection n i =
        boundarySevenTargetIntersectionToPresentationLeg a i := by
    change WidePullback.lift _ _ _ ≫ WidePullback.π _ i = _
    rw [WidePullback.lift_π]
  have hproj (i : Fin (n.unop.len + 1)) :
      (boundarySevenOrderedSourceCechSummand a ≫
          boundarySevenFaceAugmentedCechNerveMap.left.app n) ≫
          boundarySevenTargetCechProjection n i =
        (boundarySevenProperCechTupleLocalComparisonSSetMap a ≫
          boundarySevenTargetIntersectionToCechSummand a) ≫
          boundarySevenTargetCechProjection n i := by
    rw [Category.assoc,
      boundarySevenFaceAugmentedCechNerveMap_comp_projection]
    rw [← Category.assoc,
      boundarySevenOrderedSourceCechSummand_comp_projection]
    rw [Category.assoc, htargetProj]
    rw [boundarySevenOrderedSourcePresentationLeg,
      boundarySevenTargetIntersectionToPresentationLeg]
    simp only [Category.assoc]
    rw [boundarySevenFacePresentationSourceMap_iota]
    exact congrArg
      (fun k ↦ k ≫ Sigma.ι
        (fun j : Fin 8 ↦ TopCat.toSSet.obj
          (TopCat.of (boundarySevenComparisonFaceNeighborhood j))) (a.1 i))
      (boundarySevenProperCechTupleLocalComparison_comp_member a i)
  apply WidePullback.hom_ext
  · exact hproj
  · change _ ≫ WidePullback.base
        (fun _ : Fin (n.unop.len + 1) ↦
          boundarySevenFaceNeighborhoodPresentation) =
      _ ≫ WidePullback.base
        (fun _ : Fin (n.unop.len + 1) ↦
          boundarySevenFaceNeighborhoodPresentation)
    rw [show WidePullback.base
        (fun _ : Fin (n.unop.len + 1) ↦
          boundarySevenFaceNeighborhoodPresentation) =
        boundarySevenTargetCechProjection n 0 ≫
          boundarySevenFaceNeighborhoodPresentation by
      exact (WidePullback.π_arrow
        (fun _ : Fin (n.unop.len + 1) ↦
          boundarySevenFaceNeighborhoodPresentation) 0).symm]
    simp only [← Category.assoc]
    rw [hproj 0]

set_option backward.isDefEq.respectTransparency false in
/-- In a fixed outer degree, conjugating the actual Cech map by the two objectwise
decompositions gives the coproduct of the tuplewise local comparisons. -/
public theorem boundarySevenOrderedCechComparison_component
    (n : SimplexCategoryᵒᵖ) :
    (boundarySevenOrderedSourceCechIso n).hom ≫
        boundarySevenFaceAugmentedCechNerveMap.left.app n =
      CategoryTheory.Limits.Sigma.map
          (fun a : BoundarySevenProperCechTuple n ↦
            boundarySevenProperCechTupleLocalComparisonSSetMap a) ≫
        (boundarySevenOrderedTargetCechIso n).hom := by
  apply Sigma.hom_ext
  intro a
  simp only [← Category.assoc]
  rw [boundarySevenOrderedSourceCechIso_hom,
    boundarySevenOrderedSourceToCech, Sigma.ι_desc]
  change _ =
    (Sigma.ι
      (fun a : BoundarySevenProperCechTuple n ↦
        (SSet.stdSimplex.face a.1.supportᶜ : SSet.{0})) a ≫
      CategoryTheory.Limits.Sigma.map
        (fun a : BoundarySevenProperCechTuple n ↦
          boundarySevenProperCechTupleLocalComparisonSSetMap a)) ≫ _
  rw [CategoryTheory.Limits.Sigma.ι_map]
  rw [Category.assoc,
    boundarySevenOrderedTargetCechIso_hom_summand]
  exact boundarySevenOrderedCechComparison_summand a

/-- Every outer column of the actual boundary-seven Cech bicomplex map is a
quasi-isomorphism. -/
public theorem boundarySevenFaceCechBicomplexMap_column_quasiIso (p : ℕ) :
    QuasiIso (boundarySevenFaceCechBicomplexMap.f p) := by
  change QuasiIso (SSet.chainComplexMap
    (boundarySevenFaceAugmentedCechNerveMap.left.app
      (Opposite.op (SimplexCategory.mk p))) (AddCommGrpCat.of ℤ))
  apply quasiIso_sSetIntegralChains_of_finiteCoproduct_conjugation
    (fun a : BoundarySevenProperCechTuple
        (Opposite.op (SimplexCategory.mk p)) ↦
      boundarySevenOrderedSourceCommonFace a)
    (fun a : BoundarySevenProperCechTuple
        (Opposite.op (SimplexCategory.mk p)) ↦
      TopCat.toSSet.obj (TopCat.of
        (boundarySevenFaceNeighborhoodIntersection a.1.support)))
    (fun a ↦ boundarySevenProperCechTupleLocalComparisonSSetMap a)
    (boundarySevenOrderedSourceCechIso
      (Opposite.op (SimplexCategory.mk p)))
    (boundarySevenOrderedTargetCechIso
      (Opposite.op (SimplexCategory.mk p)))
    (boundarySevenFaceAugmentedCechNerveMap.left.app
      (Opposite.op (SimplexCategory.mk p)))
  · exact boundarySevenOrderedCechComparison_component
      (Opposite.op (SimplexCategory.mk p))
  · intro a
    exact boundarySevenProperCechTupleLocalIntegralComparison_quasiIso a

/-- The canonical map between the two direct-sum Cech totals is a quasi-isomorphism in all
degrees. -/
public theorem boundarySevenFaceCechTotalMap_quasiIso :
    QuasiIso boundarySevenFaceCechTotalMap :=
  boundarySevenFaceCechTotalMap_quasiIso_of_columns
    boundarySevenFaceCechBicomplexMap_column_quasiIso

/-- The canonical integral simplicial-to-singular comparison for the boundary of the
seven-simplex. -/
public theorem boundarySeven_integralComparison_proof :
    SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ) :=
  boundarySeven_integralComparison_of_faceCechTotalMap_quasiIso
    boundarySevenFaceCechTotalMap_quasiIso

/-- The completed canonical boundary comparison supplies the full degree theory of the standard
six-sphere. -/
public theorem sixSphereDegreeTheory_proof :
    Nonempty OrientedMarkedSmoothHomotopySixSphere.SixSphereDegreeTheory :=
  sixSphereDegreeTheory_of_boundarySevenComparison
    boundarySeven_integralComparison_proof

/-- The low-degree integral comparison used by the disk-cover and Kervaire branches. -/
public theorem boundarySevenLowIntegralComparison_proof :
    BoundarySevenLowIntegralComparison :=
  boundarySevenLowIntegralComparison_of_quasiIso
    boundarySeven_integralComparison_proof

/-- The four local disk-cover relative vanishings follow from the now-unconditional boundary
comparison. -/
public theorem diskSevenCoverLocalRelativeLowAcyclic_proof :
    DiskSevenCoverLocalRelativeLowAcyclic :=
  diskSevenCoverLocalRelativeLowAcyclic_of_boundaryLowComparison
    boundarySevenLowIntegralComparison_proof

/-- Hence the explicit cover-small relative disk complex is acyclic in degrees three and four. -/
public theorem diskSevenCoverSmallRelativeLowAcyclic_proof :
    DiskSevenCoverSmallRelativeLowAcyclic :=
  diskSevenCoverSmallRelativeLowAcyclic_of_localAcyclic
    diskSevenCoverLocalRelativeLowAcyclic_proof

/-- The required middle mod-two homology of the standard six-sphere vanishes. -/
public theorem sixSphere_modTwoHomology_three_isZero_proof :
    IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of SixSphere)) :=
  sixSphere_modTwoHomology_three_isZero_of_coverSmallRelative
    diskSevenCoverSmallRelativeLowAcyclic_proof

/-- The same mod-two vanishing holds for every marked smooth homotopy six-sphere. -/
public theorem markedHomotopySixSphere_modTwoHomology_three_isZero_proof
    (S : OrientedMarkedSmoothHomotopySixSphere) :
    IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of S.carrier)) :=
  markedHomotopySixSphere_modTwoHomology_three_isZero_of_coverSmallRelative
    diskSevenCoverSmallRelativeLowAcyclic_proof S

end SphereSixComplex
