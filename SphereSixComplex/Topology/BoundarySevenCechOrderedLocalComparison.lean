module

public import SphereSixComplex.Topology.BoundarySevenCechOrderedTuples

/-!
# Local comparison for ordered boundary-seven Cech tuples

For an ordered tuple with proper support, its common simplicial face is representable by the
standard simplex on the complementary vertices.  The order on `Fin 8` makes this
representability canonical.  We use it to compare that common face with singular simplices in
the corresponding intersection of affine face neighbourhoods.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap Simplicial

namespace SphereSixComplex

set_option maxHeartbeats 800000

/-- The dimension of the standard simplex whose vertices are the complement of a proper Cech
tuple's support. -/
public def boundarySevenProperCechTupleFaceDimension
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) : ℕ :=
  a.1.supportᶜ.card - 1

/-- The canonical increasing enumeration of the complementary vertices. -/
public noncomputable def boundarySevenProperCechTupleFaceOrderIso
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    Fin (boundarySevenProperCechTupleFaceDimension a + 1) ≃o
      ↑(a.1.supportᶜ) := by
  apply Finset.orderIsoOfFin
  have hpos : 0 < a.1.supportᶜ.card :=
    Finset.card_pos.mpr a.support_compl_nonempty
  dsimp [boundarySevenProperCechTupleFaceDimension]
  omega

/-- The common face is canonically representable by the standard simplex on the complementary
vertices. -/
public noncomputable def boundarySevenProperCechTupleFaceIso
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    (Δ[boundarySevenProperCechTupleFaceDimension a] : SSet.{0}) ≅
      (SSet.stdSimplex.face a.1.supportᶜ : SSet.{0}) :=
  SSet.stdSimplex.isoOfRepresentableBy
    (SSet.stdSimplex.faceRepresentableBy a.1.supportᶜ
      (boundarySevenProperCechTupleFaceDimension a)
      (boundarySevenProperCechTupleFaceOrderIso a))

/-- The simplex-category arrow which inserts the increasing complementary vertices into the
eight ambient vertices. -/
public noncomputable def boundarySevenProperCechTupleComplementSimplexHom
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    SimplexCategory.mk (boundarySevenProperCechTupleFaceDimension a) ⟶
      SimplexCategory.mk 7 :=
  SimplexCategory.Hom.mk
    { toFun := fun j ↦ (boundarySevenProperCechTupleFaceOrderIso a j).1
      monotone' := fun _ _ h ↦
        (boundarySevenProperCechTupleFaceOrderIso a).monotone h }

/-- The common complementary face includes canonically in the simplicial boundary. -/
public noncomputable def boundarySevenProperCechTupleFaceToBoundarySSetMap
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    (SSet.stdSimplex.face a.1.supportᶜ : SSet.{0}) ⟶
      (∂Δ[7] : SSet.{0}) := by
  let i := Classical.choose a.support_nonempty
  have hi : i ∈ a.1.support := Classical.choose_spec a.support_nonempty
  apply SSet.Subcomplex.homOfLE
  have hface : SSet.stdSimplex.face a.1.supportᶜ ≤
      SSet.stdSimplex.face ({i} : Finset (Fin 8))ᶜ :=
    (SSet.stdSimplex.face_le_face_iff _ _).mpr (by
      intro j hj
      simp only [Finset.mem_compl, Finset.mem_singleton]
      intro hji
      subst j
      exact (Finset.mem_compl.mp hj) hi)
  exact hface.trans (SSet.face_singleton_compl_le_boundary i)

/-- Forgetting the boundary subtype recovers the ordinary inclusion of the common face in the
ambient standard simplex. -/
@[reassoc]
public theorem boundarySevenProperCechTupleFaceToBoundarySSetMap_comp_inclusion
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    boundarySevenProperCechTupleFaceToBoundarySSetMap a ≫
        (SSet.boundary 7).ι =
      (SSet.stdSimplex.face a.1.supportᶜ).ι := by
  simp [boundarySevenProperCechTupleFaceToBoundarySSetMap]

set_option backward.isDefEq.respectTransparency false in
/-- The representability isomorphism uses exactly the increasing complementary-vertex
inclusion. -/
public theorem boundarySevenProperCechTupleFaceIso_hom_comp_faceInclusion
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    (boundarySevenProperCechTupleFaceIso a).hom ≫
        (SSet.stdSimplex.face a.1.supportᶜ).ι =
      SSet.stdSimplex.map
        (boundarySevenProperCechTupleComplementSimplexHom a) := by
  rfl

/-- Insert the barycentric coordinates of the complementary standard simplex into the eight
coordinates of the ambient seven-simplex. -/
public noncomputable def boundarySevenProperCechTupleCoordinatePoint
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (x : SSet.toTop.obj
      (Δ[boundarySevenProperCechTupleFaceDimension a] : SSet.{0})) :
    stdSimplex ℝ (Fin 8) :=
  stdSimplex.map
    (fun j ↦ (boundarySevenProperCechTupleFaceOrderIso a j).1)
    (SimplexCategory.toTopHomeo
      (SimplexCategory.mk (boundarySevenProperCechTupleFaceDimension a)) x)

/-- In barycentric coordinates, realizing the common-face inclusion is the literal insertion
of the complementary coordinates. -/
public theorem boundarySevenRealizationToStdSimplex_faceToBoundary_faceIso
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (x : SSet.toTop.obj
      (Δ[boundarySevenProperCechTupleFaceDimension a] : SSet.{0})) :
    boundarySevenRealizationToStdSimplex
        (SSet.toTop.map (boundarySevenProperCechTupleFaceToBoundarySSetMap a)
          (SSet.toTop.map (boundarySevenProperCechTupleFaceIso a).hom x)) =
      boundarySevenProperCechTupleCoordinatePoint a x := by
  unfold boundarySevenRealizationToStdSimplex
  change SimplexCategory.toTopHomeo (SimplexCategory.mk 7)
      (SSet.toTop.map (SSet.boundary 7).ι
        (SSet.toTop.map (boundarySevenProperCechTupleFaceToBoundarySSetMap a)
          (SSet.toTop.map (boundarySevenProperCechTupleFaceIso a).hom x))) = _
  rw [← ConcreteCategory.comp_apply, ← SSet.toTop.map_comp,
    boundarySevenProperCechTupleFaceToBoundarySSetMap_comp_inclusion]
  rw [← ConcreteCategory.comp_apply, ← SSet.toTop.map_comp,
    boundarySevenProperCechTupleFaceIso_hom_comp_faceInclusion]
  exact SimplexCategory.toTopHomeo_naturality_apply
    (boundarySevenProperCechTupleComplementSimplexHom a) x

/-- Coordinates indexed by the tuple's support vanish in the complementary coordinate point. -/
public theorem boundarySevenProperCechTupleCoordinatePoint_apply_of_mem_support
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (x : SSet.toTop.obj
      (Δ[boundarySevenProperCechTupleFaceDimension a] : SSet.{0}))
    {i : Fin 8} (hi : i ∈ a.1.support) :
    boundarySevenProperCechTupleCoordinatePoint a x i = 0 := by
  apply stdSimplex_map_apply_eq_zero_of_not_mem_range
  rintro ⟨j, rfl⟩
  exact (Finset.mem_compl.mp
    (boundarySevenProperCechTupleFaceOrderIso a j).2) hi

/-- The complementary coordinate point lies in the ordinary simplex boundary. -/
public theorem boundarySevenProperCechTupleCoordinatePoint_mem_boundary
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (x : SSet.toTop.obj
      (Δ[boundarySevenProperCechTupleFaceDimension a] : SSet.{0})) :
    ∃ i, boundarySevenProperCechTupleCoordinatePoint a x i = 0 := by
  exact ⟨a.1 0,
    boundarySevenProperCechTupleCoordinatePoint_apply_of_mem_support a x
      (a.1.mem_support 0)⟩

/-- The literal coordinate inclusion from the complementary standard simplex into the
intersection belonging to the tuple support. -/
public noncomputable def boundarySevenProperCechTupleStandardSimplexToIntersection
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    C((SSet.toTop.obj
        (Δ[boundarySevenProperCechTupleFaceDimension a] : SSet.{0}) : Type),
      boundarySevenFaceNeighborhoodIntersection a.1.support) := by
  let q : C((SSet.toTop.obj
        (Δ[boundarySevenProperCechTupleFaceDimension a] : SSet.{0}) : Type),
      StandardSimplexBoundary 7) :=
    ⟨fun x ↦ ⟨boundarySevenProperCechTupleCoordinatePoint a x,
        boundarySevenProperCechTupleCoordinatePoint_mem_boundary a x⟩,
      (stdSimplex.continuous_map
        (fun j ↦ (boundarySevenProperCechTupleFaceOrderIso a j).1)).comp
          (SimplexCategory.toTopHomeo
            (SimplexCategory.mk
              (boundarySevenProperCechTupleFaceDimension a))).continuous |>.subtype_mk _⟩
  have hmem (x : SSet.toTop.obj
      (Δ[boundarySevenProperCechTupleFaceDimension a] : SSet.{0})) :
      boundarySevenRealizationHomeomorphStandardBoundary.symm (q x) ∈
        boundarySevenFaceNeighborhoodIntersection a.1.support := by
    rw [mem_boundarySevenFaceNeighborhoodIntersection_iff]
    intro i hi
    have hcoord :
        boundarySevenRealizationToStdSimplex
            (boundarySevenRealizationHomeomorphStandardBoundary.symm (q x)) i = 0 := by
      rw [← boundarySevenRealizationHomeomorphStandardBoundary_apply_val]
      rw [Homeomorph.apply_symm_apply]
      exact boundarySevenProperCechTupleCoordinatePoint_apply_of_mem_support a x hi
    rw [hcoord]
    norm_num
  exact
    ⟨fun x ↦
        ⟨boundarySevenRealizationHomeomorphStandardBoundary.symm (q x), hmem x⟩,
      (boundarySevenRealizationHomeomorphStandardBoundary.symm.continuous.comp
        q.continuous).subtype_mk (fun x ↦ hmem x)⟩

/-- The underlying boundary point of the literal coordinate map. -/
@[simp]
public theorem boundarySevenProperCechTupleStandardSimplexToIntersection_val
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n)
    (x : SSet.toTop.obj
      (Δ[boundarySevenProperCechTupleFaceDimension a] : SSet.{0})) :
    (boundarySevenProperCechTupleStandardSimplexToIntersection a x).1 =
      boundarySevenRealizationHomeomorphStandardBoundary.symm
        ⟨boundarySevenProperCechTupleCoordinatePoint a x,
          boundarySevenProperCechTupleCoordinatePoint_mem_boundary a x⟩ := by
  rfl

/-- The literal coordinate inclusion with the common face itself as source.  The inverse of the
canonical representability isomorphism merely changes from face coordinates to the ordered
complementary standard-simplex coordinates. -/
public noncomputable def boundarySevenProperCechTupleFaceToIntersection
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    C((SSet.toTop.obj
        (SSet.stdSimplex.face a.1.supportᶜ : SSet.{0}) : Type),
      boundarySevenFaceNeighborhoodIntersection a.1.support) :=
  (boundarySevenProperCechTupleStandardSimplexToIntersection a).comp
    (SSet.toTop.map (boundarySevenProperCechTupleFaceIso a).inv).hom

/-- The underlying inclusion of a face-neighbourhood intersection into the realized simplicial
boundary. -/
public def boundarySevenFaceNeighborhoodIntersectionToBoundary
    (s : Finset (Fin 8)) :
    C(boundarySevenFaceNeighborhoodIntersection s,
      (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

set_option backward.isDefEq.respectTransparency false in
/-- The literal local coordinate map, followed by the ambient inclusion, is exactly the
realization of the canonical inclusion of the common face in the simplicial boundary. -/
public theorem boundarySevenProperCechTupleFaceToIntersection_comp_ambientInclusion
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    (boundarySevenFaceNeighborhoodIntersectionToBoundary a.1.support).comp
        (boundarySevenProperCechTupleFaceToIntersection a) =
      (SSet.toTop.map
        (boundarySevenProperCechTupleFaceToBoundarySSetMap a)).hom := by
  apply ContinuousMap.ext
  intro x
  let J := boundarySevenProperCechTupleFaceIso a
  change (boundarySevenProperCechTupleFaceToIntersection a x).1 =
    SSet.toTop.map (boundarySevenProperCechTupleFaceToBoundarySSetMap a) x
  change (boundarySevenProperCechTupleStandardSimplexToIntersection a
    (SSet.toTop.map J.inv x)).1 = _
  apply boundarySevenRealizationHomeomorphStandardBoundary.injective
  rw [boundarySevenProperCechTupleStandardSimplexToIntersection_val]
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  change boundarySevenProperCechTupleCoordinatePoint a
      (SSet.toTop.map J.inv x) =
    (boundarySevenRealizationHomeomorphStandardBoundary
      (SSet.toTop.map
        (boundarySevenProperCechTupleFaceToBoundarySSetMap a) x) :
          stdSimplex ℝ (Fin 8))
  rw [boundarySevenRealizationHomeomorphStandardBoundary_apply_val]
  rw [← boundarySevenRealizationToStdSimplex_faceToBoundary_faceIso a
    (SSet.toTop.map J.inv x)]
  congr 2
  rw [← ConcreteCategory.comp_apply, ← SSet.toTop.map_comp,
    Iso.inv_hom_id, SSet.toTop.map_id]
  rfl

/-- Categorical form of the ambient-inclusion compatibility, stated with the standard
topological-subset inclusion used by the Cech comparison. -/
@[reassoc]
public theorem boundarySevenProperCechTupleFaceToIntersection_comp_subsetInclusion
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    TopCat.ofHom (boundarySevenProperCechTupleFaceToIntersection a) ≫
        topologicalSubsetInclusion
          (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
          (boundarySevenFaceNeighborhoodIntersection a.1.support) =
      SSet.toTop.map
        (boundarySevenProperCechTupleFaceToBoundarySSetMap a) := by
  apply ConcreteCategory.hom_ext
  intro x
  exact DFunLike.congr_fun
    (boundarySevenProperCechTupleFaceToIntersection_comp_ambientInclusion a) x

/-- The canonical simplicial map from the common face to singular simplices in the matching
face-neighbourhood intersection. -/
public noncomputable def boundarySevenProperCechTupleLocalComparisonSSetMap
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    (SSet.stdSimplex.face a.1.supportᶜ : SSet.{0}) ⟶
      TopCat.toSSet.obj
        (TopCat.of (boundarySevenFaceNeighborhoodIntersection a.1.support)) :=
  sSetTopAdj.unit.app
      (SSet.stdSimplex.face a.1.supportᶜ : SSet.{0}) ≫
    TopCat.toSSet.map
      (TopCat.ofHom (boundarySevenProperCechTupleFaceToIntersection a))

/-- The integral chain map induced by the ordered-tuple local comparison. -/
public noncomputable def boundarySevenProperCechTupleLocalIntegralComparison
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    (SSet.stdSimplex.face a.1.supportᶜ : SSet.{0}).chainComplex
        (AddCommGrpCat.of ℤ) ⟶
      (TopCat.toSSet.obj
        (TopCat.of (boundarySevenFaceNeighborhoodIntersection a.1.support))).chainComplex
          (AddCommGrpCat.of ℤ) :=
  SSet.chainComplexMap
    (boundarySevenProperCechTupleLocalComparisonSSetMap a)
      (AddCommGrpCat.of ℤ)

set_option backward.isDefEq.respectTransparency false in
/-- Precomposing the face comparison by its canonical representability isomorphism gives the
standard-simplex comparison associated to the literal coordinate inclusion. -/
public theorem boundarySevenProperCechTupleFaceIso_hom_comp_localComparisonSSetMap
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    (boundarySevenProperCechTupleFaceIso a).hom ≫
        boundarySevenProperCechTupleLocalComparisonSSetMap a =
      sSetTopAdj.unit.app
          (Δ[boundarySevenProperCechTupleFaceDimension a] : SSet.{0}) ≫
        TopCat.toSSet.map (TopCat.ofHom
          (boundarySevenProperCechTupleStandardSimplexToIntersection a)) := by
  let J := boundarySevenProperCechTupleFaceIso a
  have hnat := sSetTopAdj.unit.naturality J.hom
  rw [boundarySevenProperCechTupleLocalComparisonSSetMap]
  change (((𝟭 SSet).map J.hom ≫ sSetTopAdj.unit.app
      (SSet.stdSimplex.face a.1.supportᶜ : SSet.{0})) ≫
    TopCat.toSSet.map (TopCat.ofHom
      (boundarySevenProperCechTupleFaceToIntersection a))) = _
  rw [hnat]
  change (sSetTopAdj.unit.app
      (Δ[boundarySevenProperCechTupleFaceDimension a] : SSet.{0}) ≫
    TopCat.toSSet.map (SSet.toTop.map J.hom)) ≫
      TopCat.toSSet.map (TopCat.ofHom
        (boundarySevenProperCechTupleFaceToIntersection a)) = _
  simp only [Category.assoc]
  rw [← Functor.map_comp]
  apply congrArg (fun f ↦ sSetTopAdj.unit.app
    (Δ[boundarySevenProperCechTupleFaceDimension a] : SSet.{0}) ≫
      TopCat.toSSet.map f)
  apply ConcreteCategory.hom_ext
  intro x
  change boundarySevenProperCechTupleStandardSimplexToIntersection a
      (SSet.toTop.map J.inv (SSet.toTop.map J.hom x)) =
    boundarySevenProperCechTupleStandardSimplexToIntersection a x
  rw [← ConcreteCategory.comp_apply, ← SSet.toTop.map_comp,
    Iso.hom_inv_id, SSet.toTop.map_id]
  rfl

/-- Chain-level form of the preceding representability identity. -/
public theorem boundarySevenProperCechTupleFaceIso_chainMap_comp_localIntegralComparison
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    SSet.chainComplexMap (boundarySevenProperCechTupleFaceIso a).hom
        (AddCommGrpCat.of ℤ) ≫
      boundarySevenProperCechTupleLocalIntegralComparison a =
    standardSimplexToContractibleSingularChainMap (AddCommGrpCat.of ℤ)
      (boundarySevenProperCechTupleFaceDimension a)
      (boundarySevenProperCechTupleStandardSimplexToIntersection a) := by
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  have h := F.congr_map
    (boundarySevenProperCechTupleFaceIso_hom_comp_localComparisonSSetMap a)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

/-- The canonical integral comparison on every proper ordered Cech tuple is a
quasi-isomorphism. -/
public theorem boundarySevenProperCechTupleLocalIntegralComparison_quasiIso
    {n : SimplexCategoryᵒᵖ} (a : BoundarySevenProperCechTuple n) :
    QuasiIso (boundarySevenProperCechTupleLocalIntegralComparison a) := by
  let P := SSet.chainComplexMap (boundarySevenProperCechTupleFaceIso a).hom
    (AddCommGrpCat.of ℤ)
  let L := boundarySevenProperCechTupleLocalIntegralComparison a
  letI : IsIso (boundarySevenProperCechTupleFaceIso a).hom := inferInstance
  letI : IsIso P := by
    dsimp only [P]
    infer_instance
  let hstandard : QuasiIso
      (standardSimplexToContractibleSingularChainMap (AddCommGrpCat.of ℤ)
        (boundarySevenProperCechTupleFaceDimension a)
        (boundarySevenProperCechTupleStandardSimplexToIntersection a)) :=
    standardSimplexToBoundarySevenFaceNeighborhoodIntersection_quasiIso
      (AddCommGrpCat.of ℤ) (boundarySevenProperCechTupleFaceDimension a)
      a.1.support a.support_nonempty a.2
      (boundarySevenProperCechTupleStandardSimplexToIntersection a)
  have hcomp : QuasiIso (P ≫ L) := by
    rw [show P ≫ L =
        standardSimplexToContractibleSingularChainMap (AddCommGrpCat.of ℤ)
          (boundarySevenProperCechTupleFaceDimension a)
          (boundarySevenProperCechTupleStandardSimplexToIntersection a) by
      exact boundarySevenProperCechTupleFaceIso_chainMap_comp_localIntegralComparison a]
    exact hstandard
  exact quasiIso_of_comp_left P L

end SphereSixComplex
