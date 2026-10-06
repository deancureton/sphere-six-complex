module

public import DifferentialGeometry.Topology.Homology.Subdivision.Singular

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology


def simplexCoordinateEmbedding (n : ℕ) :
    SimplexCategory.toTop.{u}.obj ⦋n⦌ ⟶ TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.down.weights⟩,
    continuous_uliftUp.comp
      ((Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous.comp
        continuous_uliftDown)⟩

private def coordinateRegion (n : ℕ) : Set (ULift.{u} (Fin (n + 1) → ℝ)) :=
  ULift.down ⁻¹' Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1))

private theorem convex_coordinateRegion (n : ℕ) : Convex ℝ (coordinateRegion.{u} n) := by
  intro x hx y hy a b ha hb hab
  exact (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin (n + 1))) hx hy ha hb hab

private def coordinateRegionHomeo (n : ℕ) :
    SimplexCategory.toTop.{u}.obj ⦋n⦌ ≃ₜ coordinateRegion.{u} n where
  toFun x := ⟨⟨x.down.weights⟩, x.down.weights_nonneg, x.down.total_of_fintype⟩
  invFun x := ⟨(Convexity.StdSimplex.coordinateEquiv ℝ (Fin (n + 1))).symm
    ⟨x.val.down, x.property⟩⟩
  left_inv x := by
    apply ULift.ext
    exact (Convexity.StdSimplex.coordinateEquiv ℝ (Fin (n + 1))).left_inv x.down
  right_inv x := by
    apply Subtype.ext
    apply ULift.ext
    exact congrArg Subtype.val
      ((Convexity.StdSimplex.coordinateEquiv ℝ (Fin (n + 1))).right_inv
        ⟨x.val.down, x.property⟩)
  continuous_toFun :=
    (continuous_uliftUp.comp
      ((Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous.comp
        continuous_uliftDown)).subtype_mk _
  continuous_invFun :=
    continuous_uliftUp.comp
      ((Convexity.StdSimplex.coordinateHomeomorph ℝ (Fin (n + 1))).symm.continuous.comp
        ((continuous_uliftDown.comp continuous_subtype_val).subtype_mk _))

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

private def coordinateChainIso (n : ℕ) :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).mapIso
    (TopCat.toSSet.mapIso (TopCat.isoOfHomeo (coordinateRegionHomeo n)) ≪≫
      singularSubspaceIso (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ))) (coordinateRegion n))

private theorem coordinateChainIso_inclusion (n : ℕ) :
    (coordinateChainIso R n).hom ≫
      SSet.chainComplexMap
        (smallSingularSimplices (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))
          (fun _ : Unit ↦ coordinateRegion n)).ι R =
      SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp]
  rfl

private theorem coordinateChainIso_inv_inclusion (n : ℕ) :
    (coordinateChainIso R n).inv ≫
        SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R =
      SSet.chainComplexMap
        (smallSingularSimplices (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))
          (fun _ : Unit ↦ coordinateRegion n)).ι R := by
  rw [← coordinateChainIso_inclusion R n, Iso.inv_hom_id_assoc]


theorem mono_simplexCoordinateEmbedding_chainMap_f (n d : ℕ) :
    Mono ((SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R).f d) := by
  have h := HomologicalComplex.congr_hom (coordinateChainIso_inclusion R n) d
  simp only [HomologicalComplex.comp_f] at h
  rw [← h]
  have : Mono ((SSet.chainComplexMap
      (smallSingularSimplices (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))
        (fun _ : Unit ↦ coordinateRegion n)).ι R).f d) :=
    mono_smallChainMap_f _ _ R d
  infer_instance


theorem simplexSubdivision_coordinateEmbedding (n : ℕ) :
    simplexSubdivision R n ≫
        SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R =
      SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R ≫
        affineSubdivision R := by
  change ((coordinateChainIso R n).hom ≫
      smallAffineSubdivision (convex_coordinateRegion n) R ≫ (coordinateChainIso R n).inv) ≫
        SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R = _
  simp only [Category.assoc]
  rw [coordinateChainIso_inv_inclusion]
  rw [smallAffineSubdivision_inclusion]
  rw [← Category.assoc ((coordinateChainIso R n).hom), coordinateChainIso_inclusion]


theorem affineSimplex_coordinateVertices (n : ℕ) (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    affineSimplex (fun i ↦ (ULift.up (Pi.single i (1 : ℝ)) :
      ULift.{u} (Fin (n + 1) → ℝ))) x = ULift.up (x.weights : Fin (n + 1) → ℝ) := by
  apply ULift.ext
  change (ULift.moduleEquiv : ULift.{u} (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
      (∑ i, x.weights i • ULift.up (Pi.single i (1 : ℝ))) = (x.weights : Fin (n + 1) → ℝ)
  rw [map_sum]
  simp only [map_smul, ULift.moduleEquiv_apply]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]


theorem singularSimplexMap_coordinateVertices (n : ℕ) :
    singularSimplexMap (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))
        (affineSingularSimplex (fun i ↦ ULift.up (Pi.single i (1 : ℝ)))) =
      simplexCoordinateEmbedding n := by
  apply TopCat.ext
  intro x
  exact affineSimplex_coordinateVertices n x.down


theorem barycentricSimplexChain_coordinateEmbedding (n : ℕ) :
    barycentricSimplexChain R n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R).f n =
      (TopCat.toSSet.obj (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))).ιChainComplex
        (affineSingularSimplex (fun i ↦ ULift.up (Pi.single i (1 : ℝ)))) ≫
          affineSubdivisionMap R n := by
  have h := HomologicalComplex.congr_hom (simplexSubdivision_coordinateEmbedding R n) n
  simp only [HomologicalComplex.comp_f, affineSubdivision_f] at h
  rw [barycentricSimplexChain, Category.assoc, h, ← Category.assoc]
  rw [← singularSimplexMap_coordinateVertices, fundamentalSimplexChain_pushforward]

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


def vertexCoordinateMap {n : ℕ} (v : Fin (n + 1) → E) :
    ULift.{u} (Fin (n + 1) → ℝ) →L[ℝ] E where
  toFun x := ∑ i, x.down i • v i
  map_add' x y := by
    change (∑ i, (x.down i + y.down i) • v i) = _
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    change (∑ i, (a * x.down i) • v i) = a • ∑ i, x.down i • v i
    simp only [Finset.smul_sum, mul_smul]
  cont := continuous_finsetSum _ (fun i _ ↦
    ((continuous_apply i).comp continuous_uliftDown).smul continuous_const)


@[simp]
theorem vertexCoordinateMap_vertex {n : ℕ} (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    vertexCoordinateMap v (ULift.up (Pi.single i (1 : ℝ))) = v i := by
  simp [vertexCoordinateMap, Pi.single_apply]


theorem simplexCoordinateEmbedding_vertexCoordinateMap {n : ℕ} (v : Fin (n + 1) → E) :
    simplexCoordinateEmbedding n ≫ TopCat.ofHom (⟨vertexCoordinateMap v,
        (vertexCoordinateMap v).continuous⟩ : C(ULift.{u} (Fin (n + 1) → ℝ), E)) =
      singularSimplexMap (TopCat.of E) (affineSingularSimplex v) := rfl


theorem singularSubdivisionMap_affine {n : ℕ} (v : Fin (n + 1) → E) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (affineSingularSimplex v) ≫
        singularSubdivisionMap R (TopCat.of E) n =
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (affineSingularSimplex v) ≫
        affineSubdivisionMap R n := by
  let F := SSet.chainComplexMap (TopCat.toSSet.map
    (TopCat.ofHom (⟨vertexCoordinateMap v, (vertexCoordinateMap v).continuous⟩ :
      C(ULift.{u} (Fin (n + 1) → ℝ), E)))) R
  have hF : SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R ≫ F =
      SSet.chainComplexMap (TopCat.toSSet.map
        (singularSimplexMap (TopCat.of E) (affineSingularSimplex v))) R := by
    change ((SSet.chainComplexFunctor _).obj R).map _ ≫
        ((SSet.chainComplexFunctor _).obj R).map _ =
      ((SSet.chainComplexFunctor _).obj R).map _
    rw [← Functor.map_comp, ← TopCat.toSSet.map_comp,
      simplexCoordinateEmbedding_vertexCoordinateMap]
  have hf := HomologicalComplex.congr_hom hF n
  simp only [HomologicalComplex.comp_f] at hf
  rw [ι_singularSubdivisionMap, ← hf, ← Category.assoc,
    barycentricSimplexChain_coordinateEmbedding, Category.assoc]
  have hn : affineSubdivisionMap R n ≫ F.f n = F.f n ≫ affineSubdivisionMap R n :=
    affineSubdivisionMap_naturality_linear (vertexCoordinateMap v) R n
  rw [hn, ← Category.assoc]
  change (_ ≫ (SSet.chainComplexMap _ R).f n) ≫ _ = _
  rw [SSet.ι_chainComplexMap_f, map_affineSingularSimplex_linear]
  have hv : vertexCoordinateMap v ∘
      (fun i ↦ ULift.up (Pi.single i (1 : ℝ))) = v := by
    funext i
    exact vertexCoordinateMap_vertex v i
  rw [hv]

end DifferentialGeometry.Homology
