module

public import DifferentialGeometry.Topology.Homology.Subdivision.MeshChains
public import DifferentialGeometry.Topology.Homology.SmallChains.Compactness
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v

namespace DifferentialGeometry.Homology

theorem SimplexSmallness.convex_coordinateSimplex (n : ℕ) :
    Convex ℝ (ULift.down ⁻¹' Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)) :
      Set (ULift.{u} (Fin (n + 1) → ℝ))) := by
  intro x hx y hy a b ha hb hab
  exact (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin (n + 1))) hx hy ha hb hab


def affineSimplexCoordinateLift {n : ℕ} (v : Fin (n + 1) → ULift.{u} (Fin (n + 1) → ℝ))
    (hv : ∀ i, (v i).down ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1))) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  ⟨fun x ↦ (Convexity.StdSimplex.coordinateHomeomorph ℝ (Fin (n + 1))).symm
      ⟨(affineSimplex v x).down,
        range_affineSimplex_subset v (SimplexSmallness.convex_coordinateSimplex n) hv ⟨x, rfl⟩⟩,
    (Convexity.StdSimplex.coordinateHomeomorph ℝ (Fin (n + 1))).symm.continuous.comp
      ((continuous_uliftDown.comp (affineSimplex v).continuous).subtype_mk _)⟩


theorem dist_affineSimplexCoordinateLift_le {n : ℕ}
    (v : Fin (n + 1) → ULift.{u} (Fin (n + 1) → ℝ))
    (hv : ∀ i, (v i).down ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1))) {D : ℝ}
    (hD : ∀ i j, dist (v i) (v j) ≤ D)
    (x y : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    dist (affineSimplexCoordinateLift v hv x) (affineSimplexCoordinateLift v hv y) ≤ D := by
  change dist (affineSimplex v x) (affineSimplex v y) ≤ D
  exact dist_affineSimplex_le v hD x y


def affineSingularSimplexCoordinateLift {n : ℕ}
    (v : Fin (n + 1) → ULift.{u} (Fin (n + 1) → ℝ))
    (hv : ∀ i, (v i).down ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1))) :
    TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌) _⦋n⦌ :=
  ((SimplexCategory.toTop.obj ⦋n⦌).toSSetObjEquiv (op ⦋n⦌)).symm
    ⟨fun x ↦ ULift.up (affineSimplexCoordinateLift v hv x),
      continuous_uliftUp.comp (affineSimplexCoordinateLift v hv).continuous⟩


theorem affineSingularSimplexCoordinateLift_embedding {n : ℕ}
    (v : Fin (n + 1) → ULift.{u} (Fin (n + 1) → ℝ))
    (hv : ∀ i, (v i).down ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1))) :
    (TopCat.toSSet.map (simplexCoordinateEmbedding n)).app (op ⦋n⦌)
        (affineSingularSimplexCoordinateLift v hv) = affineSingularSimplex v := by
  apply ((TopCat.of (ULift.{u} (Fin (n + 1) → ℝ))).toSSetObjEquiv (op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro x
  rfl

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem singularSubdivision_pow_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (m : ℕ) :
    (End.of (singularSubdivision R X) ^ m) ≫ SSet.chainComplexMap (TopCat.toSSet.map f) R =
      SSet.chainComplexMap (TopCat.toSSet.map f) R ≫ (End.of (singularSubdivision R Y) ^ m) := by
  induction m with
  | zero => simp only [pow_zero, End.one_def, Category.id_comp, Category.comp_id]
  | succ m hm =>
    rw [pow_succ' (End.of (singularSubdivision R X)) m,
      pow_succ' (End.of (singularSubdivision R Y)) m, End.mul_def, End.mul_def]
    simp only [Category.assoc]
    rw [singularSubdivision_naturality]
    rw [← Category.assoc (End.of (singularSubdivision R X) ^ m), hm]
    simp only [Category.assoc]

variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)

private theorem affineMeshSubmodule_le_coordinate_map {n : ℕ}
    (σ : TopCat.toSSet.obj X _⦋n⦌) {δ : ℝ}
    (hsmall : ∀ τ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))),
      (∀ a b, dist (τ a) (τ b) < δ) →
        ((X.toSSetObjEquiv (op ⦋n⦌)).symm ((X.toSSetObjEquiv (op ⦋n⦌) σ).comp τ)) ∈
          (smallSingularSimplices X U).obj (op ⦋n⦌)) {D : ℝ} (hDδ : D < δ) :
    affineMeshSubmodule R
      (ULift.down ⁻¹' Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)) : Set (ULift.{u} (Fin (n + 1) → ℝ))) n D ≤
    ((LinearMap.range ((smallChainMap X U R).f n).hom).comap
      ((SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n).hom).map
      ((SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R).f n).hom := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hvs, hvD, r, rfl⟩
  let τ := affineSingularSimplexCoordinateLift v hvs
  have hτ : (TopCat.toSSet.map (singularSimplexMap X σ)).app (op ⦋n⦌) τ ∈
      (smallSingularSimplices X U).obj (op ⦋n⦌) := by
    change ((X.toSSetObjEquiv (op ⦋n⦌)).symm
      ((X.toSSetObjEquiv (op ⦋n⦌) σ).comp (affineSimplexCoordinateLift v hvs))) ∈ _
    exact hsmall _ (fun a b ↦ (dist_affineSimplexCoordinateLift_le v hvs hvD a b).trans_lt hDδ)
  let τsmall : (smallSingularSimplices X U : SSet) _⦋n⦌ :=
    ⟨(TopCat.toSSet.map (singularSimplexMap X σ)).app (op ⦋n⦌) τ, hτ⟩
  refine Submodule.mem_map.mpr ⟨(TopCat.toSSet.obj (SimplexCategory.toTop.obj ⦋n⦌)).ιChainComplex
    (R := R) τ r, ?_, ?_⟩
  · change (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n
      ((TopCat.toSSet.obj (SimplexCategory.toTop.obj ⦋n⦌)).ιChainComplex (R := R) τ r) ∈
        LinearMap.range ((smallChainMap X U R).f n).hom
    refine ⟨(smallSingularSimplices X U : SSet).ιChainComplex (R := R) τsmall r, ?_⟩
    have he : (smallSingularSimplices X U : SSet).ιChainComplex
        τsmall ≫
          (smallChainMap X U R).f n =
        (TopCat.toSSet.obj (SimplexCategory.toTop.obj ⦋n⦌)).ιChainComplex τ ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n := by
      rw [ι_smallChainMap_f, SSet.ι_chainComplexMap_f]
    exact congrArg (fun q ↦ ModuleCat.Hom.hom q r) he
  · have he := SSet.ι_chainComplexMap_f _ _
      (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R τ
    change _ = (TopCat.toSSet.obj (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))).ιChainComplex
      (R := R) (affineSingularSimplex v) r
    rw [show τ = affineSingularSimplexCoordinateLift v hvs from rfl,
      affineSingularSimplexCoordinateLift_embedding] at he
    exact congrArg (fun q ↦ ModuleCat.Hom.hom q r) he

theorem exists_small_subdivision_power_generator
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ r : R,
      (End.of (singularSubdivision R X) ^ m).f n
          ((TopCat.toSSet.obj X).ιChainComplex (R := R) σ r) ∈
        LinearMap.range ((smallChainMap X U R).f n).hom := by
  let v₀ : Fin (n + 1) → ULift.{u} (Fin (n + 1) → ℝ) :=
    fun i ↦ ULift.up (Pi.single i (1 : ℝ))
  let D₀ : ℝ := Metric.diam (Set.range v₀)
  have hv₀ : ∀ i, (v₀ i).down ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)) :=
    fun i ↦ Convexity.StdSimplex.single_mem_coordinateSet ℝ i
  have hD₀ : ∀ i j, dist (v₀ i) (v₀ j) ≤ D₀ := fun i j ↦
    Metric.dist_le_diam_of_mem (Set.finite_range v₀).isBounded ⟨i, rfl⟩ ⟨j, rfl⟩
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_precomp_radius X U hopen hcover σ
  obtain ⟨N, hN⟩ := exists_uniform_subdivision_mesh_threshold R
    (SimplexSmallness.convex_coordinateSimplex n) n D₀ hδ
  refine ⟨N, ?_⟩
  intro m hm r
  let J := SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R
  let F := SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R
  let c := (End.of (singularSubdivision R (SimplexCategory.toTop.obj ⦋n⦌)) ^ m).f n
    (fundamentalSimplexChain R n r)
  have hJfund : fundamentalSimplexChain R n ≫ J.f n =
      (TopCat.toSSet.obj (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))).ιChainComplex
        (R := R) (affineSingularSimplex v₀) := by
    change fundamentalSimplexChain R n ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R).f n = _
    rw [← singularSimplexMap_coordinateVertices, fundamentalSimplexChain_pushforward]
  have hJc : J.f n c =
      (End.of (singularSubdivision R (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))) ^ m).f n
        ((TopCat.toSSet.obj (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))).ιChainComplex
          (R := R) (affineSingularSimplex v₀) r) := by
    have hn := HomologicalComplex.congr_hom
      (singularSubdivision_pow_naturality R (simplexCoordinateEmbedding n) m) n
    have he := congrArg (fun q ↦ ModuleCat.Hom.hom q (fundamentalSimplexChain R n r)) hn
    change J.f n c =
      (End.of (singularSubdivision R (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))) ^ m).f n
        (J.f n (fundamentalSimplexChain R n r)) at he
    rw [show J.f n (fundamentalSimplexChain R n r) =
      (TopCat.toSSet.obj (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))).ιChainComplex
        (R := R) (affineSingularSimplex v₀) r from
      congrArg (fun q ↦ ModuleCat.Hom.hom q r) hJfund] at he
    exact he
  have hmesh : J.f n c ∈ affineMeshSubmodule R
      (ULift.down ⁻¹' Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)) : Set (ULift.{u} (Fin (n + 1) → ℝ)))
      n (((n : ℝ) / (n + 1)) ^ m * D₀) := by
    rw [hJc]
    exact (hN m hm).2 _ (affineGenerator_mem_affineMeshSubmodule R v₀ hv₀ hD₀ r)
  have himage := affineMeshSubmodule_le_coordinate_map R X U σ (hsmall n)
    (hN m hm).1 hmesh
  obtain ⟨a, ha, hac⟩ := Submodule.mem_map.mp himage
  have hJmono : Mono (J.f n) := mono_simplexCoordinateEmbedding_chainMap_f R n n
  have hac' : a = c := (ModuleCat.mono_iff_injective (J.f n)).mp hJmono hac
  subst a
  have hFfund := fundamentalSimplexChain_pushforward R X σ
  have hn := HomologicalComplex.congr_hom
    (singularSubdivision_pow_naturality R (singularSimplexMap X σ) m) n
  have he := congrArg (fun q ↦ ModuleCat.Hom.hom q (fundamentalSimplexChain R n r)) hn
  change F.f n c = (End.of (singularSubdivision R X) ^ m).f n
    (F.f n (fundamentalSimplexChain R n r)) at he
  rw [show F.f n (fundamentalSimplexChain R n r) =
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ r from
      congrArg (fun q ↦ ModuleCat.Hom.hom q r) hFfund] at he
  rw [← he]
  exact ha

end DifferentialGeometry.Homology
