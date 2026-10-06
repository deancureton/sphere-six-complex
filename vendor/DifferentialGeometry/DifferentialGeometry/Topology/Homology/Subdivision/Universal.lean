module

public import DifferentialGeometry.Topology.Homology.Subdivision.Restriction
public import DifferentialGeometry.Topology.Simplex.Coordinates

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
universe u
noncomputable section
namespace DifferentialGeometry.Homology
abbrev simplexAmbient (n : ℕ) := ULift.{u} (Fin (n + 1) → ℝ)
def simplexRegion (n : ℕ) : Set (simplexAmbient.{u} n) :=
  ULift.down ⁻¹' Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1))
theorem convex_simplexRegion (n : ℕ) : Convex ℝ (simplexRegion.{u} n) := by
  intro x hx y hy a b ha hb hab
  exact (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin (n + 1))) hx hy ha hb hab
def simplexRegionHomeo (n : ℕ) :
    SimplexCategory.toTop.{u}.obj ⦋n⦌ ≃ₜ simplexRegion.{u} n where
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
private def simplexCoordinatesMap {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    simplexAmbient.{u} n →L[ℝ] simplexAmbient.{u} m where
  toFun x := ⟨FunOnFinite.linearMap ℝ ℝ f x.down⟩
  map_add' x y := by
    apply ULift.ext
    exact map_add (FunOnFinite.linearMap ℝ ℝ f) x.down y.down
  map_smul' a x := by
    apply ULift.ext
    exact map_smul (FunOnFinite.linearMap ℝ ℝ f) a x.down
  cont := continuous_uliftUp.comp ((FunOnFinite.continuous_linearMap ℝ ℝ f).comp
    continuous_uliftDown)
private theorem simplexCoordinatesMap_mem {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    Set.MapsTo (simplexCoordinatesMap.{u} f) (simplexRegion n) (simplexRegion m) := by
  intro x hx
  exact (Convexity.StdSimplex.coordinateMap f ⟨x.down, hx⟩).property
private def simplexEmbedding (n : ℕ) :
    SimplexCategory.toTop.{u}.obj ⦋n⦌ ⟶ TopCat.of (simplexAmbient.{u} n) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.down.weights⟩,
    continuous_uliftUp.comp
      ((Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous.comp
        continuous_uliftDown)⟩
private theorem simplexEmbedding_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    SimplexCategory.toTop.map f ≫ simplexEmbedding m =
      simplexEmbedding n ≫ TopCat.ofHom (⟨simplexCoordinatesMap f,
        (simplexCoordinatesMap f).continuous⟩ : C(simplexAmbient n, simplexAmbient m)) := by
  ext x : 1
  apply ULift.ext
  exact congrArg Subtype.val (Convexity.StdSimplex.coordinateEquiv_map f x.down)

def simplexSupportedIso (n : ℕ) :
    TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌) ≅
      (smallSingularSimplices (TopCat.of (simplexAmbient.{u} n))
        (fun _ : Unit ↦ simplexRegion n) : SSet) :=
  TopCat.toSSet.mapIso (TopCat.isoOfHomeo (simplexRegionHomeo n)) ≪≫
    singularSubspaceIso _ _

private theorem simplexSupportedIso_inclusion (n : ℕ) :
    (simplexSupportedIso.{u} n).hom ≫
        (smallSingularSimplices (TopCat.of (simplexAmbient.{u} n))
          (fun _ : Unit ↦ simplexRegion n)).ι =
      TopCat.toSSet.map (simplexEmbedding n) := rfl

private def simplexSupportedMap {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (smallSingularSimplices (TopCat.of (simplexAmbient.{u} n))
      (fun _ : Unit ↦ simplexRegion n) : SSet) ⟶
    (smallSingularSimplices (TopCat.of (simplexAmbient.{u} m))
      (fun _ : Unit ↦ simplexRegion m) : SSet) :=
  smallSingularSimplicesMap
    (TopCat.ofHom (⟨simplexCoordinatesMap f, (simplexCoordinatesMap f).continuous⟩ :
      C(simplexAmbient n, simplexAmbient m))) (fun _ ↦ ⟨(), simplexCoordinatesMap_mem f⟩)

private theorem simplexSupportedIso_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    TopCat.toSSet.map (SimplexCategory.toTop.map f) ≫ (simplexSupportedIso.{u} m).hom =
      (simplexSupportedIso.{u} n).hom ≫ simplexSupportedMap f := by
  apply (cancel_mono (smallSingularSimplices (TopCat.of (simplexAmbient.{u} m))
    (fun _ : Unit ↦ simplexRegion m)).ι).mp
  simp only [Category.assoc, simplexSupportedIso_inclusion, simplexSupportedMap,
    smallSingularSimplicesMap_ι]
  rw [← Category.assoc, simplexSupportedIso_inclusion, ← Functor.map_comp,
    ← Functor.map_comp, simplexEmbedding_naturality]

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

def simplexSupportedChainIso (n : ℕ) :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).mapIso (simplexSupportedIso.{u} n)

private theorem simplexSupportedChainIso_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R ≫
        (simplexSupportedChainIso R m).hom =
      (simplexSupportedChainIso R n).hom ≫ SSet.chainComplexMap (simplexSupportedMap f) R := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, simplexSupportedIso_naturality]

private theorem simplexSupportedChainIso_inv_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (simplexSupportedChainIso R n).inv ≫
        SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R =
      SSet.chainComplexMap (simplexSupportedMap f) R ≫ (simplexSupportedChainIso R m).inv := by
  apply (Iso.inv_comp_eq _).mpr
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv _).mpr (simplexSupportedChainIso_naturality R f)


def simplexSubdivision (n : ℕ) :
    (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R ⟶
      (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R :=
  (simplexSupportedChainIso R n).hom ≫
    smallAffineSubdivision (convex_simplexRegion n) R ≫ (simplexSupportedChainIso R n).inv


def simplexStraightening (n : ℕ) :
    (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R ⟶
      (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R :=
  (simplexSupportedChainIso R n).hom ≫
    SSet.chainComplexMap (smallAffineStraightening (convex_simplexRegion n)) R ≫
      (simplexSupportedChainIso R n).inv


def simplexSubdivisionHomotopy (n : ℕ) :
    Homotopy (simplexSubdivision R n) (simplexStraightening R n) :=
  ((smallAffineSubdivisionHomotopy (convex_simplexRegion n) R).compLeft
    (simplexSupportedChainIso R n).hom).compRight (simplexSupportedChainIso R n).inv

theorem simplexSubdivision_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    simplexSubdivision R n ≫
        SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R =
      SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R ≫
        simplexSubdivision R m := by
  have hB : smallAffineSubdivision (convex_simplexRegion n) R ≫
        SSet.chainComplexMap (simplexSupportedMap f) R =
      SSet.chainComplexMap (simplexSupportedMap f) R ≫
        smallAffineSubdivision (convex_simplexRegion m) R := by
    apply HomologicalComplex.hom_f_injective
    funext d
    exact smallAffineSubdivisionMap_naturality_linear _ R _ (simplexCoordinatesMap f)
      (simplexCoordinatesMap_mem f) d
  simp only [simplexSubdivision, Category.assoc]
  rw [simplexSupportedChainIso_inv_naturality]
  rw [← Category.assoc (smallAffineSubdivision (convex_simplexRegion n) R), hB]
  simp only [Category.assoc]
  rw [← Category.assoc ((simplexSupportedChainIso R n).hom),
    ← simplexSupportedChainIso_naturality]
  simp only [Category.assoc]


theorem simplexSubdivisionHomotopy_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (d : ℕ) :
    (simplexSubdivisionHomotopy R n).hom d (d + 1) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R).f (d + 1) =
      (SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R).f d ≫
        (simplexSubdivisionHomotopy R m).hom d (d + 1) := by
  have h := HomologicalComplex.congr_hom (simplexSupportedChainIso_naturality R f) d
  have hi := HomologicalComplex.congr_hom (simplexSupportedChainIso_inv_naturality R f) (d + 1)
  simp only [HomologicalComplex.comp_f] at h hi
  simp only [simplexSubdivisionHomotopy, Homotopy.compRight_hom, Homotopy.compLeft_hom,
    smallAffineSubdivisionHomotopy_hom, Category.assoc]
  rw [hi]
  rw [← Category.assoc (smallAffineSubdivisionHomotopyMap (convex_simplexRegion n) R d)]
  have hH : smallAffineSubdivisionHomotopyMap (convex_simplexRegion n) R d ≫
        (SSet.chainComplexMap (simplexSupportedMap f) R).f (d + 1) =
      (SSet.chainComplexMap (simplexSupportedMap f) R).f d ≫
        smallAffineSubdivisionHomotopyMap (convex_simplexRegion m) R d :=
    smallAffineSubdivisionHomotopyMap_naturality_linear _ R _ (simplexCoordinatesMap f)
      (simplexCoordinatesMap_mem f) d
  rw [hH]
  simp only [Category.assoc]
  rw [← Category.assoc ((simplexSupportedChainIso R n).hom.f d), ← h]
  simp only [Category.assoc]


def fundamentalSingularSimplex (n : ℕ) :
    TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌) _⦋n⦌ :=
  ULift.up (𝟙 _)


def fundamentalSimplexChain (n : ℕ) :
    R ⟶ ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R).X n :=
  (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).ιChainComplex
    (fundamentalSingularSimplex n)


def barycentricSimplexChain (n : ℕ) :
    R ⟶ ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R).X n :=
  fundamentalSimplexChain R n ≫ (simplexSubdivision R n).f n


def barycentricSimplexHomotopyChain (n : ℕ) :
    R ⟶ ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R).X (n + 1) :=
  fundamentalSimplexChain R n ≫ (simplexSubdivisionHomotopy R n).hom n (n + 1)


theorem fundamentalSimplexChain_boundary (n : ℕ) :
    fundamentalSimplexChain R (n + 1) ≫
        ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n + 1⦌)).chainComplex R).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1) ^ i.val •
        (fundamentalSimplexChain R n ≫
          (SSet.chainComplexMap (TopCat.toSSet.map
            (SimplexCategory.toTop.map (SimplexCategory.δ i))) R).f n) := by
  rw [fundamentalSimplexChain, SSet.ιChainComplex_d]
  apply Finset.sum_congr rfl
  intro i _
  rw [fundamentalSimplexChain, SSet.ι_chainComplexMap_f]
  rfl


theorem barycentricSimplexChain_boundary (n : ℕ) :
    barycentricSimplexChain R (n + 1) ≫
        ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n + 1⦌)).chainComplex R).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1) ^ i.val •
        (barycentricSimplexChain R n ≫
          (SSet.chainComplexMap (TopCat.toSSet.map
            (SimplexCategory.toTop.map (SimplexCategory.δ i))) R).f n) := by
  rw [barycentricSimplexChain, Category.assoc, (simplexSubdivision R (n + 1)).comm,
    ← Category.assoc, fundamentalSimplexChain_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro i _
  have h := HomologicalComplex.congr_hom (simplexSubdivision_naturality R (SimplexCategory.δ i)) n
  simp only [HomologicalComplex.comp_f] at h
  rw [← h]
  rfl

private theorem simplexEmbedding_fundamental (n : ℕ) :
    (TopCat.toSSet.map (simplexEmbedding.{u} n)).app (op ⦋n⦌) (fundamentalSingularSimplex n) =
      affineSingularSimplex (fun i ↦ ULift.up (Pi.single i (1 : ℝ))) := by
  apply ((TopCat.of (simplexAmbient.{u} n)).toSSetObjEquiv (op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  change (x.weights : Fin (n + 1) → ℝ) =
    (∑ i, x.weights i • ULift.up (Pi.single i (1 : ℝ))).down
  change (x.weights : Fin (n + 1) → ℝ) =
    (ULift.moduleEquiv : simplexAmbient.{u} n ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
      (∑ i, x.weights i • ULift.up (Pi.single i (1 : ℝ)))
  rw [map_sum]
  simp only [map_smul, ULift.moduleEquiv_apply]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]


theorem fundamentalSimplexChain_straightening (n : ℕ) :
    fundamentalSimplexChain R n ≫ (simplexStraightening R n).f n =
      fundamentalSimplexChain R n := by
  have hσ : (smallAffineStraightening (convex_simplexRegion n)).app (op ⦋n⦌)
        ((simplexSupportedIso.{u} n).hom.app (op ⦋n⦌) (fundamentalSingularSimplex n)) =
      (simplexSupportedIso.{u} n).hom.app (op ⦋n⦌) (fundamentalSingularSimplex n) := by
    apply Subtype.ext
    change affineSingularSimplex (singularSimplexVertices
        ((TopCat.toSSet.map (simplexEmbedding n)).app (op ⦋n⦌) (fundamentalSingularSimplex n))) =
      (TopCat.toSSet.map (simplexEmbedding n)).app (op ⦋n⦌) (fundamentalSingularSimplex n)
    rw [simplexEmbedding_fundamental, singularSimplexVertices_affineSingularSimplex]
  have h : fundamentalSimplexChain R n ≫ (simplexSupportedChainIso R n).hom.f n ≫
        (SSet.chainComplexMap (smallAffineStraightening (convex_simplexRegion n)) R).f n =
      fundamentalSimplexChain R n ≫ (simplexSupportedChainIso R n).hom.f n := by
    rw [fundamentalSimplexChain, ← Category.assoc]
    change ((TopCat.toSSet.obj (SimplexCategory.toTop.obj ⦋n⦌)).ιChainComplex
        (fundamentalSingularSimplex n) ≫
        (SSet.chainComplexMap (simplexSupportedIso n).hom R).f n) ≫ _ = _
    rw [SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f, hσ]
    exact (SSet.ι_chainComplexMap_f _ _ _ R (fundamentalSingularSimplex n)).symm
  have hid := HomologicalComplex.congr_hom (simplexSupportedChainIso R n).hom_inv_id n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hid
  change fundamentalSimplexChain R n ≫ (simplexSupportedChainIso R n).hom.f n ≫
      (SSet.chainComplexMap (smallAffineStraightening (convex_simplexRegion n)) R).f n ≫
        (simplexSupportedChainIso R n).inv.f n = _
  simpa only [Category.assoc, hid, Category.comp_id] using
    congrArg (fun q ↦ q ≫ (simplexSupportedChainIso R n).inv.f n) h


@[simp]
theorem barycentricSimplexChain_zero :
    barycentricSimplexChain R 0 = fundamentalSimplexChain R 0 := by
  have hid := HomologicalComplex.congr_hom (simplexSupportedChainIso R 0).hom_inv_id 0
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hid
  simp only [barycentricSimplexChain, simplexSubdivision, HomologicalComplex.comp_f,
    smallAffineSubdivision_f, smallAffineSubdivisionMap_zero, Category.id_comp,
    hid, Category.comp_id]


@[simp]
theorem barycentricSimplexHomotopyChain_zero : barycentricSimplexHomotopyChain R 0 = 0 := by
  simp only [barycentricSimplexHomotopyChain, simplexSubdivisionHomotopy,
    Homotopy.compRight_hom, Homotopy.compLeft_hom, smallAffineSubdivisionHomotopy_hom,
    smallAffineSubdivisionHomotopyMap_zero, comp_zero, zero_comp]


theorem barycentricSimplexHomotopyChain_boundary (n : ℕ) :
    barycentricSimplexChain R (n + 1) - fundamentalSimplexChain R (n + 1) =
      (∑ i : Fin (n + 2), (-1) ^ i.val •
        (barycentricSimplexHomotopyChain R n ≫
          (SSet.chainComplexMap (TopCat.toSSet.map
            (SimplexCategory.toTop.map (SimplexCategory.δ i))) R).f (n + 1))) +
      barycentricSimplexHomotopyChain R (n + 1) ≫
        ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n + 1⦌)).chainComplex R).d (n + 2) (n + 1) := by
  have h := (simplexSubdivisionHomotopy R (n + 1)).comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  have he := congrArg (fun q ↦ fundamentalSimplexChain R (n + 1) ≫ q) h
  simp only [Preadditive.comp_add] at he
  rw [fundamentalSimplexChain_straightening] at he
  apply (sub_eq_iff_eq_add).mpr
  change fundamentalSimplexChain R (n + 1) ≫ (simplexSubdivision R (n + 1)).f (n + 1) = _
  rw [he]
  congr 2
  rw [← Category.assoc, fundamentalSimplexChain_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro i _
  rw [← simplexSubdivisionHomotopy_naturality R (SimplexCategory.δ i) n]
  rfl

end DifferentialGeometry.Homology
