module

public import DifferentialGeometry.Topology.Homology.Subdivision.Homotopy

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E E' : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : E →L[ℝ] E')

local notation "Φ" => TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f)))


theorem affineSimplex_map_linear {n : ℕ} (v : Fin (n + 1) → E) :
    (⟨f, f.continuous⟩ : C(E, E')).comp (affineSimplex v) = affineSimplex (f ∘ v) := by
  ext x
  change f (∑ i, x.weights i • v i) = ∑ i, x.weights i • f (v i)
  simp only [map_sum, map_smul]


theorem map_affineSingularSimplex_linear {n : ℕ} (v : Fin (n + 1) → E) :
    (Φ).app (op ⦋n⦌) (affineSingularSimplex v) = affineSingularSimplex (f ∘ v) := by
  apply ((TopCat.of E').toSSetObjEquiv (op ⦋n⦌)).injective
  exact affineSimplex_map_linear f v


theorem singularSimplexVertices_map_linear {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    singularSimplexVertices ((Φ).app (op ⦋n⦌) σ) = f ∘ singularSimplexVertices σ := rfl


theorem singularSimplexBarycenter_map_linear {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    singularSimplexBarycenter ((Φ).app (op ⦋n⦌) σ) = f (singularSimplexBarycenter σ) := by
  simp only [singularSimplexBarycenter, singularSimplexVertices_map_linear,
    Finset.centerMass, Function.comp_apply, map_smul, map_sum]


theorem affineStraightening_naturality_linear :
    (Φ) ≫ affineStraightening (E := E') = affineStraightening (E := E) ≫ (Φ) := by
  ext n σ
  exact (congrArg affineSingularSimplex (singularSimplexVertices_map_linear f σ)).trans
    (map_affineSingularSimplex_linear f (singularSimplexVertices σ)).symm

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

local notation "T" => _root_.SSet.chainComplexMap (Φ) R
local notation "K" => _root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R
local notation "L" => _root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E')) R
local notation "S" => _root_.SSet.chainComplexMap (affineStraightening (E := E)) R
local notation "S'" => _root_.SSet.chainComplexMap (affineStraightening (E := E')) R


theorem affineStraightening_chain_naturality_linear : (T) ≫ (S') = (S) ≫ (T) := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, affineStraightening_naturality_linear]


@[reassoc]
theorem affineCone_naturality_linear (p : E) (n : ℕ) :
    affineCone R p n ≫ (T).f (n + 1) = (T).f n ≫ affineCone R (f p) n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_affineCone, SSet.ι_chainComplexMap_f,
    map_affineSingularSimplex_linear]
  rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((T).f n),
    SSet.ι_chainComplexMap_f, ι_affineCone, singularSimplexVertices_map_linear, Fin.comp_cons]


theorem affineSubdivisionMap_naturality_linear (n : ℕ) :
    affineSubdivisionMap (E := E) R n ≫ (T).f n =
      (T).f n ≫ affineSubdivisionMap (E := E') R n := by
  induction n with
  | zero => rw [affineSubdivisionMap_zero, affineSubdivisionMap_zero,
      Category.id_comp, Category.comp_id]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionMap_succ]
    simp only [Category.assoc]
    rw [affineCone_naturality_linear]
    rw [← Category.assoc (affineSubdivisionMap (E := E) R n), hn]
    simp only [Category.assoc]
    rw [← Category.assoc ((K).d (n + 1) n), ← (T).comm]
    simp only [Category.assoc]
    rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((T).f (n + 1)),
      SSet.ι_chainComplexMap_f]
    rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((T).f (n + 1)),
      SSet.ι_chainComplexMap_f, ι_affineSubdivisionMap_succ, singularSimplexBarycenter_map_linear]


theorem affineSubdivision_naturality_linear :
    affineSubdivision (E := E) R ≫ (T) = (T) ≫ affineSubdivision (E := E') R := by
  apply HomologicalComplex.hom_f_injective
  funext n
  exact affineSubdivisionMap_naturality_linear f R n

private theorem difference_naturality_linear (n : ℕ) :
    (affineSubdivision (E := E) R - S).f n ≫ (T).f n =
      (T).f n ≫ (affineSubdivision (E := E') R - S').f n := by
  rw [HomologicalComplex.sub_f_apply, Preadditive.sub_comp, affineSubdivision_f,
    affineSubdivisionMap_naturality_linear]
  have h := HomologicalComplex.congr_hom (affineStraightening_chain_naturality_linear f R) n
  simp only [HomologicalComplex.comp_f] at h
  rw [← h, HomologicalComplex.sub_f_apply, Preadditive.comp_sub, affineSubdivision_f]


theorem affineSubdivisionHomotopyMap_naturality_linear (n : ℕ) :
    affineSubdivisionHomotopyMap (E := E) R n ≫ (T).f (n + 1) =
      (T).f n ≫ affineSubdivisionHomotopyMap (E := E') R n := by
  induction n with
  | zero => rw [affineSubdivisionHomotopyMap_zero, affineSubdivisionHomotopyMap_zero,
      zero_comp, comp_zero]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    have hz :
        ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫
            (affineSubdivision (E := E) R - S).f (n + 1) -
          (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (K).d (n + 1) n ≫
            affineSubdivisionHomotopyMap R n) ≫ (T).f (n + 1) =
        (TopCat.toSSet.obj (TopCat.of E')).ιChainComplex ((Φ).app (op ⦋n + 1⦌) σ) ≫
            (affineSubdivision (E := E') R - S').f (n + 1) -
          (TopCat.toSSet.obj (TopCat.of E')).ιChainComplex ((Φ).app (op ⦋n + 1⦌) σ) ≫
            (L).d (n + 1) n ≫ affineSubdivisionHomotopyMap R n := by
      rw [Preadditive.sub_comp]
      simp only [Category.assoc]
      rw [difference_naturality_linear, hn]
      rw [← Category.assoc ((K).d (n + 1) n), ← (T).comm]
      simp only [Category.assoc]
      rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((T).f (n + 1)),
        SSet.ι_chainComplexMap_f]
      rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((T).f (n + 1)),
        SSet.ι_chainComplexMap_f]
    rw [← Category.assoc, ι_affineSubdivisionHomotopyMap_succ, Category.assoc,
      affineCone_naturality_linear, ← Category.assoc, hz]
    rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((T).f (n + 1)),
      SSet.ι_chainComplexMap_f, ι_affineSubdivisionHomotopyMap_succ,
      singularSimplexBarycenter_map_linear]

end DifferentialGeometry.Homology
