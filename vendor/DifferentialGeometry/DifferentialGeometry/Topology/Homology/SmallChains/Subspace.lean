module

public import DifferentialGeometry.Topology.Homology.SmallChains

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial AlgebraicTopology

universe u

namespace DifferentialGeometry.Homology

variable (X : TopCat.{u}) (s : Set X)

local notation "A" => smallSingularSimplices X (fun _ : Unit ↦ s)
local notation "j" => TopCat.toSSet.map (TopCat.ofHom
  (ContinuousMap.mk Subtype.val (continuous_subtype_val : Continuous (Subtype.val : s → X))))


def singularSubspaceEquiv (n : SimplexCategoryᵒᵖ) :
    (TopCat.toSSet.obj (TopCat.of s)).obj n ≃ (A : SSet).obj n where
  toFun σ := ⟨(j).app n σ, by
    refine ⟨(), ?_⟩
    rintro _ ⟨z, rfl⟩
    exact (((TopCat.of s).toSSetObjEquiv n) σ z).property⟩
  invFun σ := ((TopCat.of s).toSSetObjEquiv n).symm
    ⟨fun z ↦ ⟨X.toSSetObjEquiv n σ.val z, σ.property.choose_spec ⟨z, rfl⟩⟩,
      (X.toSSetObjEquiv n σ.val).continuous.subtype_mk _⟩
  left_inv σ := by
    apply ((TopCat.of s).toSSetObjEquiv n).injective
    ext z
    rfl
  right_inv σ := by
    apply Subtype.ext
    apply (X.toSSetObjEquiv n).injective
    ext z
    rfl


def singularSubspaceIso : TopCat.toSSet.obj (TopCat.of s) ≅ (A : SSet) :=
  NatIso.ofComponents (fun n ↦ (singularSubspaceEquiv X s n).toIso) (by
    intro n m f
    ext σ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((j).naturality f) σ)


@[reassoc (attr := simp)]
theorem singularSubspaceIso_hom_ι :
    (singularSubspaceIso X s).hom ≫ (A).ι = (j) := rfl


@[reassoc (attr := simp)]
theorem singularSubspaceIso_inv_inclusion :
    (singularSubspaceIso X s).inv ≫ (j) = (A).ι := by
  rw [← singularSubspaceIso_hom_ι X s, Iso.inv_hom_id_assoc]

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def singularSubspaceChainIso :
    (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj (TopCat.of s)) ≅
      (A : SSet).chainComplex R :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).mapIso (singularSubspaceIso X s)


@[reassoc]
theorem ι_singularSubspaceChainIso_hom_f {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of s) _⦋n⦌) :
    (TopCat.toSSet.obj (TopCat.of s)).ιChainComplex σ ≫
        (singularSubspaceChainIso X s R).hom.f n =
      (A : SSet).ιChainComplex (singularSubspaceEquiv X s (op ⦋n⦌) σ) :=
  SSet.ι_chainComplexMap_f _ _ _ R σ


@[reassoc]
theorem ι_singularSubspaceChainIso_inv_f {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    (A : SSet).ιChainComplex σ ≫ (singularSubspaceChainIso X s R).inv.f n =
      (TopCat.toSSet.obj (TopCat.of s)).ιChainComplex
        ((singularSubspaceEquiv X s (op ⦋n⦌)).symm σ) :=
  SSet.ι_chainComplexMap_f _ _ _ R σ

@[reassoc (attr := simp)]
theorem singularSubspaceChainIso_hom_inclusion :
    (singularSubspaceChainIso X s R).hom ≫ smallChainMap X (fun _ : Unit ↦ s) R =
      ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))) := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, singularSubspaceIso_hom_ι]


@[reassoc (attr := simp)]
theorem singularSubspaceChainIso_inv_inclusion :
    (singularSubspaceChainIso X s R).inv ≫
        ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
          (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))) =
      smallChainMap X (fun _ : Unit ↦ s) R := by
  rw [← singularSubspaceChainIso_hom_inclusion X s R, Iso.inv_hom_id_assoc]

end DifferentialGeometry.Homology
